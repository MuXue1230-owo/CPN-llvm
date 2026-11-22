"""Discriminated unions with scalar payloads (CPN26 chapters 10 and 12)."""

from dataclasses import dataclass

from numeric import Value, irtype, literal, record
from syntax import Error


@dataclass
class Variant:
    owner: str
    tag: int
    fields: list


def define_union(module, decl):
    name = decl.token.text
    if name in module.names:
        raise Error(decl.token, "name already declared")
    typ = "record.union." + (module.prefix + name).encode().hex()
    layout = {".tag": literal(0, "u32")}
    cases, default = {}, None
    for tag, (case, is_default, payload) in enumerate(decl.args):
        if case.text in cases or (is_default and default is not None):
            raise Error(case, "duplicate union case or default")
        fields, names = [], set()
        for spelling, field in payload:
            target = module.bind_type(spelling, module.types, field)
            if (
                field.text in names
                or record(target)
                or target.endswith(("&", "]"))
                or target in ("void", "const<void>")
                or target in module.signatures
                or target in module.incomplete
            ):
                raise Error(field, "invalid or unsupported union payload")
            names.add(field.text)
            fields.append((target, len(layout)))
            layout[f".{tag}.{field.text}"] = Value(target)
        variant = Variant(typ, tag, fields)
        cases[case.text] = variant
        module.names[name + "::" + case.text] = variant
        if is_default:
            default = variant
    module.types[name] = typ
    module.unions[typ] = (cases, default)
    module.records[typ] = layout
    module.ir.append(
        f"%{typ} = type {{ {', '.join(irtype(v.type) for v in layout.values())} }}"
    )


class UnionLowering:
    def variant(self, case, operands, tok, use_defaults=False):
        if not use_defaults and len(operands) != len(case.fields):
            raise Error(tok, "wrong union case payload arity")
        ir = "zeroinitializer"
        union = irtype(case.owner)
        for i, (typ, index) in enumerate(case.fields):
            v = (
                self.zero(typ)
                if use_defaults
                else self.convert(self.expr(operands[i], typ), typ, tok)
            )
            ir = self.temp(f"insertvalue {union} {ir}, {irtype(typ)} {v.ir}, {index}")
        return Value(
            case.owner, self.temp(f"insertvalue {union} {ir}, i32 {case.tag}, 0")
        )

    def match(self, node):
        expression, arms = node.args
        obj = self.expr(expression)
        if obj.type not in self.module.unions:
            raise Error(node.token, "match requires a tagged union")
        cases, _ = self.module.unions[obj.type]
        used, plan = {}, []
        wildcard = None
        for case, patterns, body in arms:
            label = self.ident()
            variant = None
            if wildcard is not None:
                raise Error(body.token, "wildcard must be the final match arm")
            if case is None:
                wildcard = label
            else:
                owner, name = case
                variant = cases.get(name.text)
                if self.resolve(owner.text) != obj.type or variant is None:
                    raise Error(name, "case does not belong to the subject type")
                if variant.tag in used or len(patterns) != len(variant.fields):
                    raise Error(name, "duplicate case or incomplete payload pattern")
                used[variant.tag] = label
            plan.append((label, variant, patterns, body))
        if wildcard is None and len(used) != len(cases):
            raise Error(node.token, "non-exhaustive match")
        addr = obj.address
        if not addr:
            addr = self.allocate(obj.type)
            self.store(obj, addr)
        tag = self.temp(f"extractvalue {irtype(obj.type)} {obj.ir}, 0")
        done, invalid = self.ident(), self.ident()
        table = " ".join(f"i32 {n}, label %{label}" for n, label in used.items())
        self.emit(f"switch i32 {tag}, label %{wildcard or invalid} [ {table} ]")
        if wildcard is None:
            self.label(invalid)
            self.emit("unreachable")
        live, continuing = self.reachable, False
        for label, variant, patterns, body in plan:
            self.label(label)
            self.forget_lifetimes()
            self.reachable = live
            scope = {}
            self.scopes.append(scope)
            for (kind, name), (typ, index) in zip(
                patterns, variant.fields if variant else ()
            ):
                if kind == "_":
                    continue
                if kind == "move" and not obj.expiring:
                    raise Error(name, "move binding requires an expiring subject")
                self.reserve(name, scope)
                ptr = self.temp(
                    f"getelementptr {irtype(obj.type)}, ptr {addr}, i32 0, i32 {index}"
                )
                v = Value(typ, address=ptr, readonly=obj.readonly)
                if kind != "ref":
                    copy = self.allocate(typ)
                    self.store(self.load(v), copy)
                    self.register(typ, copy, scope)
                    v = Value(typ, address=copy)
                scope[name.text] = v
            self.statement(body)
            self.cleanup(len(self.scopes) - 1, leaving=True)
            self.scopes.pop()
            continuing |= self.reachable
            self.jump(done)
        self.label(done)
        self.forget_lifetimes()
        self.reachable = continuing
