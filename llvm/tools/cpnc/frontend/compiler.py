"""Bind a single CPN26 root unit and generate LLVM IR for the supported target."""

from dataclasses import dataclass, replace
from copy import copy
from itertools import count
import re

from numeric import (
    IntegerLowering,
    Value,
    bounds,
    common,
    irtype,
    literal,
    record,
    width,
    resolve_type,
    handle,
    enum_type,
)
from memory import MemoryLowering, uses_storage
from control import bind_names, label_edges
from lifecycle import MemberLifetime, emit_destruction, register_array_destruction
from inheritance import BaseSubobjects, base_paths, member_paths
from statics import define_static, emit_domain
from dispatch import VirtualCalls, build_tables
from construction import bind_constructors
from packs import Expansion, pack_arity
from tagged import Variant, UnionLowering, define_union
from syntax import (
    ASSIGN,
    CallableType,
    Error,
    NoOperation,
    Function,
    Node,
    Parser,
    TYPES,
    integer_value,
    quoted_text,
)


@dataclass
class Definition:
    syntax: Function
    result: str
    params: tuple
    symbol: str
    types: dict
    names: dict
    policy: str
    default_int: str
    receiver: str = ""
    producers: dict | None = None
    accessible: bool = True
    readonly: bool = False
    phase: str = ""
    default_owner: object = None
    slot: int | None = None

    def accepts_arity(self, count):
        formals = (self.default_owner or self).syntax.params
        if any(p.expansion for p in formals):
            return count >= sum(not p.expansion and p.default is None for p in formals)
        return count == len(formals) or (
            count < len(formals) and formals[count].default is not None
        )


def ir_name(name):
    if re.fullmatch(r"[a-zA-Z_.$][a-zA-Z_0-9.$]*", name):
        return name
    return '"' + "".join(f"\\{byte:02X}" for byte in name.encode()) + '"'


def abi_type(typ, foreign, result=False):
    ir = irtype(typ)
    if not foreign or typ not in ("bool", "i8", "u8", "i16", "u16"):
        return ir
    extension = "signext" if typ.startswith("i") else "zeroext"
    return f"{extension} {ir}" if result else f"{ir} {extension}"


def referent(typ):
    base = typ.rstrip("&")
    readonly = base.startswith("const<") and base.endswith(">")
    return (base[6:-1] if readonly else base), readonly


def deduced_types(name, formal, actual, default_int):
    results = set()
    for pattern, value in zip(formal, actual):
        pattern, _ = referent(pattern)
        typ = default_int if value.type == "integer" else value.type
        while pattern.endswith("*") and typ.endswith("*"):
            pattern, typ = pattern[:-1], typ[:-1]
            if pattern.startswith("const<") and pattern.endswith(">"):
                pattern = pattern[6:-1]
                if typ.startswith("const<") and typ.endswith(">"):
                    typ = typ[6:-1]
        if pattern == name:
            results.add(typ)
    return results


DIAGNOSTIC_CODES = {
    "ERROR": {
        "CFG001",
        "CFG002",
        "ABI001",
        "LIFE001",
        "LIFE002",
        "LIFE005",
        "NUM001",
        "STAT001",
        "EXC002",
    }
    | {f"META{i:03}" for i in range(1, 11)},
    "WARNING": {"NUM002"},
    "ANOMALY": {"GEN001", "LIFE003", "LIFE004", "NUM003", "STAT002", "EXC001"},
    "INFO": set(),
}


class Module:
    def __init__(
        self,
        preset,
        profile="unicode",
        warn=lambda token, message, category="WARNING": None,
    ):
        self.profile = profile
        self.report = warn
        self.minimum = "WARNING"
        self.promote = ()
        self.suppress = ()
        self.preset = preset
        self.overflow = None
        self.default_int = "i32"
        self.types = {t: t for t in TYPES}
        self.types["byte"] = "u8"
        self.prefix = ""
        self.namespaces = {}
        self.widths = (8, 16, 32, 64)
        self.names = {}
        self.ir = []
        self.records = {}
        self.virtual_methods = {}
        self.virtual_destructors = {}
        self.vtables = {}
        self.bases = {}
        self.final_records = set()
        self.incomplete = set()
        self.enum_cases = {}
        self.unions = {}
        self.destructors = {}
        self.specials = {}
        self.constructors = {}
        self.plans = {}
        self.methods = {}
        self.families = {}
        self.constraints = {}
        self.record_instances = {}
        self.type_expressions = {}
        self.callable_types = {}
        self.callable_ids = {}
        self.signatures = {}
        self.private = set()
        self.instances = {}
        self.pending = {}
        self.definitions = {}
        self.default_entries = {}
        self.foreign_objects = {}
        self.statics = []
        self.static_flags = {}
        self.static_attributes = {}
        self.used = set()
        self.ids = count()

    @property
    def policy(self):
        return self.overflow or (
            "checked" if self.preset.endswith("Debug") else "native"
        )

    def weakens_noexcept(self, source, target):
        if not source.endswith("*") or not target.endswith("*"):
            return False
        before = self.signatures.get(source[:-1])
        after = self.signatures.get(target[:-1])
        return bool(
            before and before.noexcept and after == replace(before, noexcept=False)
        )

    def warn(self, token, message, category="WARNING", code=""):
        levels = ("INFO", "WARNING", "ANOMALY", "ERROR", "none")
        if code:
            message = f"{code}: {message}"
        if category in self.promote or code in self.promote:
            raise Error(token, message)
        if code not in self.suppress and levels.index(category) >= levels.index(
            self.minimum
        ):
            self.report(token, message, category)

    def project_config(self, source):
        for item in Parser(source, self.profile, self.warn).unit():
            if not isinstance(item, Node) or item.kind != "config":
                t = item.name if isinstance(item, Function) else item.token
                raise Error(t, "cpn.config admits configuration declarations only")
            self.config(item, project=True)

    def config(self, node, project=False):
        for key, value in node.args[0].items():
            if key == "preset" and value in (
                "Release",
                "Debug",
                "MinimalRelease",
                "MinimalDebug",
            ):
                self.preset = value
            elif key == "numeric.integer.overflow" and value in (
                "checked",
                "native",
                "wrapping",
                "saturating",
            ):
                self.overflow = value
            elif key == "numeric.literal.integer_default" and value in (
                "i8",
                "i16",
                "i32",
                "i64",
            ):
                self.default_int = value
            elif key == "numeric.integer.widths" and isinstance(value, list):
                if (
                    not all(n in ("8", "16", "32", "64") for n in value)
                    or "32" not in value
                    or len(set(value)) != len(value)
                ):
                    raise Error(node.token, "invalid enabled integer widths")
                self.widths = tuple(map(int, value))
            elif key == "diagnostics.minimum" and value in (
                "INFO",
                "WARNING",
                "ANOMALY",
                "ERROR",
                "none",
            ):
                self.minimum = value
            elif key in ("diagnostics.promote", "diagnostics.suppress") and isinstance(
                value, list
            ):
                allowed = set().union(*DIAGNOSTIC_CODES.values())
                if key == "diagnostics.promote":
                    allowed.update(DIAGNOSTIC_CODES)
                else:
                    allowed.difference_update(DIAGNOSTIC_CODES["ERROR"])
                if not all(
                    isinstance(v, str) and v.strip('"') in allowed for v in value
                ):
                    raise Error(
                        node.token, f"CFG001: invalid diagnostic selection for {key}"
                    )
                codes = tuple(v.strip('"') for v in value)
                if key == "diagnostics.promote":
                    self.promote = codes
                else:
                    self.suppress = codes
            elif key in (
                "compilation.modules",
                "compilation.separate",
                "tooling.contract_export",
                "generic.higher_kinds",
                "generic.associated_entities",
            ) and value in ("true", "false"):
                if value == "true":
                    raise Error(node.token, f"CFG002: capability {key} unavailable")
            elif (
                key == "source.identifiers"
                and project
                and value in ("ascii", "unicode")
            ):
                self.profile = value
            elif key == "source.unicode_version" and project and value == '"17.0.0"':
                pass
            elif key == "target" and project and value == '"x86_64-linux-gnu"':
                pass
            else:
                raise Error(
                    node.token,
                    f"CFG001: unsupported configuration binding {key} = {value}",
                )

    def type_constant(self, spelling, target, tok, evaluator=None):
        expr = self.type_expressions.get(spelling)
        evaluator = evaluator or Emitter(self)
        if expr is not None:
            return evaluator.constant_expr(expr, target)
        if not spelling.isdecimal():
            raise Error(tok, "constant expression required")
        return evaluator.convert(literal(int(spelling)), target, tok)

    def bind_type(self, typ, bindings, tok, evaluator=None):
        if typ.endswith(("*", "&")):
            suffix = "&&" if typ.endswith("&&") else typ[-1]
            base = self.bind_type(typ[: -len(suffix)], bindings, tok, evaluator)
            if base.endswith("&") or (
                suffix.endswith("&") and base in ("void", "const<void>")
            ):
                raise Error(tok, "invalid pointer or reference target")
            return base + suffix
        if typ.endswith("]"):
            element, n = typ[:-1].rsplit("[", 1)
            count = self.type_constant(n, "usize", tok, evaluator).constant
            if count >= 1 << 63:
                raise Error(tok, "array extent exceeds core target limit")
            base = self.bind_type(element, bindings, tok, evaluator)
            if (
                base in ("void", "const<void>")
                or base in self.signatures
                or base.endswith("&")
            ):
                raise Error(tok, "array requires a complete object element type")
            element_type = (
                base[6:-1] if base.startswith("const<") and base.endswith(">") else base
            )
            if (
                element_type in self.incomplete
                or record(element_type)
                and element_type not in self.records
            ):
                raise Error(tok, "array has incomplete record element type")
            array = f"{base}[{count}]"
            element = (
                base[6:-1] if base.startswith("const<") and base.endswith(">") else base
            )
            register_array_destruction(self, array, element, count)
            return array
        if typ.startswith("const<") and typ.endswith(">"):
            base = self.bind_type(typ[6:-1], bindings, tok, evaluator)
            if base in self.signatures:
                raise Error(tok, "function type cannot have object qualification")
            if base.startswith("const<") and base.endswith(">"):
                return base
            if base.endswith("&"):
                plain = base.rstrip("&")
                return self.bind_type(
                    f"const<{plain}>" + base[len(plain) :], bindings, tok, evaluator
                )
            if base.endswith("]"):
                plain, extent = base[:-1].rsplit("[", 1)
                return self.bind_type(
                    f"const<{plain}>[{extent}]", bindings, tok, evaluator
                )
            return f"const<{base}>"
        if typ in self.callable_types:
            spec = self.callable_types[typ]
            result = self.bind_type(spec.result, bindings, tok, evaluator)
            params = tuple(
                self.bind_type(p, bindings, tok, evaluator) for p in spec.params
            )
            if (
                any(p == "void" or p in self.signatures for p in params)
                or result in self.signatures
            ):
                raise Error(tok, "invalid function type result or parameter")
            contract = CallableType(result, params, spec.noexcept)
            if contract not in self.callable_ids:
                name = f"function.{next(self.ids)}"
                self.callable_ids[contract] = name
                self.signatures[name] = contract
            return self.callable_ids[contract]
        if "<" not in typ:
            if "::" in typ and typ not in bindings:
                raise Error(tok, f"unknown qualified type '{typ}'")
            resolved = bindings.get(typ, typ)
            if (
                re.fullmatch(r"[iu]\d+", resolved)
                and width(resolved) not in self.widths
            ):
                raise Error(tok, f"type {resolved} is unavailable")
            return resolved
        family, rest = typ[:-1].split("<", 1)
        if family not in self.families:
            raise Error(tok, "unknown record family")
        params, shell, context, requirement = self.families[family]
        raw, start, depth = [], 0, 0
        for i, ch in enumerate(rest):
            if ch == "," and depth == 0:
                raw.append(rest[start:i])
                start = i + 1
            depth += (ch == "<") - (ch == ">")
        if rest:
            raw.append(rest[start:])
        if params and params[-1].pack:
            expansion = Expansion(
                self, params[-1], max(0, len(raw) - len(params) + 1), tok
            )
            params = expansion.parameters(params)
            shell = expansion.visit(shell)
            requirement = expansion.visit(requirement)
        explicit = []
        for word, param in zip(raw, params):
            if param.kind == "type":
                explicit.append(word)
            elif word in self.type_expressions:
                explicit.append(self.type_expressions[word])
            else:
                explicit.append(Node(replace(tok, text=word), "integer"))
        site = Emitter(context)
        caller = evaluator or Emitter(self)
        subs, values = self.generic_arguments(params, explicit, site, caller, tok)
        site.require_constraint(requirement, tok)
        identity = (family, tuple(subs.values()))
        if identity not in self.record_instances:
            instance_name = f"{family}.{next(self.ids)}"
            instance_token = replace(shell.token, text=instance_name)
            captured = copy(context)
            captured.types = context.types | subs
            captured.names = context.names | values
            self.record_instances[identity] = "record." + instance_name.encode().hex()
            captured.record(replace(shell, token=instance_token))
        return self.record_instances[identity]

    def function(self, f):
        name = f.name.text
        type_parameters = {g.name for g in f.generics if g.kind == "type"}
        for p in f.params:
            if p.forwarding and (p.type not in type_parameters or p.readonly):
                raise Error(
                    p.name or f.name,
                    "forward requires an unqualified generic type parameter",
                )
            if p.expansion and not any(g.pack for g in f.generics):
                raise Error(
                    p.name or f.name, "parameter expansion requires a generic pack"
                )
        if f.generics and f.generics[-1].pack:
            Expansion(self, f.generics[-1], 1, f.name).visit(f)
        self.check_generic_parameters(f.generics, f.name)
        bindings = self.types.copy()
        for param in f.generics:
            if param.kind == "type":
                bindings[param.name] = param.name
        # Dependent signatures are finalized when a concrete application is selected.
        bind = (
            resolve_type
            if f.generics
            else lambda typ, table: self.bind_type(typ, table, f.name)
        )
        params = tuple(bind(p.type, bindings) for p in f.params)
        result = bind(f.result, bindings)
        if any(t in self.signatures for t in (*params, result)):
            raise Error(f.name, "function type requires a pointer")
        if result.endswith("&") or result.startswith("const<") and result.endswith(">"):
            raise Error(f.name, "unsupported qualified result type")
        if any(
            p in ("void", "void&") or (p.startswith("const<") and p.endswith(">"))
            for p in params
        ):
            raise Error(f.name, "void parameter is invalid; use ()")
        if (
            not self.prefix
            and name == "main"
            and (params or result != "i32" or f.generics)
        ):
            raise Error(f.name, "the hosted entry point must be i32 main()")
        if f.foreign and any(record(t) for t in (*params, result)):
            raise Error(f.name, "foreign aggregate ABI is unsupported")
        previous = self.names.get(name, ())
        if not isinstance(previous, tuple):
            raise Error(f.name, "name already declared")
        symbol = (
            name
            if (not self.prefix and name == "main") or f.foreign
            else f"cpn.{next(self.ids)}.{name}"
        )
        matching = None
        for old in previous:
            if old.params == params and old.syntax.generics == f.generics:
                matching = old
                if (
                    old.result != result
                    or old.syntax.foreign != f.foreign
                    or old.syntax.noexcept != f.noexcept
                    or old.syntax.mode != f.mode
                ):
                    raise Error(f.name, "incompatible redeclaration")
                if old.syntax.body and f.body:
                    raise Error(f.name, "function already defined")
                if any(p.default is not None for p in f.params):
                    raise Error(
                        f.name, "defaults must belong to one canonical declaration"
                    )
                if not f.body:
                    return
                symbol = old.symbol
            elif f.foreign or old.syntax.foreign or f.generics or old.syntax.generics:
                raise Error(
                    f.name, "unsupported overload of generic or foreign function"
                )
        definition = Definition(
            f, result, params, symbol, bindings, {}, self.policy, self.default_int
        )
        self.names[name] = tuple(x for x in previous if x is not matching) + (
            definition,
        )
        definition.names = self.names.copy()
        if (
            matching
            and matching.params
            and matching.accepts_arity(len(matching.params) - 1)
        ):
            definition.default_owner = matching.default_owner or matching
        self.check_defaults(definition)
        if f.body:
            self.definitions[symbol] = definition
        if f.generics:
            visible = set(definition.names) | {p.name for p in f.generics}
            bind_names(f.requirement, visible, bindings, self.families)
            visible.update(p.name.text for p in f.params if p.name)
            bind_names(f.body, visible, bindings, self.families)
            if f.body:
                label_edges(f.body)
        if f.body is None:
            self.pending[symbol] = definition
        elif not f.generics:
            self.pending.pop(symbol, None)
            body_ir = Emitter(self, definition).function_ir()
            if f.mode != "consteval":
                self.ir.append(body_ir)

    def check_defaults(self, d):
        owner = d.default_owner or d
        visible = set(owner.names) | {p.name for p in owner.syntax.generics}
        if d.receiver:
            visible.update(self.records[d.receiver])
            visible.add("this")
        for i, p in enumerate(owner.syntax.params):
            if p.default is not None:
                bind_names(p.default, visible, d.types, self.families)
                if not d.syntax.generics and (
                    i == 0 or owner.syntax.params[i - 1].default is None
                ):
                    if d.syntax.body or d.syntax.foreign:
                        self.default_entry(d, i)
                    else:
                        # Check a prototype's defaults even if no call or definition follows.
                        context = copy(self)
                        context.used, context.default_entries = set(), {}
                        syntax = replace(
                            d.syntax, result="void", body=Node(d.syntax.name, "block")
                        )
                        probe = replace(d, result="void", syntax=syntax)
                        Emitter(context, probe).function_ir(arity=i)
            if p.name:
                visible.add(p.name.text)

    def default_entry(self, d, count):
        if count == len(d.params):
            return d.symbol
        key = (d.symbol, count)
        if key not in self.default_entries:
            self.default_entries[key] = (d, f"cpn.default.{next(self.ids)}")
        return self.default_entries[key][1]

    def generic_arguments(
        self,
        params,
        explicit,
        site,
        caller,
        tok,
        formal=(),
        actual=(),
        runtime_params=(),
    ):
        if len(explicit) > len(params):
            raise Error(tok, "too many generic arguments")
        substitutions, values = {}, {}
        site.site = tok
        site.types = site.types.copy()
        site.scopes.append(values)
        for i, param in enumerate(params):
            kind, name = param.kind, param.name
            arg = explicit[i] if i < len(explicit) else None
            if isinstance(arg, Node) and arg.kind == "expand":
                raise Error(tok, "unexpanded generic argument pack")
            if kind == "type":
                if arg is not None:
                    typ = caller.resolve(arg)
                else:
                    inferred = deduced_types(name, formal, actual, caller.default_int)
                    if any(p.forwarding and p.type == name for p in runtime_params):
                        inferred = set()
                        for p, v in zip(runtime_params, actual):
                            if p.type != name:
                                continue
                            target = (
                                caller.default_int if v.type == "integer" else v.type
                            )
                            if p.forwarding:
                                if v.readonly:
                                    target = f"const<{target}>"
                                if v.address and not v.expiring:
                                    target += "&"
                            inferred.add(target)
                    if len(inferred) == 1:
                        typ = inferred.pop()
                    elif not inferred and param.default is not None:
                        typ = site.resolve(param.default)
                    else:
                        raise Error(tok, f"cannot deduce type parameter {name}")
                substitutions[name] = typ
            else:
                target = site.resolve(kind)
                if not self.constant_parameter_type(target):
                    raise Error(
                        tok, f"invalid generic constant parameter type {target}"
                    )
                if arg is not None:
                    value = caller.constant_expr(arg, target)
                elif param.default is not None:
                    value = site.constant_expr(param.default, target)
                else:
                    raise Error(tok, f"{name} needs a constant argument")
                values[name] = value
                substitutions[name] = str(value.constant)
            site.types[name] = substitutions[name]
        return substitutions, values

    def check_generic_parameters(self, params, tok):
        visible = set(self.names)
        type_parameters = set()
        for param in params:
            if param.kind == "type":
                type_parameters.add(param.name)
                continue
            if param.kind not in type_parameters:
                target = self.bind_type(param.kind, self.types, tok)
                if not self.constant_parameter_type(target):
                    raise Error(
                        tok, f"invalid generic constant parameter type {target}"
                    )
            if param.default is not None:
                bind_names(
                    param.default,
                    visible,
                    self.types.keys() | type_parameters,
                    self.families,
                )
            visible.add(param.name)

    @staticmethod
    def constant_parameter_type(typ):
        return (
            typ in ("bool", "char", "usize", "isize")
            or enum_type(typ)
            or bool(re.fullmatch(r"[iu](8|16|32|64)", typ))
        )

    def instantiate(self, definition, arguments, explicit, caller, tok):
        f = definition.syntax
        formal = definition.params
        if f.generics[-1].pack:
            n = pack_arity(f, explicit, arguments, tok)
            expansion = Expansion(self, f.generics[-1], n, tok)
            f = replace(expansion.visit(f), generics=expansion.parameters(f.generics))
            formal = tuple(resolve_type(p.type, definition.types) for p in f.params)
        site = Emitter(self, definition)
        bound, values = self.generic_arguments(
            f.generics, explicit, site, caller, tok, formal, arguments, f.params
        )
        site.require_constraint(f.requirement, tok)
        types = definition.types | bound
        identity = (definition.symbol, tuple(bound.values()))
        if identity not in self.instances:
            evaluator = Emitter(self, definition, values)
            evaluator.types = types
            params = []
            for p, pattern in zip(f.params, formal):
                target = self.bind_type(pattern, types, tok, evaluator)
                if p.forwarding and not target.endswith("&"):
                    target += "&&"
                params.append(target)
            instance = replace(
                definition,
                syntax=f,
                types=types,
                names=definition.names | values,
                params=tuple(params),
                result=self.bind_type(f.result, types, tok, evaluator),
                symbol=f"{definition.symbol}.{next(self.ids)}",
            )
            self.instances[identity] = instance
            self.definitions[instance.symbol] = instance
            self.ir.append(Emitter(self, instance, values).function_ir())
        return self.instances[identity]

    def record(self, item):
        name = item.token.text
        if name in self.names:
            raise Error(item.token, "name already declared")
        fields = {}
        emitter = Emitter(self)
        (
            declarations,
            ctors,
            dtor,
            cleanup,
            methods,
            specials,
            manual,
            base_types,
            final,
            destructor_spec,
        ) = item.args
        typ_id = "record." + (self.prefix + name).encode().hex()
        self.incomplete.add(typ_id)
        self.types[name] = typ_id
        bases = tuple(
            self.bind_type(base, self.types, item.token) for base in base_types
        )
        if len(bases) != len(set(bases)):
            raise Error(item.token, "duplicate direct base")
        for base in bases:
            if (
                base not in self.records
                or base in self.unions
                or base in self.final_records
                or base == typ_id
            ):
                raise Error(item.token, "base must be a complete non-final record")
            fields["$base:" + base] = Value(base, "zeroinitializer")
        self.bases[typ_id] = bases
        if final:
            self.final_records.add(typ_id)

        def slot_name(spelling):
            if spelling.startswith("$base:"):
                return "$base:" + self.bind_type(spelling[6:], self.types, item.token)
            return spelling

        manual = {slot_name(slot) for slot in manual}
        for field, public in declarations:
            _, typ, member, init = field.args
            typ = self.bind_type(typ, self.types, member)
            if typ in self.incomplete:
                raise Error(member, "field requires a complete object type")
            if typ in self.signatures:
                raise Error(member, "function type requires a pointer")
            if not public:
                self.private.add((typ_id, member.text))
            if (
                typ.split("[")[0] == typ_id
                or typ.endswith("&")
                or (typ.startswith("const<") and typ.endswith(">"))
            ):
                raise Error(member, "unsupported or incomplete member type")
            if member.text in fields or typ == "void":
                raise Error(member, "invalid or duplicate member")
            if len(init) > 1 or (record(typ) and init):
                raise Error(member, "unsupported in-class member initializer")
            emitter.site = member
            default = emitter.constant_expr(init[0], typ) if init else emitter.zero(typ)
            fields[member.text] = default
        if any(f.virtual or f.override for f, _, _ in methods) or destructor_spec[0]:
            fields["$vtable"] = Value("void*", "null")
        typ = typ_id
        self.records[typ] = fields
        self.incomplete.discard(typ)
        self.specials[typ] = specials
        layout = ", ".join(irtype(v.type) for v in fields.values()) or "i8"
        self.ir.append(f"{irtype(typ)} = type {{ {layout} }}")

        # Index the complete member set before binding any member body.
        members = []
        for f, readonly, public in methods:
            params = tuple(self.bind_type(p.type, self.types, f.name) for p in f.params)
            result = self.bind_type(f.result, self.types, f.name)
            existing = self.methods.setdefault((typ, f.name.text), [])
            if f.name.text in fields or any(
                m.params == params
                and m.readonly == readonly
                and (
                    not m.syntax.receiver_category
                    or not f.receiver_category
                    or m.syntax.receiver_category == f.receiver_category
                )
                for m in existing
            ):
                raise Error(f.name, "duplicate class member")
            m = Definition(
                f,
                result,
                params,
                f"method.{typ}.{next(self.ids)}",
                self.types.copy(),
                self.names.copy(),
                self.policy,
                self.default_int,
                receiver=typ,
                accessible=public,
                readonly=readonly,
            )
            existing.append(m)
            members.append(m)
            self.check_defaults(m)
        build_tables(self, typ, members, destructor_spec, item.token)
        for params, producers, body, public in ctors:
            normalized = {slot_name(slot): args for slot, args in producers.items()}
            if len(normalized) != len(producers):
                raise Error(item.token, "duplicate base initialization producer")
            producers = normalized
            unknown = set(producers) - set(fields)
            if unknown:
                raise Error(
                    item.token, f"unknown initialization target '{sorted(unknown)[0]}'"
                )
            f = Function(item.token, "void", params, body, False, [])
            signature = tuple(
                self.bind_type(p.type, self.types, f.name) for p in params
            )
            ctor = Definition(
                f,
                "void",
                signature,
                f"ctor.{typ}.{next(self.ids)}",
                self.types.copy(),
                self.names.copy(),
                self.policy,
                self.default_int,
                typ,
                producers,
                public,
            )
            existing = self.constructors.setdefault(typ, [])
            if any(c.params == signature for c in existing):
                raise Error(item.token, "duplicate constructor")
            existing.append(ctor)
            self.check_defaults(ctor)
        bind_constructors(self, self.constructors.get(typ, ()))
        for method in members:
            self.ir.append(Emitter(self, method).function_ir())
        if "$members" in manual:
            manual = (manual - {"$members"}) | {
                slot for slot in fields if not slot.startswith("$base:")
            }
        if manual - {"*"} - fields.keys():
            raise Error(item.token, "Complete selector is not a direct member")
        if "*" in manual:
            manual = set(fields)
        if (
            dtor
            or typ in self.virtual_destructors
            or any(v.type in self.destructors for v in fields.values())
        ):
            emit_destruction(self, item, typ, fields, manual, dtor, cleanup)

    def bind_items(self, items):
        for item in items:
            if isinstance(item, Function):
                self.function(item)
            elif item.kind == "static_attributes":
                context = copy(self)
                context.static_attributes, obj = item.args
                Emitter(context).object(obj, global_object=True)
            elif item.kind == "config":
                self.config(item)
            elif item.kind == "configured_decl":
                context = copy(self)
                context.config(Node(item.token, "config", (item.args[0],)))
                context.bind_items(item.args[1])
            elif item.kind == "foreign_object":
                defining, obj = item.args
                q, spelling, name, args = obj.args
                typ = self.bind_type(spelling, self.types, name)
                if (
                    typ in ("void", "const<void>")
                    or typ in self.signatures
                    or record(typ)
                    or typ.endswith(("&", "]"))
                ):
                    raise Error(name, "unsupported external object type")
                old = self.foreign_objects.get(name.text)
                if (old is None and name.text in self.names) or (
                    old and (old[:2] != (typ, q) or (defining and old[2] is not None))
                ):
                    raise Error(name, "conflicting external object declaration")
                initializer = old[2] if old else None
                if defining:
                    em = Emitter(self)
                    em.site = name
                    value = em.construct(typ, args, name)
                    if em.lines:
                        raise Error(
                            name, "dynamic external initialization is unsupported"
                        )
                    initializer = value.ir
                self.foreign_objects[name.text] = (typ, q, initializer)
                self.names[name.text] = Value(
                    typ, address="@" + ir_name(name.text), readonly=bool(q)
                )
            elif item.kind == "namespace":
                if item.token.text in self.names or item.token.text in self.types:
                    raise Error(item.token, "namespace name already declared")
                prefix = self.prefix + item.token.text + "::"
                names, types = self.namespaces.setdefault(prefix, ({}, {}))
                context = copy(self)
                context.prefix = prefix
                context.names, context.types = self.names | names, self.types | types
                previous_names, previous_types = (
                    context.names.copy(),
                    context.types.copy(),
                )
                context.bind_items(item.args)
                for name, v in context.names.items():
                    if previous_names.get(name) is not v:
                        names[name] = v
                        self.names[item.token.text + "::" + name] = v
                for name, v in context.types.items():
                    if previous_types.get(name) != v:
                        types[name] = v
                        self.types[item.token.text + "::" + name] = v
            elif item.kind == "incomplete":
                kind, spelling = item.args
                name = item.token.text
                if name in self.names:
                    raise Error(item.token, "name already declared")
                identity = (self.prefix + name).encode().hex()
                if kind == "enum":
                    base = self.bind_type(spelling, self.types, item.token)
                    if not re.fullmatch(r"[iu](?:8|16|32|64|size)", base):
                        raise Error(
                            item.token, "enum requires an integer underlying type"
                        )
                    typ = f"enum.{identity}.{base}"
                else:
                    typ = ("record.union." if kind == "union" else "record.") + identity
                if name in self.types and self.types[name] != typ:
                    raise Error(item.token, "incompatible incomplete declaration")
                self.types[name] = typ
                if typ not in self.records and typ not in self.enum_cases:
                    self.incomplete.add(typ)
            elif item.kind == "union":
                define_union(self, item)
                self.incomplete.discard(self.types[item.token.text])
            elif item.kind == "enum":
                name = item.token.text
                base, cases = item.args
                underlying = self.bind_type(base, self.types, item.token)
                if not re.fullmatch(r"[iu](?:8|16|32|64|size)", underlying):
                    raise Error(item.token, "enum requires an integer underlying type")
                if name in self.names:
                    raise Error(item.token, "name already declared")
                typ = f"enum.{(self.prefix + name).encode().hex()}.{underlying}"
                if name in self.types and self.types[name] != typ:
                    raise Error(item.token, "incompatible enum underlying type")
                self.incomplete.discard(typ)
                self.types[name] = typ
                values = set()
                emitter = Emitter(self)
                for case, expr in cases:
                    value = emitter.constant_expr(expr, underlying).constant
                    key = name + "::" + case.text
                    if key in self.names or value in values:
                        raise Error(case, "duplicate enum case name or value")
                    self.names[key] = literal(value, typ)
                    values.add(value)
                self.enum_cases[typ] = values
            elif item.kind == "constraint":
                params, requirements = item.args
                self.check_generic_parameters(params, item.token)
                visible = set(self.names) | {p.name for p in params}
                types = self.types.keys() | {p.name for p in params if p.kind == "type"}
                for rule in requirements:
                    if rule[0] == "predicate":
                        bind_names(rule[1], visible, types, self.families)
                    elif rule[0] == "expression":
                        names = visible | {p.name.text for p in rule[1] if p.name}
                        for expr, _, _ in rule[2]:
                            bind_names(expr, names, types, self.families)
                context = copy(self)
                context.types, context.names = self.types.copy(), self.names.copy()
                self.constraints[item.token.text] = (params, requirements, context)
            elif item.kind == "record_family":
                params, record_decl, requirement = item.args
                self.check_generic_parameters(params, item.token)
                context = copy(self)
                context.types, context.names = self.types.copy(), self.names.copy()
                bind_names(
                    requirement,
                    self.names.keys() | {p.name for p in params},
                    self.types.keys() | {p.name for p in params if p.kind == "type"},
                    self.families,
                )
                self.families[item.token.text] = (
                    params,
                    record_decl,
                    context,
                    requirement,
                )
            elif item.kind == "record":
                self.record(item)
            elif item.kind == "alias":
                if item.token.text in self.names:
                    raise Error(item.token, "name already declared")
                self.types[item.token.text] = self.bind_type(
                    item.args[0], self.types, item.token
                )
            else:
                emitter = Emitter(self)
                emitter.object(item, global_object=True)

    def compile(self, source, logical_path="root.cpn", root_id=None):
        self.logical_path = logical_path
        self.root_id = root_id or logical_path
        parser = Parser(source, self.profile, self.warn)
        self.type_expressions = parser.type_expressions
        self.callable_types = parser.callable_types
        self.bind_items(parser.unit())
        generated = set()
        while pending := self.default_entries.keys() - generated:
            for key in sorted(pending):
                source, symbol = self.default_entries[key]
                definition = self.definitions.get(source.symbol, source)
                if not definition.syntax.body and not definition.syntax.foreign:
                    raise Error(
                        source.syntax.name,
                        "called native function needs a definition in this root",
                    )
                emitter = Emitter(self, definition)
                body_ir = emitter.function_ir(arity=key[1], symbol=symbol)
                if definition.syntax.mode != "consteval":
                    self.ir.append(body_ir)
                generated.add(key)
        for name, (typ, q, initializer) in self.foreign_objects.items():
            storage = "constant" if q else "global"
            linkage = "external " if initializer is None else ""
            value = " " + initializer if initializer is not None else ""
            self.ir.append(
                f"@{ir_name(name)} = {linkage}{storage} {irtype(typ)}{value}"
            )
        for symbol, d in self.pending.items():
            if d.syntax.foreign:
                self.ir.append(
                    f"declare {abi_type(d.result, True, True)} @{ir_name(symbol)}({', '.join(abi_type(p, True) for p in d.params)})"
                )
            elif symbol in self.used:
                raise Error(
                    d.syntax.name,
                    "called native function needs a definition in this root",
                )
        emit_domain(self)
        return (
            'target triple = "x86_64-unknown-linux-gnu"\n'
            "declare void @llvm.trap()\n" + "\n".join(self.ir) + "\n"
        )


class Emitter(
    VirtualCalls,
    BaseSubobjects,
    MemberLifetime,
    UnionLowering,
    MemoryLowering,
    IntegerLowering,
):
    def __init__(self, module, definition=None, values=None):
        self.module = module
        self.site = definition.syntax.name if definition else None
        self.d = definition
        self.plan = module.plans.get(definition.symbol) if definition else None
        self.depth = 0
        self.probing_delegation = False
        self.delegate_edge = None
        self.names = definition.names if definition else module.names
        self.types = definition.types if definition else module.types
        self.policy = definition.policy if definition else module.policy
        self.default_int = definition.default_int if definition else module.default_int
        self.scopes = [values or {}, {}]
        self.extents = {}
        self.temporaries = []
        self.tracking = bool(definition and uses_storage(definition.syntax.body))
        self.loops = []
        self.statement_label = None
        self.declared_at = {}
        self.entry = []
        self.lines = []
        self.serial = count()
        self.block = "entry"
        self.reachable = True
        self.evaluated = True
        self.required = False
        self.may_throw = False
        self.budget = None

    def resolve(self, typ):
        return self.module.bind_type(
            typ, self.types, self.d.syntax.name if self.d else self.site, self
        )

    def ident(self):
        return f"v{next(self.serial)}"

    def emit(self, instruction):
        self.lines.append("  " + instruction)

    def temp(self, instruction):
        result = "%" + self.ident()
        self.emit(f"{result} = {instruction}")
        return result

    def jump(self, label):
        self.emit("br label %" + label)

    def label(self, name):
        self.lines.append(name + ":")
        self.block = name

    def guard(self, condition):
        trap, resume = self.ident(), self.ident()
        self.emit(f"br i1 {condition}, label %{trap}, label %{resume}")
        self.label(trap)
        self.emit("call void @llvm.trap()")
        self.emit("unreachable")
        self.label(resume)

    def lookup(self, t):
        for scope in reversed(self.scopes):
            if t.text in scope:
                value = scope[t.text]
                if value is None:
                    raise Error(t, "use before initialization")
                return value
        if self.d and self.d.receiver:
            matches = member_paths(self.module, self.d.receiver, t.text)
            if matches and any(
                t.text in self.module.records[owner] for _, owner in matches
            ):
                obj = Value(self.d.receiver, address="%self", readonly=self.d.readonly)
                return self.member_value(self.member_owner(obj, t), t, load=False)
        if t.text in self.names:
            if self.names[t.text] is None:
                raise Error(t, "use before initialization")
            return self.names[t.text]
        raise Error(t, f"unknown name '{t.text}'")

    def load(self, v):
        if v.type in self.module.incomplete:
            raise Error(self.site, "read requires a complete object type")
        if (
            self.evaluated
            and not self.required
            and v.address in self.module.static_flags
        ):
            ready = self.temp(f"load i1, ptr {self.module.static_flags[v.address]}")
            self.guard(self.temp(f"xor i1 {ready}, true"))
        if v.address and v.constant is None:
            return replace(v, ir=self.temp(f"load {irtype(v.type)}, ptr {v.address}"))
        return v

    def reserve(self, t, scope):
        if t.text in scope:
            raise Error(t, f"duplicate declaration '{t.text}'")
        if any(t.text in outer for outer in self.scopes if outer is not scope):
            self.module.warn(t, "declaration shadows an outer binding")
        scope[t.text] = None

    def allocate(self, typ):
        ptr = "%" + self.ident()
        self.entry.append(f"  {ptr} = alloca {irtype(typ)}")
        return ptr

    def store(self, v, ptr):
        self.emit(f"store {irtype(v.type)} {v.ir}, ptr {ptr}")

    def temporary(self, v, ptr=None):
        if v.type not in self.module.destructors or v.temporary or v.address:
            return v
        if ptr is None:
            ptr = self.allocate(v.type)
            self.store(v, ptr)
        flag = self.allocate("bool")
        self.entry.append(f"  store i1 false, ptr {flag}")
        self.emit(f"store i1 true, ptr {flag}")
        self.temporaries.append((v.type, ptr, flag))
        return replace(v, temporary=ptr)

    def consume(self, v):
        if v.temporary:
            flag = next(flag for _, ptr, flag in self.temporaries if ptr == v.temporary)
            self.emit(f"store i1 false, ptr {flag}")

    def finish_expression(self):
        for typ, ptr, flag in reversed(self.temporaries):
            live = self.temp(f"load i1, ptr {flag}")
            drop, done = self.ident(), self.ident()
            self.emit(f"br i1 {live}, label %{drop}, label %{done}")
            self.label(drop)
            self.drop(typ, ptr)
            self.emit(f"store i1 false, ptr {flag}")
            self.jump(done)
            self.label(done)
        self.temporaries.clear()

    def aggregate(self, typ, members):
        if not members:
            return Value(typ, "zeroinitializer")
        if all(
            v.constant is not None or record(v.type) and not v.ir.startswith("%")
            for v in members
        ):
            elements = ", ".join(f"{irtype(v.type)} {v.ir}" for v in members)
            return Value(typ, "{ " + elements + " }")
        aggregate = "zeroinitializer"
        for index, v in enumerate(members):
            aggregate = self.temp(
                f"insertvalue {irtype(typ)} {aggregate}, {irtype(v.type)} {v.ir}, {index}"
            )
        return Value(typ, aggregate)

    def zero(self, typ):
        if enum_type(typ) and 0 not in self.module.enum_cases[typ]:
            raise Error(self.site, "enum has no zero-valued default")
        if typ.endswith("]"):
            return Value(typ, "zeroinitializer")
        if typ.endswith("*"):
            return Value(typ, "null")
        if typ == "nullptr_t":
            return Value(typ, "0")
        if typ.endswith("&") or typ.startswith("const<") and typ.endswith(">"):
            raise Error(
                self.site, "cannot default construct a reference or qualified view"
            )
        if record(typ):
            return self.aggregate(typ, self.module.records[typ].values())
        return literal(0, typ)

    def special(self, typ, op, tok):
        control = self.module.specials.get(typ, {}).get(op)
        if not control or control[0] == "delete":
            raise NoOperation(tok, f"no available {op.replace('_', ' ')}")
        if not control[1] and (not self.d or self.d.receiver != typ):
            raise NoOperation(tok, "inaccessible special member")
        for field in self.module.records[typ].values():
            base = field.type.split("[")[0]
            if record(base):
                self.special(base, op, tok)

    def construct(self, typ, args, tok, destination=None):
        if typ in self.module.incomplete:
            raise Error(tok, "construction requires a complete object type")
        if typ in self.module.signatures:
            raise Error(tok, "function type requires a pointer")
        if typ in self.module.unions:
            if len(args) == 1:
                return self.convert(self.expr(args[0]), typ, tok)
            default = self.module.unions[typ][1]
            if args or not default:
                raise Error(tok, "union construction requires a selected case")
            return self.variant(default, (), tok, use_defaults=True)
        if typ.endswith("]"):
            return self.construct_array(typ, args, tok)
        if record(typ):
            if not args and "default" in self.module.specials[typ]:
                availability, public = self.module.specials[typ]["default"]
                if (
                    availability == "delete"
                    or not public
                    and (not self.d or self.d.receiver != typ)
                ):
                    raise Error(tok, "default constructor unavailable")
            candidates = [
                c
                for c in self.module.constructors.get(typ, ())
                if c.accepts_arity(len(args))
            ]
            if candidates:
                actual = [self.expr(arg) for arg in args]
                ctor = self.select(candidates, actual, (), tok)
                if not ctor.accessible and (not self.d or self.d.receiver != typ):
                    raise NoOperation(tok, "inaccessible constructor")
                ptr = destination or self.allocate(typ)
                params = self.call_args(ctor, actual, tok)
                self.emit(
                    f"call void @{self.module.default_entry(ctor, len(actual))}({', '.join(['ptr ' + ptr] + params)})"
                )
                return self.temporary(
                    Value(typ, self.temp(f"load {irtype(typ)}, ptr {ptr}")), ptr
                )
            bases = self.module.bases.get(typ, ())
            fields = list(self.module.records[typ].values())[len(bases) :]
            own_table = "$vtable" in self.module.records[typ]
            if own_table:
                fields.pop()
            values = []
            for index, arg in enumerate(args):
                expected = fields[index].type if index < len(fields) else None
                v = self.expr(arg, expected)
                if len(args) == 1 and v.type == typ:
                    return self.convert(v, typ, tok)
                if expected is None:
                    raise Error(tok, "too many aggregate initializers")
                values.append(self.convert(v, expected, tok))
                self.consume(v)
            base_values = []
            for base in bases:
                value = self.construct(base, (), tok)
                self.consume(value)
                base_values.append(value)
            for default in fields[len(values) :]:
                v = (
                    self.construct(default.type, (), tok)
                    if record(default.type) or default.type.endswith("]")
                    else default
                )
                values.append(v)
                self.consume(v)
            if own_table:
                values.append(Value("void*", "null"))
            return self.temporary(
                self.value_tables(self.aggregate(typ, base_values + values))
            )
        if typ == "void" or len(args) > 1:
            raise Error(tok, "invalid scalar construction")
        return (
            self.convert(self.expr(args[0], typ), typ, tok) if args else self.zero(typ)
        )

    def object(self, node, global_object=False):
        q, typ, name, init = node.args
        self.site = name
        scope = self.names if global_object else self.scopes[-1]
        self.reserve(name, scope)
        typ = self.resolve(typ)
        if typ.endswith("&"):
            if global_object or len(init) != 1:
                raise Error(name, "local reference needs one lvalue initializer")
            base = self.place(init[0])
            target, readonly = referent(typ)
            paths = base_paths(self.module, base.type, target)
            if len(paths) != 1 or base.readonly and not (q or readonly):
                raise Error(name, "incompatible reference binding")
            address = self.subobject_address(base.address, base.type, paths[0])
            scope[name.text] = replace(
                base,
                type=target,
                address=address,
                readonly=bool(q) or readonly or base.readonly,
            )
            return
        if typ.startswith("const<") and typ.endswith(">"):
            q, typ = "const", typ[6:-1]
        if typ == "void":
            raise Error(name, "object cannot have void type")
        start = len(self.lines)
        ptr = (
            "@" + ir_name("cpn.g." + self.module.prefix + name.text)
            if global_object
            else None
        )
        previous_required = self.required
        self.required |= q == "constexpr"
        if typ == "auto":
            val = self.expr(init[0])
            typ = self.default_int if val.type == "integer" else val.type
        else:
            val = self.construct(typ, init, name, destination=ptr)
        self.required = previous_required
        val = self.convert(val, typ, name)
        if q == "constexpr" and (len(self.lines) != start or val.constant is None):
            raise Error(name, "constexpr initializer requires a constant")
        if global_object:
            define_static(self, name, typ, val, ptr, q)
        else:
            ptr = val.temporary or self.allocate(typ)
            if not val.temporary:
                self.store(val, ptr)
            self.consume(val)
            self.finish_expression()
        if not global_object:
            self.register(typ, ptr, scope)
            self.declared_at[id(node)] = ptr
        scope[name.text] = Value(
            typ,
            val.ir,
            val.constant if q == "constexpr" else None,
            ptr,
            bool(q),
            val.owner,
            val.generation,
            subobject=val.subobject,
        )

    def parameter_default(self, index, previous, fields):
        owner = self.d.default_owner or self.d
        p = owner.syntax.params[index]
        typ = self.d.params[index]
        saved = self.names, self.types, self.scopes, self.policy, self.default_int
        self.names, self.types = (
            owner.names,
            owner.types
            | {
                g.name: self.d.types[g.name]
                for g in owner.syntax.generics
                if g.name in self.d.types
            },
        )
        self.scopes = [self.scopes[0], fields, previous]
        self.policy, self.default_int = owner.policy, owner.default_int
        tok = p.name or owner.syntax.name
        try:
            if typ.endswith("&"):
                if len(p.default) != 1:
                    raise Error(tok, "reference default requires one initializer")
                return self.bind_argument(self.expr(p.default[0]), typ, tok)
            return self.construct(typ, p.default, tok)
        finally:
            self.names, self.types, self.scopes, self.policy, self.default_int = saved

    def function_ir(self, arity=None, symbol=None):
        f = self.d.syntax
        if any(t in self.module.incomplete for t in (*self.d.params, self.d.result)):
            raise Error(
                f.name, "definition requires complete parameter and result types"
            )
        if any(t in self.module.signatures for t in (*self.d.params, self.d.result)):
            raise Error(f.name, "function type requires a pointer")
        if any(t in ("void", "const<void>") for t in self.d.params):
            raise Error(f.name, "void parameter is invalid; use ()")
        labels, self.jump_cleanup = label_edges(f.body) if f.body else ({}, {})
        self.labels = {name: self.ident() for name in labels}
        self.used_labels = set()

        def discover(node):
            if isinstance(node, Node):
                if node.kind == "goto":
                    self.used_labels.add(node.args[0].text)
                discover(node.args)
            elif isinstance(node, (tuple, list)):
                for element in node:
                    discover(element)

        discover(f.body)
        args = ["ptr %self"] if self.d.receiver else []
        if self.depth:
            args.append("ptr %activation")
        self.field_flags = {}
        if self.d.phase:
            args.append("ptr %field.live")
        fields = {}
        if self.d.receiver:
            # Keep member lookup outside the parameter/local scope.
            self.scopes.insert(-1, fields)
            fields["this"] = Value(
                (
                    "const<" + self.d.receiver + ">"
                    if self.d.readonly
                    else self.d.receiver
                )
                + "*",
                "%self",
            )
            for index, (name, v) in enumerate(
                self.module.records[self.d.receiver].items()
            ):
                if name == "$vtable":
                    continue
                addr = self.temp(
                    f"getelementptr %{self.d.receiver}, ptr %self, i32 0, i32 {index}"
                )
                if self.d.phase:
                    flag = self.temp(f"getelementptr i1, ptr %field.live, i32 {index}")
                    self.field_flags[name] = (addr, flag)
                fields[name] = replace(
                    v, address=addr, constant=None, readonly=self.d.readonly
                )
        count = len(f.params) if arity is None else arity
        default_names = (self.d.default_owner or self.d).syntax.params
        previous, cells = {}, []
        for i, (p, typ) in enumerate(zip(f.params, self.d.params)):
            if i < count:
                args.append(f"{abi_type(typ, f.foreign)} %arg{i}")
                value = Value(typ, f"%arg{i}")
            else:
                value = self.parameter_default(i, previous, fields)
            if typ.endswith("&"):
                base, const = referent(typ)
                cell = Value(base, address=value.ir, readonly=p.readonly or const)
            else:
                ptr = value.temporary or self.allocate(typ)
                if not value.temporary:
                    self.store(value, ptr)
                self.consume(value)
                cell = Value(typ, address=ptr, readonly=p.readonly)
                self.register(typ, ptr, self.scopes[-1])
            if p.name:
                self.reserve(p.name, self.scopes[-1])
                self.scopes[-1][p.name.text] = cell
            if default_names[i].name:
                previous[default_names[i].name.text] = cell
            cells.append(cell)
        if self.plan and not self.probing_delegation:
            self.plan.initialize(self, fields, cells)
        virtual_default = arity is not None and self.d.slot is not None
        if f.body and not virtual_default:
            for stmt in f.body.args:
                self.statement(stmt)
        else:
            operands = [
                f"{abi_type(typ, f.foreign)} {cell.address if typ.endswith('&') else self.load(cell).ir}"
                for typ, cell in zip(self.d.params, cells)
            ]
            target = "@" + ir_name(self.d.symbol)
            if virtual_default:
                # Defaults belong to the statically selected contract. Transfer
                # the completed arguments to the final overrider exactly once.
                target = self.virtual_target(self.d, "%self")
                operands.insert(0, "ptr %self")
                for typ, cell in zip(self.d.params, cells):
                    if not typ.endswith("&"):
                        self.extents.pop(cell.address, None)
            call = f"call {abi_type(self.d.result, f.foreign, True)} {target}({', '.join(operands)})"
            if self.d.result == "void":
                self.emit(call)
            else:
                result = self.temp(call)
                self.cleanup(0)
                self.emit(f"ret {irtype(self.d.result)} {result}")
                self.label(self.ident())
                self.reachable = False
        if self.reachable:
            if self.d.result != "void":
                raise Error(f.name, "function can finish without returning a value")
            self.cleanup(0)
            self.emit("ret void")
        else:
            self.emit("unreachable")
        linkage = (
            ""
            if symbol is None and (f.foreign or self.d.symbol == "main")
            else "internal "
        )
        header = f"define {linkage}{abi_type(self.d.result, f.foreign, True)} @{ir_name(symbol or self.d.symbol)}({', '.join(args)}) {{"
        return "\n".join([header, "entry:", *self.entry, *self.lines, "}"])

    def boolean(self, node):
        v = self.expr(node)
        if v.type != "bool":
            raise Error(node.token, "condition requires bool")
        if node.kind == "binary" and node.token.text == "=":
            self.module.warn(
                node.token, "assignment used directly as a Boolean condition"
            )
        return v

    def statement(self, s):
        k, args = s.kind, s.args
        statement_label, self.statement_label = self.statement_label, None
        if k == "delegate":
            if not self.d or self.d.producers is None:
                raise Error(s.token, "delegate requires a constructor activation")
            actual = [self.expr(arg) for arg in args]
            if self.probing_delegation:
                if self.delegate_edge:
                    raise Error(s.token, "only one direct delegation is permitted")
                target = self.select(
                    self.module.constructors[self.d.receiver], actual, (), s.token
                )
                self.delegate_edge = target, len(actual)
                self.finish_expression()
            else:
                self.plan.delegate(self, actual, s.token)
            return
        if k == "label":
            label = self.labels[s.token.text]
            self.jump(label)
            self.label(label)
            if s.token.text in self.used_labels:
                self.reachable = True
                self.forget_lifetimes()
            self.statement_label = s.token.text
            self.statement(args[0])
        elif k == "goto":
            for item in reversed(self.jump_cleanup[id(s)]):
                ptr = self.declared_at.get(item)
                if ptr in self.extents:
                    self.drop_registered(self.extents[ptr], ptr)
            self.jump(self.labels[args[0].text])
            self.label(self.ident())
            self.reachable = False
        elif k == "configured_block":
            self.configured(s, None)
        elif k == "block":
            self.scopes.append({})
            for item in args:
                self.statement(item)
            self.cleanup(len(self.scopes) - 1, leaving=True)
            self.scopes.pop()
        elif k == "object":
            self.object(s)
        elif k == "expr":
            self.expr(args[0])
            self.finish_expression()
        elif k == "return":
            if (
                self.plan
                and self.reachable
                and any(
                    self.construction_fields[name] is None
                    for name in self.slot_addresses
                )
            ):
                raise Error(s.token, "return bypasses required construction")
            result = self.d.result
            if args[0] is None:
                if result != "void":
                    raise Error(s.token, "return value required")
                self.cleanup(0)
                self.emit("ret void")
            else:
                v = self.convert(self.expr(args[0], result), result, s.token)
                if handle(v.type) and v.owner:
                    raise Error(
                        s.token, "borrow of automatic storage escapes the function"
                    )
                self.consume(v)
                self.finish_expression()
                self.cleanup(0)
                self.emit(f"ret {irtype(result)} {v.ir}")
            self.label(self.ident())
            self.reachable = False
        elif k == "if_constexpr":
            cond, yes, no = args
            selected = self.constant_expr(cond, "bool").constant
            taken, discarded = (yes, no) if selected else (no, yes)
            if discarded:
                visible = set(self.names).union(*self.scopes)
                bind_names(discarded, visible, self.types, self.module.families)
            if taken:
                self.statement(taken)
        elif k == "if":
            cond, yes, no = args
            c = self.boolean(cond)
            self.finish_expression()
            a, b, done = self.ident(), self.ident(), self.ident()
            live = self.reachable
            self.emit(f"br i1 {c.ir}, label %{a}, label %{b}")
            self.label(a)
            self.reachable = live and c.constant != 0
            before = self.facts()
            evaluated = self.evaluated
            self.evaluated = evaluated and c.constant != 0
            self.statement(yes)
            yes_facts = self.extents
            self.extents = before
            self.evaluated = evaluated and c.constant != 1
            yes_live = self.reachable
            self.jump(done)
            self.label(b)
            self.reachable = live and c.constant != 1
            if no:
                self.statement(no)
            self.jump(done)
            self.label(done)
            self.evaluated = evaluated
            if yes_live:
                if self.reachable:
                    self.merge_facts(yes_facts)
                else:
                    self.extents = yes_facts
            self.reachable |= yes_live
        elif k in ("while", "for", "do"):
            self.forget_lifetimes()
            self.loop(s, statement_label)
            self.forget_lifetimes()
        elif k == "match":
            self.match(s)
        elif k == "switch":
            self.switch(s, statement_label)
            self.forget_lifetimes()
        elif k == "fallthrough":
            raise Error(s.token, "fallthrough must terminate a nonfinal switch arm")
        elif k in ("break", "continue"):
            target = args[0]
            loop = next(
                (
                    context
                    for context in reversed(self.loops)
                    if k in context and (not target or context["label"] == target.text)
                ),
                None,
            )
            if loop is None:
                raise Error(s.token, f"{k} outside an eligible control statement")
            loop[k + "_live"] |= self.reachable
            self.cleanup(loop["depth"])
            self.jump(loop[k])
            self.label(self.ident())
            self.reachable = False

    def switch(self, s, label_name):
        subject, arms = s.args
        value = self.expr(subject)
        self.finish_expression()
        if (
            value.type.endswith("]")
            or handle(value.type)
            or record(value.type)
            or value.type in ("bool", "char", "void")
        ):
            raise Error(subject.token, "switch requires an integer")
        if value.type == "integer":
            value = self.convert(value, self.default_int, subject.token)
        done = self.ident()
        labels = [self.ident() for _ in arms]
        cases = {}
        default = done
        for (case, body), label in zip(arms, labels):
            if case is None:
                if default != done:
                    raise Error(body.token, "duplicate default arm")
                default = label
            else:
                v = self.constant_expr(case, value.type)
                if v.constant in cases:
                    raise Error(case.token, "duplicate case value")
                cases[v.constant] = label
        if (
            enum_type(value.type)
            and default == done
            and set(cases) != self.module.enum_cases[value.type]
        ):
            self.module.warn(s.token, "switch omits enum cases")
        ty = irtype(value.type)
        table = " ".join(f"{ty} {n}, label %{label}" for n, label in cases.items())
        self.emit(f"switch {ty} {value.ir}, label %{default} [ {table} ]")
        context = {
            "label": label_name,
            "break": done,
            "break_live": False,
            "depth": len(self.scopes),
        }
        self.loops.append(context)
        live = self.reachable
        exit_live = live and default == done
        for i, ((_, body), label) in enumerate(zip(arms, labels)):
            self.forget_lifetimes()
            self.label(label)
            self.reachable = live
            falling = bool(body.args) and body.args[-1].kind == "fallthrough"
            if falling and i + 1 == len(arms):
                raise Error(body.args[-1].token, "final switch arm cannot fall through")
            self.statement(replace(body, args=body.args[:-1]) if falling else body)
            self.jump(labels[i + 1] if falling else done)
            if not falling:
                exit_live |= self.reachable
        self.loops.pop()
        self.label(done)
        self.reachable = exit_live or context["break_live"]

    def constant_expr(self, node, typ=None):
        start = len(self.lines)
        previous = self.required
        self.required = True
        v = self.expr(node, typ)
        self.required = previous
        if typ:
            v = self.convert(v, typ, node.token)
        if len(self.lines) != start or v.constant is None:
            raise Error(node.token, "constant expression required")
        return v

    def require_constraint(self, expr, tok):
        if expr and not self.constant_expr(expr, "bool").constant:
            raise Error(tok, "generic constraint is not satisfied")

    def loop(self, s, label_name):
        self.scopes.append({})
        init, cond, step, body = None, None, None, None
        if s.kind == "for":
            init, cond, step, body = s.args
        else:
            cond, body = s.args
        if init:
            self.statement(init)
        live = self.reachable
        test, run, update, done = (self.ident() for _ in range(4))
        loop = {
            "label": label_name,
            "break": done,
            "continue": update,
            "depth": len(self.scopes),
            "break_live": False,
            "continue_live": False,
        }
        self.loops.append(loop)
        self.jump(run if s.kind == "do" else test)
        self.label(test)
        v = self.boolean(cond) if cond else literal(1, "bool")
        self.finish_expression()
        self.emit(f"br i1 {v.ir}, label %{run}, label %{done}")
        self.label(run)
        self.reachable = live and (s.kind == "do" or v.constant != 0)
        self.statement(body)
        self.jump(update)
        self.label(update)
        if step:
            self.expr(step)
            self.finish_expression()
        self.jump(test)
        test_live = live if s.kind != "do" else self.reachable or loop["continue_live"]
        self.reachable = loop["break_live"] or (test_live and v.constant != 1)
        self.label(done)
        self.loops.pop()
        self.cleanup(len(self.scopes) - 1, leaving=True)
        self.scopes.pop()

    def destination(self, node):
        if node.kind == "group":
            return self.destination(node.args[0])
        v = self.place(node)
        field = self.field_name(node)
        if field:
            self.field_live(field, node.token)
        if node.kind == "name" and v.address in self.extents:
            self.live(v.address, 1, node.token)
        if not isinstance(v, Value) or not v.address or v.readonly:
            raise NoOperation(node.token, "writable lvalue required")
        return v

    def expr(self, node, expected=None):
        k, t, args = node.kind, node.token, node.args
        op = t.text
        if k == "expand":
            raise Error(t, "unexpanded pack in expression")
        if k == "predicate":
            from constraints import predicate

            return literal(int(predicate(self, t, args[0])), "bool")
        if k == "configured_expr":
            return self.configured(node, expected)
        if k == "nullptr":
            return Value("nullptr_t", "0")
        if k == "layout":
            arg = args[0]
            if isinstance(arg, str):
                typ = self.resolve(arg)
            else:
                from copy import copy

                probe = copy(self)
                probe.lines, probe.entry, probe.temporaries = [], [], []
                probe.extents = {k: replace(e) for k, e in self.extents.items()}
                probe.evaluated = False
                typ = probe.expr(arg).type
            if typ in ("integer", "void", "const<void>", "storage") or typ.endswith(
                "&"
            ):
                raise Error(t, "a complete object type is required")
            if typ in self.module.signatures:
                raise Error(t, "function type has no object layout")
            size, align = self.layout(typ)
            return literal(size if op == "sizeof" else align, "usize")
        if k == "integer":
            return literal(integer_value(t))
        if k == "string":
            raw = quoted_text(t).encode("utf-8") + bytes(1)
            name = f"@cpn.string.{next(self.module.ids)}"
            typ = f"const<u8>[{len(raw)}]"
            data = "".join(f"\\{b:02X}" for b in raw)
            self.module.ir.append(
                f'{name} = private unnamed_addr constant {irtype(typ)} c"{data}"'
            )
            return self.load(Value(typ, address=name, readonly=True))
        if k == "char":
            ch = quoted_text(t)
            if len(ch) != 1:
                raise Error(t, "character literal requires exactly one Unicode scalar")
            return literal(ord(ch), "char")
        if k == "bool":
            return literal(int(op == "true"), "bool")
        if k == "name":
            field = self.field_name(node)
            if field:
                self.field_live(field, t)
            v = self.lookup(t)
            if not isinstance(v, Value):
                raise Error(t, "function needs a call")
            if v.address in self.extents:
                self.live(v.address, 1, t)
            return self.load(v)
        if k == "group":
            return self.expr(args[0], expected)
        if k == "index":
            return self.index(node)
        if k == "member":
            field = self.field_name(node)
            if field in getattr(self, "field_flags", {}):
                self.field_live(field, t)
            if args[0].kind == "name" and args[0].token.text in self.types:
                base = self.types[args[0].token.text]
                if re.fullmatch(r"[iu](?:8|16|32|64|size)", base) and op in (
                    "MIN",
                    "MAX",
                ):
                    return literal(bounds(base)[op == "MAX"], base)
                raise Error(t, "unknown type member")
            obj = self.expr(args[0])
            return self.member_value(self.member_owner(obj, t), t)
        if k == "method":
            return self.method(self.expr(args[0]), t, args[1])
        if k == "call":
            return self.call(node)
        if k == "invoke":
            operand = args[0]
            while operand.kind == "group":
                operand = operand.args[0]
            if operand.kind == "prefix" and operand.token.text == "*":
                return self.indirect_call(self.expr(operand.args[0]), args[1], t)
            return self.indirect_call(self.expr(args[0]), args[1], t)
        if k in ("prefix", "postfix"):
            if op == "&":
                operand = args[0]
                while operand.kind == "group":
                    operand = operand.args[0]
                if operand.kind == "name":
                    value = self.lookup(operand.token)
                    if isinstance(value, tuple):
                        return self.function_address(value, expected, t)
                obj = self.place(args[0])
                typ = "const<" + obj.type + ">" if obj.readonly else obj.type
                owner = obj.address if obj.address in self.extents else ""
                self.live(owner, 1, t)
                return Value(typ + "*", obj.address, owner=owner, generation=1)
            if op == "*":
                return self.load(self.place(node))
            if op in ("++", "--"):
                dst = self.destination(args[0])
                old = self.load(dst)
                v = self.arithmetic(op[0], old, literal(1), t)
                self.store(v, dst.address)
                return (
                    replace(old, address="")
                    if k == "postfix"
                    else replace(v, address=dst.address)
                )
            v = self.expr(args[0], expected)
            if op == "!":
                if v.type != "bool":
                    raise NoOperation(t, "logical negation requires bool")
                if v.constant is not None:
                    return literal(1 - v.constant, "bool")
                return Value("bool", self.temp(f"xor i1 {v.ir}, true"))
            if (
                enum_type(v.type)
                or v.type.endswith("]")
                or record(v.type)
                or handle(v.type)
                or v.type in ("bool", "char", "void")
            ):
                raise NoOperation(t, "integer operand required")
            if op == "+":
                return replace(v, address="")
            if op == "-":
                return self.arithmetic("-", literal(0), v, t)
            if v.type == "integer":
                v = self.convert(v, expected or self.default_int, t)
            if v.constant is not None:
                lo, _ = bounds(v.type)
                return literal((~v.constant - lo) % (1 << width(v.type)) + lo, v.type)
            return Value(v.type, self.temp(f"xor {irtype(v.type)} {v.ir}, -1"))
        if k == "conditional" or op in ("&&", "||"):
            return self.choice(node, expected)
        if op in ASSIGN:
            dst = self.destination(args[0])
            if record(dst.type):
                rhs = self.expr(args[1], dst.type)
                if op != "=" or rhs.type != dst.type:
                    raise Error(t, "no matching record assignment operator")
                self.special(
                    dst.type,
                    ("move" if rhs.expiring or not rhs.address else "copy")
                    + "_assignment",
                    t,
                )
                self.store(self.value_tables(rhs, dst.address), dst.address)
                return replace(rhs, address=dst.address, temporary="", expiring=False)
            old = self.load(dst) if op != "=" else None
            rhs = self.expr(args[1], dst.type if op == "=" else None)
            if old:
                rhs = self.arithmetic(op[:-1], old, rhs, t)
            v = self.convert(rhs, dst.type, t)
            if (
                handle(dst.type)
                and (v.owner or dst.owner)
                and (v.owner, v.generation) != (dst.owner, dst.generation)
            ):
                raise Error(
                    t,
                    "changing the provenance of a tracked local borrow is unsupported",
                )
            self.store(v, dst.address)
            return replace(v, address=dst.address, readonly=False)
        a = self.expr(args[0])
        b = self.expr(args[1])
        return self.arithmetic(op, a, b, t, expected)

    def configured(self, node, expected):
        pairs, body = node.args
        old = self.policy, self.default_int
        for key, value in pairs.items():
            if key == "numeric.integer.overflow" and value in (
                "checked",
                "wrapping",
                "saturating",
                "native",
            ):
                self.policy = value
            elif key == "numeric.literal.integer_default" and value in (
                "i8",
                "i16",
                "i32",
                "i64",
            ):
                self.default_int = value
            else:
                raise Error(
                    node.token, f"unsupported local configuration {key} = {value}"
                )
        try:
            if node.kind == "configured_block":
                self.statement(body)
            else:
                return self.expr(body, expected)
        finally:
            self.policy, self.default_int = old

    def choice(self, node, expected):
        cond, *branches = node.args
        c = self.boolean(cond)
        if self.required:
            if c.constant is None:
                raise Error(cond.token, "constant condition required")
            bind_names(
                branches,
                set(self.names).union(*self.scopes),
                self.types,
                self.module.families,
            )
            if node.kind == "conditional":
                return self.expr(branches[0 if c.constant else 1], expected)
            if bool(c.constant) == (node.token.text == "&&"):
                return self.boolean(branches[0])
            return literal(c.constant, "bool")
        a, b, done = self.ident(), self.ident(), self.ident()
        self.emit(f"br i1 {c.ir}, label %{a}, label %{b}")
        old = self.evaluated
        original = self.facts()
        values = []
        facts = []
        # Edge blocks allow conversions to be emitted after binding both arms.
        for idx, lab in enumerate((a, b)):
            self.extents = {p: replace(e) for p, e in original.items()}
            self.label(lab)
            self.evaluated = old and c.constant != idx
            op = node.token.text
            if op == "?":
                v = self.expr(branches[idx], expected)
            elif (op == "&&") == (idx == 0):
                v = self.boolean(branches[0])
            else:
                v = literal(int(idx == 0), "bool")
            edge = self.ident()
            self.jump(edge)
            values.append((v, edge))
            facts.append(self.extents)
        self.evaluated = old
        if c.constant is not None:
            self.extents = facts[0 if c.constant else 1]
        else:
            self.merge_facts(facts[0])
        (x, left), (y, right) = values
        if x.type == y.type:
            typ = (expected or self.default_int) if x.type == "integer" else x.type
        elif x.type == "integer" or y.type == "integer":
            typ = y.type if x.type == "integer" else x.type
        elif (
            enum_type(x.type)
            or enum_type(y.type)
            or handle(x.type)
            or handle(y.type)
            or x.type.endswith("]")
            or y.type.endswith("]")
            or record(x.type)
            or record(y.type)
            or x.type in ("bool", "char", "void")
            or y.type in ("bool", "char", "void")
        ):
            raise Error(node.token, "incompatible conditional branches")
        else:
            typ = common(x.type, y.type, node.token)
        parts = []
        for v, edge in values:
            self.label(edge)
            v = self.convert(v, typ, node.token)
            parts.append(f"[ {v.ir}, %{edge} ]")
            self.jump(done)
        self.label(done)
        ir = self.temp(f"phi {irtype(typ)} {', '.join(parts)}")
        if x.address and y.address and x.type == y.type:
            address = self.temp(
                f"phi ptr [ {x.address}, %{left} ], [ {y.address}, %{right} ]"
            )
            return Value(typ, ir, address=address, readonly=x.readonly or y.readonly)
        return Value(typ, ir)

    def member_value(self, obj, t, load=True):
        op = t.text
        fields = self.module.records.get(obj.type, {})
        if (obj.type, op) in self.module.private and (
            not self.d or self.d.receiver != obj.type
        ):
            raise NoOperation(t, "inaccessible member")
        if op not in fields:
            raise NoOperation(t, f"unknown member '{op}' of {obj.type}")
        typ = fields[op].type
        index = list(fields).index(op)
        if obj.address:
            addr = self.temp(
                f"getelementptr {irtype(obj.type)}, ptr {obj.address}, i32 0, i32 {index}"
            )
            cell = Value(typ, address=addr, readonly=obj.readonly)
            return self.load(cell) if load else cell
        ir = self.temp(f"extractvalue {irtype(obj.type)} {obj.ir}, {index}")
        return Value(typ, ir)

    def method(self, obj, tok, operands):
        category = "&&" if obj.expiring or not obj.address else "&"
        obj = self.member_owner(obj, tok)
        if tok.text in self.module.records[obj.type]:
            return self.indirect_call(self.member_value(obj, tok), operands, tok)
        methods = self.module.methods.get((obj.type, tok.text), [])
        applicable = [
            m
            for m in methods
            if (m.readonly or not obj.readonly)
            and m.syntax.receiver_category in ("", category)
        ]
        if not applicable:
            raise NoOperation(tok, "no applicable member function")
        args = [self.expr(expr) for expr in operands]
        # Receiver qualification is an independent overload rank.
        d = self.select(applicable, args, (), tok, receiver=obj)
        self.may_throw |= not d.syntax.noexcept
        if not d.accessible and (not self.d or self.d.receiver != obj.type):
            raise NoOperation(tok, "inaccessible member function")
        addr = obj.address or obj.temporary
        if not addr:
            addr = self.allocate(obj.type)
            self.store(obj, addr)
        actual = ", ".join(["ptr " + addr] + self.call_args(d, args, tok))
        target = (
            self.virtual_target(d, addr)
            if d.slot is not None and len(args) == len(d.params)
            else "@" + self.module.default_entry(d, len(args))
        )
        ir = f"call {irtype(d.result)} {target}({actual})"
        if d.result == "void":
            self.emit(ir)
            return Value("void")
        return self.temporary(Value(d.result, self.temp(ir)))

    def function_address(self, candidates, expected, tok):
        signature = (
            self.module.signatures.get(expected[:-1])
            if expected and expected.endswith("*")
            else None
        )
        if not signature:
            raise Error(tok, "function address requires a target function-pointer type")
        matches = [
            d
            for d in candidates
            if d.result == signature.result
            and d.params == signature.params
            and (not signature.noexcept or d.syntax.noexcept)
            and not d.syntax.foreign
            and not d.syntax.generics
            and d.syntax.mode != "consteval"
        ]
        if len(matches) != 1:
            raise Error(tok, "no unique compatible function for target pointer")
        d = matches[0]
        self.module.used.add(d.symbol)
        return Value(expected, "@" + ir_name(d.symbol))

    def indirect_call(self, pointer, operands, tok):
        signature = (
            self.module.signatures.get(pointer.type[:-1])
            if pointer.type.endswith("*")
            else None
        )
        if not signature or len(operands) != len(signature.params):
            raise Error(tok, "invalid indirect call or wrong argument count")
        self.may_throw |= not signature.noexcept
        if self.required or signature.result.endswith("&"):
            raise Error(tok, "unsupported indirect call in this context")
        if pointer.ir == "null":
            raise Error(tok, "call through null function pointer")
        self.guard(self.temp(f"icmp eq ptr {pointer.ir}, null"))
        params = []
        for expr, typ in zip(operands, signature.params):
            value = self.bind_argument(self.expr(expr, typ), typ, tok)
            self.consume(value)
            params.append(f"{irtype(typ)} {value.ir}")
        call = f"call {irtype(signature.result)} {pointer.ir}({', '.join(params)})"
        if signature.result == "void":
            self.emit(call)
            return Value("void")
        return self.temporary(Value(signature.result, self.temp(call)))

    def call(self, node):
        t = node.token
        explicit, operands = node.args
        variant = self.names.get(t.text)
        if isinstance(variant, Variant):
            return self.variant(variant, operands, t)
        if t.text == "std::move" and len(operands) == 1:
            return replace(self.expr(operands[0]), expiring=True)
        if t.text == "std::forward":
            if len(explicit) != 1 or len(operands) != 1:
                raise Error(t, "std::forward requires a type and one operand")
            target = self.resolve(explicit[0])
            base, readonly = referent(target)
            v = self.expr(operands[0])
            if (
                base != v.type
                or (v.readonly and not readonly)
                or (
                    target.endswith("&")
                    and not target.endswith("&&")
                    and (not v.address or v.expiring)
                )
            ):
                raise Error(t, "incompatible forwarding type or category")
            return replace(
                v,
                expiring=not target.endswith("&") or target.endswith("&&"),
                readonly=readonly or v.readonly,
            )
        if t.text in ("destroy_base", "abandon_base") and t.text not in self.names:
            if (
                not self.d
                or not self.d.phase
                or len(explicit) != 1
                or len(operands) != 1
                or operands[0].kind != "name"
                or operands[0].token.text != "this"
            ):
                raise Error(
                    t, "base lifetime request requires the current destructor layer"
                )
            base = self.resolve(explicit[0])
            if base not in self.module.bases[self.d.receiver]:
                raise Error(t, "base request must select a direct nonvirtual base")
            self.end_field("$base:" + base, replace(t, text=t.text.partition("_")[0]))
            self.finish_expression()
            self.cleanup(0)
            self.emit("ret void")
            self.label(self.ident())
            self.reachable = False
            return Value("void")
        if (
            t.text in ("storage_of", "destroy", "abandon", "construct_at")
            and t.text not in self.names
            and all(t.text not in scope for scope in self.scopes)
        ):
            return self.storage_op(node)
        if t.text in self.types or t.text.partition("<")[0] in self.module.families:
            typ = self.module.bind_type(t.text, self.types, t, self)
            return replace(self.construct(typ, operands, t), address="")
        if (
            self.d
            and member_paths(self.module, self.d.receiver, t.text)
            and not any(t.text in s for s in self.scopes)
        ):
            obj = Value(self.d.receiver, address="%self", readonly=self.d.readonly)
            return self.method(obj, t, operands)
        candidates = self.lookup(t)
        if isinstance(candidates, Value):
            return self.indirect_call(self.load(candidates), operands, t)
        if not isinstance(candidates, tuple):
            raise Error(t, "object is not callable")
        args = []
        for index, arg in enumerate(operands):
            target = None
            if arg.kind == "prefix" and arg.token.text == "&":
                targets = {
                    d.params[index]
                    for d in candidates
                    if d.accepts_arity(len(operands))
                }
                if len(targets) == 1:
                    target = targets.pop()
            args.append(self.expr(arg, target))
        d = self.select(candidates, args, explicit, t)
        self.may_throw |= not d.syntax.noexcept
        if self.required or d.syntax.mode == "consteval":
            # Binding a consteval definition can reference its own parameters.
            # Only its concrete invocation enters the compile-time interpreter.
            symbolic = (
                self.d and self.d.syntax.mode == "consteval" and not self.required
            )
            if not symbolic:
                if d.syntax.mode not in ("constexpr", "consteval") or not d.syntax.body:
                    raise Error(
                        t,
                        "constant evaluation requires a visible constexpr or consteval definition",
                    )
                from constant import ConstantFrame

                values = [self.convert(v, p, t) for v, p in zip(args, d.params)]
                return ConstantFrame(self.module, d, self.budget or [100000]).evaluate(
                    values
                )
        actual = ", ".join(self.call_args(d, args, t))
        self.module.used.add(d.symbol)
        symbol = self.module.default_entry(d, len(args))
        call = f"call {abi_type(d.result, d.syntax.foreign, True)} @{ir_name(symbol)}({actual})"
        if d.result == "void":
            self.emit(call)
            return Value("void")
        return self.temporary(Value(d.result, self.temp(call)))

    def bind_argument(self, v, typ, tok):
        if not typ.endswith("&"):
            return self.convert(v, typ, tok)
        if self.reference_rank(v, typ) is None:
            raise Error(tok, "incompatible reference argument")
        address = v.address or v.temporary
        base, _ = referent(typ)
        paths = base_paths(self.module, v.type, base)
        if not address:
            materialized = v.type if paths else base
            address = self.allocate(materialized)
            self.store(self.convert(v, materialized, tok), address)
        if paths:
            address = self.subobject_address(address, v.type, paths[0])
        return Value(typ, address)

    def reference_rank(self, v, typ):
        base, const = referent(typ)
        expiring = v.expiring or not v.address
        if v.readonly and not const or typ.endswith("&&") and not expiring:
            return None
        if not typ.endswith("&&") and expiring and not const:
            return None
        if v.type == base:
            return int(const and not v.readonly)
        if len(base_paths(self.module, v.type, base)) == 1:
            return 1 + int(const and not v.readonly)
        if v.type == "integer" and re.fullmatch(r"[iu](8|16|32|64|size)", base):
            if bounds(base)[0] <= v.constant <= bounds(base)[1]:
                return int(base != self.default_int) + int(const)
        return None

    def call_args(self, d, args, t):
        converted = [self.bind_argument(v, typ, t) for v, typ in zip(args, d.params)]
        for v in converted:
            self.consume(v)
        return [f"{abi_type(v.type, d.syntax.foreign)} {v.ir}" for v in converted]

    def select(self, candidates, args, explicit, t, receiver=None):
        choices = []
        for d in candidates:
            if not d.accepts_arity(len(args)):
                continue
            if d.syntax.generics:
                d = self.module.instantiate(d, args, explicit, self, t)
            ranks = [int(d.readonly and not receiver.readonly)] if receiver else []
            for v, typ in zip(args, d.params):
                if typ.endswith("&"):
                    rank = self.reference_rank(v, typ)
                    if rank is None:
                        break
                    ranks.append(rank)
                elif v.type == typ or (
                    v.type == "integer"
                    and typ == self.default_int
                    and bounds(typ)[0] <= v.constant <= bounds(typ)[1]
                ):
                    ranks.append(0)
                elif (
                    (v.type == "nullptr_t" and typ.endswith("*"))
                    or self.module.weakens_noexcept(v.type, typ)
                    or self.base_pointer_path(v.type, typ)
                ):
                    ranks.append(1)
                elif (
                    enum_type(v.type)
                    or enum_type(typ)
                    or v.type.endswith("]")
                    or typ.endswith("]")
                    or handle(v.type)
                    or handle(typ)
                    or record(v.type)
                    or record(typ)
                    or v.type in ("bool", "char", "void")
                    or typ in ("bool", "char", "void")
                    or (v.type != "integer" and ("size" in typ) != ("size" in v.type))
                ):
                    break
                else:
                    lo, hi = bounds(typ)
                    a, b = (
                        (v.constant, v.constant)
                        if v.constant is not None
                        else bounds(v.type)
                    )
                    if not lo <= a <= b <= hi:
                        break
                    ranks.append(1)
            else:
                choices.append((ranks, d))
        best = [
            d
            for r, d in choices
            if not any(
                other != r and all(x <= y for x, y in zip(other, r))
                for other, _ in choices
            )
        ]
        if not best:
            raise NoOperation(t, "no matching function")
        if len(best) != 1:
            raise Error(t, "ambiguous call")
        return best[0]
