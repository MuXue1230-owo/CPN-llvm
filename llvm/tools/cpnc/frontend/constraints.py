"""Evaluate ordinary type predicates and structural requirements (chapters 10 and 27)."""

from copy import copy

from numeric import Value, record
from syntax import Error, NoOperation


def predicate(caller, tok, args):
    from compiler import Emitter

    name = tok.text
    if name not in caller.module.constraints:
        count = 2 if name == "SameType" else 1
        if len(args) != count:
            raise Error(tok, "wrong number of type predicate arguments")
        types = [caller.resolve(arg) for arg in args]
        typ = types[0]
        if name == "SameType":
            return typ == types[1]
        is_object = (
            typ != "void"
            and not typ.endswith("&")
            and typ not in caller.module.signatures
        )
        if name == "ObjectType":
            return is_object
        complete = (
            is_object
            and typ not in caller.module.incomplete
            and (not record(typ) or typ in caller.module.records)
        )
        if name == "CompleteType" or not complete:
            return complete
        element = typ.split("[")[0]
        if not record(element):
            return True
        try:
            operation = (
                "copy_constructor"
                if name == "CopyConstructible"
                else "move_constructor"
            )
            caller.special(element, operation, tok)
        except NoOperation:
            return False
        return True

    params, requirements, captured = caller.module.constraints[name]
    context = copy(captured)
    context.used = set()
    site = Emitter(context)
    site.site = tok
    caller.module.generic_arguments(params, args, site, caller, tok)
    for rule in requirements:
        if rule[0] == "predicate":
            if not site.constant_expr(rule[1], "bool").constant:
                return False
        elif rule[0] == "type":
            head, _, member = rule[1].partition("::")
            if not member:
                raise Error(tok, "a nested type requirement needs a qualified name")
            if site.types.get(head, head) + "::" + member not in site.types:
                return False
        else:
            probe = Emitter(context)
            probe.types, probe.site, probe.evaluated = site.types, tok, False
            probe.scopes = [*site.scopes, {}]
            for p in rule[1]:
                typ = probe.resolve(p.type).rstrip("&")
                readonly = p.readonly or typ.startswith("const<") and typ.endswith(">")
                if typ.startswith("const<") and typ.endswith(">"):
                    typ = typ[6:-1]
                if p.name:
                    probe.reserve(p.name, probe.scopes[-1])
                    probe.scopes[-1][p.name.text] = Value(
                        typ, address=probe.allocate(typ), readonly=readonly
                    )
            for expr, spelling, noexcept in rule[2]:
                expected = probe.resolve(spelling)
                probe.may_throw = False
                try:
                    result = probe.expr(expr)
                except NoOperation:
                    return False
                category = "&&" if result.expiring else "&" if result.address else ""
                result_type = result.type
                if category and result.readonly:
                    result_type = f"const<{result_type}>"
                if result_type + category != expected or (noexcept and probe.may_throw):
                    return False
    return True
