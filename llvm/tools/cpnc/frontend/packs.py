"""Ordered substitution of ordinary CPN26 type and constant packs."""

from dataclasses import replace
import re

from syntax import Error, Function, Node, Parameter, Token


def pack_arity(function, explicit, actual, tok):
    fixed_generics = len(function.generics) - 1
    expansions = sum(p.expansion for p in function.params)
    supplied = max(0, len(explicit) - fixed_generics)
    if not expansions:
        return supplied
    surplus = len(actual) - (len(function.params) - expansions)
    if (
        surplus < 0
        or surplus % expansions
        or (supplied and supplied != surplus // expansions)
    ):
        raise Error(tok, "incompatible pack lengths or argument count")
    return surplus // expansions


class Expansion:
    def __init__(self, module, pack, count, tok, names=()):
        self.module = module
        self.pack = pack
        self.count = count
        self.names = {pack.name, *names}
        self.tok = tok
        self.words = re.compile(r"\$expr\d+|[^\W\d]\w*", re.UNICODE)

    def element(self, name, index):
        return f"$pack{index}_{name}"

    def parameters(self, generics):
        return [
            *generics[:-1],
            *(
                replace(self.pack, name=self.element(self.pack.name, i), pack=False)
                for i in range(self.count)
            ),
        ]

    def dependent(self, value):
        if isinstance(value, Node):
            return self.dependent(value.token) or self.dependent(value.args)
        if isinstance(value, Token):
            return self.dependent(value.text)
        if isinstance(value, (tuple, list)):
            return any(self.dependent(v) for v in value)
        if isinstance(value, str):
            return any(
                word in self.names
                or (
                    word in self.module.type_expressions
                    and self.dependent(self.module.type_expressions[word])
                )
                for word in self.words.findall(value)
            )
        return False

    def spelling(self, text, index):
        if not self.dependent(text):
            return text

        def word(match):
            original = match[0]
            if original in self.names:
                if index is None:
                    raise Error(self.tok, f"unexpanded pack '{original}'")
                return self.element(original, index)
            expression = self.module.type_expressions.get(original)
            if expression and self.dependent(expression):
                key = f"$expr{len(self.module.type_expressions)}"
                self.module.type_expressions[key] = self.visit(expression, index)
                return key
            return original

        return self.words.sub(word, text)

    def sequence(self, items, index):
        result = []
        for item in items:
            if isinstance(item, Node) and item.kind == "expand":
                pattern = item.args[0]
                if not self.dependent(pattern):
                    raise Error(item.token, "expansion requires an unexpanded pack")
                result.extend(self.visit(pattern, i) for i in range(self.count))
            elif isinstance(item, Parameter) and item.expansion:
                if not self.dependent(item.type):
                    raise Error(
                        item.name or self.tok,
                        "parameter expansion type must depend on a pack",
                    )
                result.extend(
                    self.visit(replace(item, expansion=False), i)
                    for i in range(self.count)
                )
            else:
                result.append(self.visit(item, index))
        return type(items)(result)

    def visit(self, value, index=None):
        if isinstance(value, Node):
            # A quoted token's contents do not take part in name substitution.
            if value.kind in ("char", "string"):
                return value
            return replace(
                value,
                token=self.visit(value.token, index),
                args=self.sequence(value.args, index),
            )
        if isinstance(value, (list, tuple)):
            return self.sequence(value, index)
        if isinstance(value, Token):
            return replace(value, text=self.spelling(value.text, index))
        if isinstance(value, str):
            # A pack expansion inside a serialized record-family type-id.
            if "..." in value:

                def spread(match):
                    pattern = match[1]
                    if not self.dependent(pattern):
                        raise Error(self.tok, "type expansion requires a pack")
                    return ",".join(
                        self.spelling(pattern, i) for i in range(self.count)
                    )

                value = re.sub(r"([\w$:*&\[\]]+)\.\.\.", spread, value)
                value = value.replace(",>", ">").replace("<,", "<").replace(",,", ",")
            return self.spelling(value, index)
        if isinstance(value, Parameter):
            return replace(
                value,
                type=self.visit(value.type, index),
                name=self.visit(value.name, index),
                default=self.visit(value.default, index),
            )
        if isinstance(value, Function):
            names = [p.name.text for p in value.params if p.expansion and p.name]
            local = Expansion(self.module, self.pack, self.count, self.tok, names)
            return replace(
                value,
                result=local.visit(value.result),
                params=local.visit(value.params),
                body=local.visit(value.body),
                requirement=local.visit(value.requirement),
            )
        if isinstance(value, dict):
            return {key: self.visit(v, index) for key, v in value.items()}
        return value
