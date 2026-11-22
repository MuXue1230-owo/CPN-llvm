"""Required evaluation of scalar functions, using the frontend's target arithmetic."""

from dataclasses import replace

from compiler import Emitter
from numeric import Value, literal
from syntax import Error


class Transfer(Exception):
    def __init__(self, kind, value=None):
        self.kind, self.value = kind, value


class ConstantFrame(Emitter):
    def __init__(self, module, definition, budget):
        super().__init__(module, definition)
        self.budget = budget
        self.memory = {}
        self.site = definition.syntax.name
        self.required = True

    def tick(self):
        self.budget[0] -= 1
        if self.budget[0] < 0:
            raise Error(self.site, "constant evaluation step budget exhausted")

    def evaluate(self, args):
        previous = {}
        owner = self.d.default_owner or self.d
        for i, p in enumerate(self.d.syntax.params):
            value = (
                args[i] if i < len(args) else self.parameter_default(i, previous, {})
            )
            if value.constant is None:
                raise Error(self.site, "constant argument required")
            name = p.name or replace(self.site, text=f"$param{i}")
            self.variable(name, value, p.readonly)
            canonical = owner.syntax.params[i].name
            if canonical:
                previous[canonical.text] = self.scopes[-1][name.text]
        try:
            self.statement(self.d.syntax.body)
        except Transfer as flow:
            if flow.kind != "return":
                raise Error(self.site, "invalid compile-time control transfer")
            return flow.value
        if self.d.result != "void":
            raise Error(self.site, "constant invocation completed without a result")
        return Value("void")

    def guard(self, condition):
        if condition != "false":
            raise Error(self.site, "terminal failure in required constant evaluation")

    def temp(self, instruction):
        raise Error(
            self.site, "operation is unavailable in required constant evaluation"
        )

    def variable(self, name, v, readonly):
        if v.constant is None:
            raise Error(name, "constant initializer required")
        slot = self.ident()
        cell = Value(v.type, address=slot, readonly=readonly)
        self.scopes[-1][name.text] = cell
        self.memory[slot] = v

    def load(self, v):
        if v.address in self.memory:
            return replace(
                self.memory[v.address], address=v.address, readonly=v.readonly
            )
        if v.constant is None:
            raise Error(self.site, "read of runtime state during constant evaluation")
        return v

    def store(self, v, address):
        if address not in self.memory:
            raise Error(self.site, "write to runtime state during constant evaluation")
        self.memory[address] = replace(v, address="")

    def choice(self, node, expected):
        cond, *arms = node.args
        c = self.boolean(cond).constant
        if node.token.text == "?":
            return self.expr(arms[0 if c else 1], expected)
        if bool(c) == (node.token.text == "&&"):
            return self.boolean(arms[0])
        return literal(int(bool(c)), "bool")

    def statement(self, node):
        self.tick()
        k, args = node.kind, node.args
        if k == "block":
            self.scopes.append({})
            try:
                for s in args:
                    self.statement(s)
            finally:
                for cell in self.scopes.pop().values():
                    if isinstance(cell, Value):
                        self.memory.pop(cell.address, None)
        elif k == "object":
            q, typ, name, init = args
            self.reserve(name, self.scopes[-1])
            if typ == "auto":
                v = self.expr(init[0])
                typ = self.default_int if v.type == "integer" else v.type
            else:
                typ = self.resolve(typ)
                v = self.construct(typ, init, name)
            self.variable(name, self.convert(v, typ, name), bool(q))
        elif k == "return":
            result = Value("void")
            if args[0] is not None:
                result = self.convert(
                    self.expr(args[0], self.d.result), self.d.result, node.token
                )
            raise Transfer("return", replace(result, address=""))
        elif k in ("break", "continue"):
            raise Transfer(k)
        elif k in ("if", "if_constexpr"):
            cond, yes, no = args
            arm = yes if self.boolean(cond).constant else no
            if arm:
                self.statement(arm)
        elif k in ("while", "for", "do"):
            init, cond, step, body = (
                args if k == "for" else (None, args[0], None, args[1])
            )
            self.scopes.append({})
            try:
                if init:
                    self.statement(init)
                first = True
                while (
                    (first and k == "do") or cond is None or self.boolean(cond).constant
                ):
                    self.tick()
                    first = False
                    try:
                        self.statement(body)
                    except Transfer as flow:
                        if flow.kind == "break":
                            break
                        if flow.kind != "continue":
                            raise
                    if step:
                        self.expr(step)
            finally:
                self.scopes.pop()
        elif k == "expr":
            self.expr(args[0])
        elif k == "configured_block":
            self.configured(node, None)
        elif k != "empty":
            raise Error(
                node.token, f"{k} is unavailable in required constant evaluation"
            )
