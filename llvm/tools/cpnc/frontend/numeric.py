"""Fixed-integer binding and LLVM lowering for chapters 2, 4, and 7."""

from dataclasses import dataclass, replace
import operator

from syntax import Error, NoOperation


@dataclass(frozen=True)
class Value:
    type: str
    ir: str = ""
    constant: int | None = None
    address: str = ""
    readonly: bool = False
    owner: str = ""
    generation: int | str = 0
    temporary: str = ""
    expiring: bool = False
    subobject: bool = False


def literal(number, typ="integer"):
    return Value(typ, str(number), number)


def enum_type(typ):
    return typ.startswith("enum.") and not typ.endswith(("*", "&", "]"))


def width(typ):
    if enum_type(typ):
        return width(typ.rsplit(".", 1)[1])
    if typ == "char":
        return 32
    if typ in ("isize", "usize"):
        return 64
    return 1 if typ == "bool" else int(typ[1:])


def record(typ):
    return typ.startswith("record.") and not handle(typ) and not typ.endswith("]")


def handle(typ):
    return typ.endswith(("*", "&")) or typ in ("storage", "nullptr_t")


def resolve_type(typ, bindings):
    if typ.endswith("]"):
        element, extent = typ[:-1].rsplit("[", 1)
        return f"{resolve_type(element, bindings)}[{bindings.get(extent, extent)}]"
    if typ.endswith(("*", "&")):
        return resolve_type(typ[:-1], bindings) + typ[-1]
    if typ.startswith("const<") and typ.endswith(">"):
        return "const<" + resolve_type(typ[6:-1], bindings) + ">"
    return bindings.get(typ, typ)


def irtype(typ):
    if typ.startswith("const<") and typ.endswith(">"):
        return irtype(typ[6:-1])
    if typ.endswith("]"):
        element, extent = typ[:-1].rsplit("[", 1)
        if extent == "0":
            return "{ [0 x " + irtype(element) + "], i8 }"
        return f"[{extent} x {irtype(element)}]"
    if handle(typ):
        return "i8" if typ == "nullptr_t" else "ptr"
    if record(typ):
        return "%" + typ
    return "void" if typ == "void" else f"i{width(typ)}"


def bounds(typ):
    n = width(typ)
    if typ.startswith("i"):
        return -(1 << (n - 1)), (1 << (n - 1)) - 1
    return 0, (1 << n) - 1


def common(a, b, token):
    if a == b:
        return a
    if "size" in a or "size" in b:
        raise Error(token, "platform and fixed integers require explicit unification")
    if a[0] == b[0]:
        return max((a, b), key=width)
    signed, unsigned = (a, b) if a[0] == "i" else (b, a)
    n = width(signed) if width(signed) > width(unsigned) else 2 * width(unsigned)
    if n > 64:
        raise Error(token, f"derived type i{n} is unavailable")
    return f"i{n}"


def quotient(a, b):
    q = abs(a) // abs(b)
    return -q if (a < 0) != (b < 0) else q


OPS = {
    "+": operator.add,
    "-": operator.sub,
    "*": operator.mul,
    "/": quotient,
    "%": lambda a, b: a - quotient(a, b) * b,
    "&": operator.and_,
    "|": operator.or_,
    "^": operator.xor,
    "<<": operator.lshift,
    ">>": operator.rshift,
}
COMPARE = {
    "<": operator.lt,
    ">": operator.gt,
    "<=": operator.le,
    ">=": operator.ge,
    "==": operator.eq,
    "!=": operator.ne,
}


class IntegerLowering:
    def cast_bits(self, v, bits):
        if v.constant is not None:
            return str(v.constant)
        old = width(v.type)
        if old == bits:
            return v.ir
        cast = "trunc" if old > bits else "sext" if v.type[0] == "i" else "zext"
        return self.temp(f"{cast} i{old} {v.ir} to i{bits}")

    def convert(self, v, typ, tok):
        if v.type == typ and typ != "void":
            if typ.endswith("]") and v.address:
                element = typ.split("[")[0]
                if element.startswith("const<") and element.endswith(">"):
                    element = element[6:-1]
                if record(element):
                    self.special(
                        element,
                        "move_constructor" if v.expiring else "copy_constructor",
                        tok,
                    )
                return replace(v, address="", temporary="", expiring=False)
            if record(typ) and v.address:
                self.special(
                    typ, "move_constructor" if v.expiring else "copy_constructor", tok
                )
                return self.value_tables(
                    replace(v, address="", temporary="", expiring=False)
                )
            return v
        if typ.endswith("*") and v.type == "nullptr_t":
            return Value(typ, "null")
        if self.module.weakens_noexcept(v.type, typ):
            return replace(v, type=typ)
        conversion = self.base_pointer_path(v.type, typ)
        if conversion:
            return self.upcast_pointer(v, typ, conversion)
        if (
            typ.startswith("const<")
            and typ.endswith(">*")
            and typ[6:-2] + "*" == v.type
        ):
            return replace(v, type=typ)
        if (
            enum_type(typ)
            or enum_type(v.type)
            or typ.endswith("]")
            or v.type.endswith("]")
            or handle(typ)
            or handle(v.type)
            or record(typ)
            or record(v.type)
        ):
            raise Error(tok, f"cannot convert {v.type} to {typ}")
        if v.type in ("char", "bool", "void") or typ in ("char", "bool", "void"):
            raise Error(tok, f"cannot convert {v.type} to {typ}")
        lo, hi = bounds(typ)
        if v.constant is not None:
            if lo <= v.constant <= hi:
                return literal(v.constant, typ)
            raise Error(tok, f"{v.constant} is outside the range of {typ}")
        a, b = bounds(v.type)
        if a < lo or b > hi or (("size" in typ) != ("size" in v.type)):
            raise Error(tok, f"no implicit lossless conversion from {v.type} to {typ}")
        return Value(typ, self.cast_bits(v, width(typ)))

    def compare(self, op, a, b, tok):
        if a.type in ("bool", "char") or b.type in ("bool", "char"):
            if a.type != b.type or op not in ("==", "!="):
                raise NoOperation(tok, "invalid Boolean comparison")
        elif "integer" not in (a.type, b.type) and (
            ("size" in a.type or "size" in b.type) and a.type != b.type
        ):
            raise Error(tok, "comparison requires the same integer family")
        if a.constant is not None and b.constant is not None:
            return literal(int(COMPARE[op](a.constant, b.constant)), "bool")
        # Compare in a signed domain wide enough to hold both mathematical values.
        # Out-of-domain abstract literals never need a giant LLVM integer type.
        if a.type == "integer" or b.type == "integer":
            scalar, abstract = (b, a) if a.type == "integer" else (a, b)
            lo, hi = bounds(scalar.type)
            if not lo <= abstract.constant <= hi:
                x, y = (
                    (abstract.constant, lo)
                    if a is abstract
                    else (lo, abstract.constant)
                )
                return literal(int(COMPARE[op](x, y)), "bool")
            abstract = literal(abstract.constant, scalar.type)
            a, b = (abstract, scalar) if a.type == "integer" else (scalar, abstract)
        bits = max(width(a.type), width(b.type)) + 1
        left, right = self.cast_bits(a, bits), self.cast_bits(b, bits)
        pred = {
            "==": "eq",
            "!=": "ne",
            "<": "slt",
            "<=": "sle",
            ">": "sgt",
            ">=": "sge",
        }[op]
        return Value("bool", self.temp(f"icmp {pred} i{bits} {left}, {right}"))

    def arithmetic(self, op, a, b, tok, expected=None):
        if handle(a.type) or handle(b.type):
            if op not in ("==", "!=") or "storage" in (a.type, b.type):
                raise NoOperation(tok, "unsupported pointer operation")
            if a.type == b.type == "nullptr_t":
                return literal(int(op == "=="), "bool")
            if a.type == "nullptr_t":
                a = self.convert(a, b.type, tok)
            if b.type == "nullptr_t":
                b = self.convert(b, a.type, tok)
            if a.type != b.type or not a.type.endswith("*"):
                raise NoOperation(tok, "incompatible pointer comparison")
            pred = "eq" if op == "==" else "ne"
            return Value("bool", self.temp(f"icmp {pred} ptr {a.ir}, {b.ir}"))
        if enum_type(a.type) or enum_type(b.type):
            if a.type != b.type or op not in ("==", "!="):
                raise NoOperation(tok, "enum equality requires matching enum types")
            if a.constant is not None and b.constant is not None:
                return literal(int(COMPARE[op](a.constant, b.constant)), "bool")
            pred = "eq" if op == "==" else "ne"
            return Value(
                "bool", self.temp(f"icmp {pred} {irtype(a.type)} {a.ir}, {b.ir}")
            )
        if (
            a.type.endswith("]")
            or b.type.endswith("]")
            or record(a.type)
            or record(b.type)
        ):
            raise NoOperation(tok, "record has no declared operator")
        if "void" in (a.type, b.type):
            raise Error(tok, "void expression has no value")
        if op in COMPARE:
            return self.compare(op, a, b, tok)
        if a.type in ("bool", "char") or b.type in ("bool", "char"):
            raise NoOperation(tok, "integer operands required")
        abstract = a.type == b.type == "integer"
        if op in ("/", "%") and b.constant == 0 and self.evaluated:
            raise Error(tok, "evaluated integer division by zero")
        if abstract and op in "+-*/%":
            if op in ("/", "%") and b.constant == 0:
                return literal(0)  # statically unselected operand
            return literal(OPS[op](a.constant, b.constant))
        default = (
            expected
            if expected and expected not in ("bool", "void")
            else self.default_int
        )
        if op in ("<<", ">>"):
            typ = default if a.type == "integer" else a.type
            a = self.convert(a, typ, tok)
            return self.shift(op, a, b, tok)
        if a.type == "integer":
            a = self.convert(a, default if abstract else b.type, tok)
        if b.type == "integer":
            b = self.convert(b, a.type, tok)
        if op in ("&", "|", "^") and a.type != b.type:
            raise Error(tok, "bitwise operands require identical integer types")
        typ = common(a.type, b.type, tok)
        self.module.bind_type(typ, self.types, tok)
        a, b = self.convert(a, typ, tok), self.convert(b, typ, tok)
        bits = width(typ)
        policy = self.policy
        if a.constant is not None and b.constant is not None:
            if op not in ("/", "%") or b.constant:
                z = OPS[op](a.constant, b.constant)
                lo, hi = bounds(typ)
                exceptional = op in ("/", "%") and a.constant == lo and b.constant == -1
                if exceptional and policy == "native":
                    self.guard("true")
                if not lo <= z <= hi and policy == "checked":
                    self.guard("true")
                z = (
                    min(max(z, lo), hi)
                    if policy == "saturating"
                    else (z - lo) % (1 << bits) + lo
                )
                return literal(z, typ)
        if op in ("/", "%"):
            signed = typ[0] == "i"
            zero = self.temp(f"icmp eq i{bits} {b.ir}, 0")
            self.guard(zero)
            if signed and policy == "native":
                low = self.temp(f"icmp eq i{bits} {a.ir}, {bounds(typ)[0]}")
                neg = self.temp(f"icmp eq i{bits} {b.ir}, -1")
                self.guard(self.temp(f"and i1 {low}, {neg}"))
            opcode = ("s" if signed else "u") + ("div" if op == "/" else "rem")
            # One extra bit also makes MIN / -1 and MIN % -1 defined in LLVM.
            wide = bits + 1 if signed else bits
            x, y = self.cast_bits(a, wide), self.cast_bits(b, wide)
            z = self.temp(f"{opcode} i{wide} {x}, {y}")
            return self.project(z, wide, typ)
        opcode = {
            "+": "add",
            "-": "sub",
            "*": "mul",
            "&": "and",
            "|": "or",
            "^": "xor",
        }[op]
        wide = bits
        if op in ("+", "-", "*") and policy in ("checked", "saturating"):
            wide = 2 * bits + 1
        x, y = self.cast_bits(a, wide), self.cast_bits(b, wide)
        result = self.temp(f"{opcode} i{wide} {x}, {y}")
        return self.project(result, wide, typ)

    def project(self, result, wide, typ):
        bits = width(typ)
        if wide == bits:
            return Value(typ, result)
        if self.policy in ("checked", "saturating"):
            lo, hi = bounds(typ)
            below = self.temp(f"icmp slt i{wide} {result}, {lo}")
            above = self.temp(f"icmp sgt i{wide} {result}, {hi}")
            if self.policy == "checked":
                self.guard(self.temp(f"or i1 {below}, {above}"))
            else:
                result = self.temp(f"select i1 {below}, i{wide} {lo}, i{wide} {result}")
                result = self.temp(f"select i1 {above}, i{wide} {hi}, i{wide} {result}")
        return Value(typ, self.temp(f"trunc i{wide} {result} to i{bits}"))

    def shift(self, op, a, b, tok):
        n = width(a.type)
        if b.constant is not None:
            if not 0 <= b.constant < n:
                raise Error(tok, f"shift count must be in [0, {n})")
        else:
            bad = self.temp(f"icmp uge {irtype(b.type)} {b.ir}, {n}")
            self.guard(bad)
        if a.constant is not None and b.constant is not None:
            z = OPS[op](a.constant, b.constant)
            lo, hi = bounds(a.type)
            if not lo <= z <= hi and self.policy == "checked":
                self.guard("true")
            z = (
                min(max(z, lo), hi)
                if self.policy == "saturating"
                else (z - lo) % (1 << n) + lo
            )
            return literal(z, a.type)
        wide = (
            2 * n + 1 if op == "<<" and self.policy in ("checked", "saturating") else n
        )
        x, k = self.cast_bits(a, wide), self.cast_bits(b, wide)
        opcode = "shl" if op == "<<" else "ashr" if a.type[0] == "i" else "lshr"
        return self.project(self.temp(f"{opcode} i{wide} {x}, {k}"), wide, a.type)
