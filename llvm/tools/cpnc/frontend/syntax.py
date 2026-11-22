"""CPN26 source profiles and recursive-descent grammar (chapters 12 and 15)."""

from dataclasses import dataclass
import re

from identifiers import admitted, nfc


class Error(Exception):
    def __init__(self, token, message):
        super().__init__(f"{token.line}:{token.column}: ERROR: {message}")


class NoOperation(Error):
    """An operation is absent or inapplicable for the bound operand types."""


@dataclass(frozen=True)
class Token:
    text: str
    line: int
    column: int


TYPES = {"bool", "char", "byte", "nullptr_t", "void", "isize", "usize"} | {
    sign + str(width) for sign in "iu" for width in (8, 16, 32, 64)
}
RESERVED = set(
    """
    alias alignof associated async auto await break case catch
    class cleanup configuration configured const consteval constexpr constraint
    continue declaration decltype declare default define delegate delete derive derive_access destruction_owner do else
    emit enum export extern fallthrough false for forward function generate
    generic goto if import init match meta_grant module mutable namespace noexcept nullptr operator
    partial_typefn private protected public quote reflect_decl reflect_expr reflect_type requires return satisfy sizeof specialize splice_expr splice_name splice_type
    static struct switch this thread_local throw true try typefn union virtual
    while
""".split()
)
INTEGER = re.compile(
    r"(?:[0-9](?:_?[0-9])*|0[xX][0-9a-fA-F](?:_?[0-9a-fA-F])*|"
    r"0[bB][01](?:_?[01])*|0[oO][0-7](?:_?[0-7])*)"
)
LEX = re.compile(
    r"[ \t\f\v\n]+|//[^\n]*|/\*|[a-zA-Z_][a-zA-Z_0-9]*|[0-9][a-zA-Z_0-9]*|"
    r'"[^"\n]*"|\.\.\.|<<=|>>=|::|->|\+\+|--|&&|\|\||<<|>>|[!=<>+*/%&^|\-]=|.'
)


def quoted_text(token):
    text = token.text[1:-1]
    parts = []
    pos = 0
    escapes = {"n": 10, "r": 13, "t": 9, "0": 0, "'": 39, '"': 34, chr(92): 92}
    while pos < len(text):
        ch = text[pos]
        pos += 1
        if ch != chr(92):
            parts.append(ch)
        elif pos < len(text) and text[pos] in escapes:
            parts.append(chr(escapes[text[pos]]))
            pos += 1
        else:
            m = re.match(r"u\{([0-9a-fA-F]{1,6})\}", text[pos:])
            if not m:
                raise Error(token, "invalid escape sequence")
            cp = int(m[1], 16)
            if cp > 0x10FFFF or 0xD800 <= cp <= 0xDFFF:
                raise Error(token, "escape does not denote a Unicode scalar")
            parts.append(chr(cp))
            pos += m.end()
    return "".join(parts)


def integer_value(token):
    digits = token.text.replace("_", "")
    try:
        return int(digits, 0 if digits[:2].lower() in ("0x", "0o", "0b") else 10)
    except ValueError:
        raise Error(token, "integer literal exceeds compiler resource limit") from None


def identifier(word):
    return admitted(word[0], first=True) and all(admitted(ch) for ch in word[1:])


def tokens(source, profile, warn):
    pos, line, col = 0, 1, 1
    while pos < len(source):
        word = LEX.match(source, pos).group()
        tok = Token(word, line, col)
        if admitted(word[0], first=True) or word[0] in "0123456789":
            end = pos + len(word)
            while end < len(source) and admitted(source[end]):
                end += 1
            word = source[pos:end]
            if word[0] in "0123456789":
                if not INTEGER.fullmatch(word):
                    raise Error(tok, "malformed or unsupported numeric literal")
            elif profile == "ascii" and not word.isascii():
                raise Error(tok, "non-ASCII identifier in ASCII source profile")
            canonical = nfc(word)
            if canonical != word:
                warn(tok, "identifier spelling is not NFC")
            yield Token(canonical, line, col)
        elif word[0] in ("'", '"'):
            quote = word[0]
            end = pos + 1
            while end < len(source) and source[end] != quote:
                if source[end] == chr(92):
                    end += 1
                if end >= len(source) or source[end] == chr(10):
                    raise Error(tok, "unterminated quoted literal")
                end += 1
            if end == len(source):
                raise Error(tok, "unterminated quoted literal")
            word = source[pos : end + 1]
            tok = Token(word, line, col)
            decoded = quoted_text(tok)
            if quote == "'" and len(decoded) != 1:
                raise Error(
                    tok, "character literal requires exactly one Unicode scalar"
                )
            yield tok
        elif word == "/*":
            depth = 1
            for marker in COMMENT.finditer(source, pos + 2):
                depth += 1 if marker.group() == "/*" else -1
                if depth == 0:
                    word = source[pos : marker.end()]
                    break
            else:
                raise Error(tok, "unterminated block comment")
        elif word[0] not in " \t\f\v\n" and not word.startswith("//"):
            if word[0].isascii() and word[0].isdigit() and not INTEGER.fullmatch(word):
                raise Error(tok, "malformed or unsupported numeric literal")
            yield tok
        pos += len(word)
        line += word.count("\n")
        col = len(word) - word.rfind("\n") if "\n" in word else col + len(word)
    yield Token("<end>", line, col)


COMMENT = re.compile(r"/\*|\*/")
ASSIGN = "= += -= *= /= %= <<= >>= &= ^= |=".split()
BINDING = {
    op: level
    for level, group in enumerate(
        [
            ASSIGN,
            ["?"],
            ["||"],
            ["&&"],
            ["|"],
            ["^"],
            ["&"],
            ["==", "!="],
            ["<", "<=", ">", ">="],
            ["<<", ">>"],
            ["+", "-"],
            ["*", "/", "%"],
        ],
        start=1,
    )
    for op in group
}


@dataclass(frozen=True)
class Node:
    token: Token
    kind: str
    args: tuple = ()


@dataclass(frozen=True)
class GenericParameter:
    kind: str
    name: str
    default: object = None
    pack: bool = False


@dataclass(frozen=True)
class Parameter:
    type: str
    name: Token | None
    readonly: bool
    default: tuple | None
    expansion: bool = False
    forwarding: bool = False


@dataclass(frozen=True)
class CallableType:
    result: str
    params: tuple
    noexcept: bool


@dataclass
class Function:
    name: Token
    result: str
    params: list
    body: object
    foreign: bool
    generics: list
    noexcept: bool = False
    mode: str = ""
    requirement: Node | None = None
    receiver_category: str = ""
    virtual: bool = False
    override: bool = False
    final: bool = False


class Parser:
    def __init__(self, source, profile, warn):
        self.stream = list(tokens(source, profile, warn))
        self.index = 0
        self.types = set(TYPES)
        self.function_families = {
            name: [GenericParameter("type", "T")]
            for name in ("construct_at", "destroy_base", "abandon_base", "std::forward")
        }
        one_type = [GenericParameter("type", "T")]
        self.predicates = {
            name: one_type
            for name in (
                "ObjectType",
                "CompleteType",
                "CopyConstructible",
                "MoveConstructible",
            )
        }
        self.predicates["SameType"] = one_type + [GenericParameter("type", "U")]
        self.record_families = {}
        self.type_expressions = {}
        self.callable_types = {}
        self.namespace = ""
        self.tags = {}

    @property
    def here(self):
        return self.stream[self.index]

    def take(self):
        t = self.here
        if t.text == "<end>":
            raise Error(t, "unexpected end of file")
        self.index += 1
        return t

    def eat(self, text):
        if self.here.text == text:
            self.take()
            return True
        return False

    def expect(self, text):
        if not self.eat(text):
            raise Error(self.here, f"expected '{text}', found '{self.here.text}'")

    def name(self):
        t = self.take()
        if not identifier(t.text) or t.text in RESERVED or t.text in self.types:
            raise Error(t, "expected an identifier")
        return t

    def tag_name(self, kind, defining):
        key = self.namespace + self.here.text
        old = self.tags.get(key)
        if old:
            t = self.take()
            if old[0] != kind or (old[1] and defining):
                raise Error(t, "conflicting nominal type declaration")
        else:
            t = self.name()
        self.tags[key] = (kind, defining or bool(old and old[1]))
        self.types.add(t.text)
        return t

    def typename(self):
        t = self.take()
        if identifier(t.text):
            while self.eat("::"):
                member = self.take()
                if not identifier(member.text) or member.text in RESERVED:
                    raise Error(member, "expected qualified type name")
                t = Token(t.text + "::" + member.text, t.line, t.column)
        if t.text == "function":
            self.expect("<")
            result = self.typename()
            self.expect("(")
            params = self.parameters(allow_defaults=False)
            noexcept = self.eat("noexcept")
            self.close_generic()
            typ = f"$function{len(self.callable_types)}"
            self.callable_types[typ] = CallableType(
                result, tuple(p.type for p in params), noexcept
            )
        elif t.text == "(":
            typ = self.typename()
            self.expect(")")
        elif t.text == "const":
            self.expect("<")
            typ = "const<" + self.typename() + ">"
            self.close_generic()
        else:
            if t.text not in self.types and not (
                "::" in t.text and t.text.partition("::")[0] in self.types
            ):
                raise Error(t, f"unsupported or unknown type '{t.text}'")
            typ = t.text
        if typ in self.record_families:
            typ = self.record_application(t)
        while self.here.text in ("*", "&", "&&", "["):
            if self.eat("["):
                count = self.type_expression(self.expr())
                self.expect("]")
                typ += "[" + count + "]"
            else:
                typ += self.take().text
        return typ

    def function_body_follows(self, member=True):
        if self.here.text != "(":
            return False
        j, depth = self.index + 1, 1
        while depth and j < len(self.stream):
            word = self.stream[j].text
            depth += (word == "(") - (word == ")")
            j += 1
        if member and j < len(self.stream) and self.stream[j].text == "const":
            j += 1
        if member and j < len(self.stream) and self.stream[j].text in ("&", "&&"):
            j += 1
        if j < len(self.stream) and self.stream[j].text == "noexcept":
            j += 1
        for suffix in ("override", "final"):
            if member and j < len(self.stream) and self.stream[j].text == suffix:
                j += 1
        return j < len(self.stream) and self.stream[j].text == "{"

    def close_generic(self):
        if self.here.text == ">>":
            t = self.here
            self.stream[self.index] = Token(">", t.line, t.column + 1)
        else:
            self.expect(">")

    def type_expression(self, node):
        # Type spellings retain the AST until the enclosing use is bound.
        if node.kind == "integer":
            return str(integer_value(node.token))
        key = f"$expr{len(self.type_expressions)}"
        self.type_expressions[key] = node
        return key

    def generic_arguments(self, parameters):
        self.expect("<")
        args = []
        if self.here.text not in (">", ">>"):
            while True:
                if len(args) >= len(parameters) and not parameters[-1].pack:
                    raise Error(self.here, "too many generic arguments")
                kind = parameters[min(len(args), len(parameters) - 1)].kind
                arg = self.typename() if kind == "type" else self.expr(generic=True)
                args.append(self.expansion(arg))
                if not self.eat(","):
                    break
        self.close_generic()
        return args

    def record_application(self, t):
        params = self.record_families[t.text]
        args = self.generic_arguments(params)
        actual = []
        for arg in args:
            expand = isinstance(arg, Node) and arg.kind == "expand"
            value = arg.args[0] if expand else arg
            word = self.type_expression(value) if isinstance(value, Node) else value
            actual.append(word + ("..." if expand else ""))
        return t.text + "<" + ",".join(actual) + ">"

    def special_control(self, owner, ops, params, role, public):
        key = None
        if not params and role == "constructor":
            key = "default"
        elif len(params) == 1:
            typ, qualified = params[0].type, params[0].readonly
            if (
                typ == "const<" + owner.text + ">&"
                or qualified
                and typ == owner.text + "&"
            ):
                key = "copy_" + role
            elif not qualified and typ == owner.text + "&&":
                key = "move_" + role
        if not key:
            raise Error(owner, "unsupported special-member signature")
        control = self.take()
        if control.text not in ("default", "delete") or key in ops:
            raise Error(control, "invalid or duplicate special-member definition")
        self.expect(";")
        ops[key] = (control.text, public)

    def initialization_target(self):
        t = self.here
        if t.text == "base" and self.stream[self.index + 1].text == "<":
            self.take()
            self.expect("<")
            base = self.typename()
            self.close_generic()
            return Token("$base:" + base, t.line, t.column)
        return self.name()

    def parameters(self, allow_defaults=True):
        params = []
        if not self.eat(")"):
            while True:
                const = (
                    self.here.text == "const"
                    and self.stream[self.index + 1].text != "<"
                    and self.eat("const")
                )
                forwarding = self.eat("forward")
                ptype = self.typename()
                expansion = self.eat("...")
                if const and ptype.endswith("&"):
                    base = ptype.rstrip("&")
                    ptype = f"const<{base}>" + ptype[len(base) :]
                elif ptype.startswith("const<") and ptype.endswith(">"):
                    ptype, const = ptype[6:-1], True
                pname = self.name() if self.here.text not in (",", ")", "(") else None
                default = None
                if self.eat("("):
                    if not allow_defaults:
                        raise Error(
                            self.here,
                            "function type cannot contain a parameter default",
                        )
                    default = self.arguments()
                elif params and params[-1].default is not None:
                    raise Error(
                        self.here, "parameter defaults must form a trailing suffix"
                    )
                if expansion and default is not None:
                    raise Error(
                        pname or self.here, "parameter expansion cannot have a default"
                    )
                if not allow_defaults and forwarding:
                    raise Error(
                        pname or self.here,
                        "forward requires a generic function parameter",
                    )
                params.append(
                    Parameter(ptype, pname, const, default, expansion, forwarding)
                )
                if not self.eat(","):
                    break
            self.expect(")")
        return params

    def expansion(self, pattern):
        if self.here.text == "...":
            return Node(self.take(), "expand", (pattern,))
        return pattern

    def arguments(self):
        items = []
        if not self.eat(")"):
            while True:
                items.append(self.expansion(self.expr()))
                if not self.eat(","):
                    break
            self.expect(")")
        return tuple(items)

    def expr(self, minimum=1, *, generic=False):
        t = self.take()
        if t.text in ("+", "-", "!", "~", "++", "--", "*", "&"):
            lhs = Node(t, "prefix", (self.expr(13, generic=generic),))
        elif t.text == "(":
            lhs = Node(t, "group", (self.expr(),))
            self.expect(")")
        elif INTEGER.fullmatch(t.text):
            lhs = Node(t, "integer")
        elif t.text in ("sizeof", "alignof"):
            self.expect("(")
            if self.here.text in self.types or self.here.text in ("const", "function"):
                operand = self.typename()
            elif t.text == "sizeof":
                operand = self.expr()
            else:
                raise Error(t, "alignof requires a type")
            self.expect(")")
            lhs = Node(t, "layout", (operand,))
        elif t.text == "configured":
            pairs = self.bindings()
            self.expect("(")
            lhs = Node(t, "configured_expr", (pairs, self.expr()))
            self.expect(")")
        elif t.text == "this":
            lhs = Node(t, "name")
        elif t.text == "nullptr":
            lhs = Node(t, "nullptr")
        elif t.text.startswith('"'):
            lhs = Node(t, "string")
        elif t.text.startswith("'"):
            lhs = Node(t, "char")
        elif t.text in ("true", "false"):
            lhs = Node(t, "bool")
        elif identifier(t.text) and t.text not in RESERVED:
            while self.eat("::"):
                member = (
                    self.take()
                    if t.text == "std" and self.here.text == "forward"
                    else self.name()
                )
                t = Token(t.text + "::" + member.text, t.line, t.column)
            generic_args = []
            if t.text in self.record_families:
                t = Token(self.record_application(t), t.line, t.column)
            if t.text in self.function_families and self.here.text == "<":
                generic_args = self.generic_arguments(self.function_families[t.text])
            if t.text in self.predicates and self.here.text == "<":
                predicate_args = self.generic_arguments(self.predicates[t.text])
                lhs = Node(t, "predicate", (tuple(predicate_args),))
            elif self.eat("("):
                lhs = Node(t, "call", (tuple(generic_args), self.arguments()))
            elif generic_args:
                raise Error(t, "expected a call after generic arguments")
            else:
                lhs = Node(t, "name")
        else:
            raise Error(t, f"expected expression, found '{t.text}'")
        while self.here.text in (".", "->", "[", "(", "++", "--"):
            if self.eat("("):
                if lhs.kind == "member":
                    lhs = Node(lhs.token, "method", (lhs.args[0], self.arguments()))
                else:
                    lhs = Node(lhs.token, "invoke", (lhs, self.arguments()))
                continue
            if self.here.text == "[":
                bracket = self.take()
                lhs = Node(bracket, "index", (lhs, self.expr()))
                self.expect("]")
                continue
            if self.here.text == "->":
                arrow = self.take()
                if (
                    self.here.text in self.types
                    and self.stream[self.index + 1].text == "::"
                    and self.stream[self.index + 2].text == "~"
                ):
                    base = self.take()
                    self.expect("::")
                    self.expect("~")
                    self.expect(base.text)
                    self.expect("(")
                    self.expect(")")
                    lhs = Node(
                        Token("destroy_base", arrow.line, arrow.column),
                        "call",
                        ((base.text,), (lhs,)),
                    )
                    continue
                ptr = Node(Token("*", arrow.line, arrow.column), "prefix", (lhs,))
                lhs = Node(self.name(), "member", (ptr,))
            elif self.eat("."):
                lhs = Node(self.name(), "member", (lhs,))
            else:
                lhs = Node(self.take(), "postfix", (lhs,))
        while BINDING.get(self.here.text, 0) >= minimum:
            if generic and self.here.text in (">", ">>"):
                break
            op = self.take()
            power = BINDING[op.text]
            if op.text == "?":
                yes = self.expr(generic=generic)
                self.expect(":")
                lhs = Node(op, "conditional", (lhs, yes, self.expr(generic=generic)))
            else:
                rhs = self.expr(
                    power if op.text in ASSIGN else power + 1, generic=generic
                )
                lhs = Node(op, "binary", (lhs, rhs))
        return lhs

    def block(self):
        t = self.here
        self.expect("{")
        body = []
        while not self.eat("}"):
            body.append(self.statement())
        return Node(t, "block", tuple(body))

    def condition(self):
        self.expect("(")
        e = self.expr()
        self.expect(")")
        return e

    def object_decl(self, t, qualifier, typ, name):
        values = self.arguments() if self.eat("(") else ()
        if typ == "auto" and len(values) != 1:
            raise Error(t, "invalid scalar initializer")
        self.expect(";")
        return Node(t, "object", (qualifier, typ, name, values))

    def simple(self):
        t = self.here
        if self.eat(";"):
            return Node(t, "empty")
        q = (
            self.take().text
            if t.text in ("const", "constexpr")
            and self.stream[self.index + 1].text != "<"
            else ""
        )
        pos = self.index
        qualified = self.here.text
        while pos + 2 < len(self.stream) and self.stream[pos + 1].text == "::":
            qualified += "::" + self.stream[pos + 2].text
            pos += 2
        if (
            q
            or self.here.text in ("auto", "const", "function")
            or (qualified in self.types and self.stream[pos + 1].text != "(")
        ):
            typ = "auto" if self.eat("auto") else self.typename()
            return self.object_decl(t, q, typ, self.name())
        value = self.expr()
        self.expect(";")
        return Node(t, "expr", (value,))

    def statement(self):
        t = self.here
        if self.eat("delegate"):
            self.expect("(")
            args = self.arguments()
            self.expect(";")
            return Node(t, "delegate", args)
        if t.text == "{":
            return self.block()
        if (
            identifier(t.text)
            and t.text not in RESERVED
            and self.stream[self.index + 1].text == ":"
        ):
            name = self.name()
            self.expect(":")
            statement = self.statement()
            if statement.kind == "object":
                raise Error(name, "a label requires a statement")
            return Node(name, "label", (statement,))
        if self.eat("goto"):
            label = self.name()
            self.expect(";")
            return Node(t, "goto", (label,))
        if t.text == "configured":
            before = self.index
            self.take()
            pairs = self.bindings()
            if self.here.text == "{":
                return Node(t, "configured_block", (pairs, self.block()))
            if self.here.text != "(":
                decl = self.simple()
                if decl.kind != "object":
                    raise Error(
                        t, "expected configured declaration, block or expression"
                    )
                return Node(t, "configured_block", (pairs, decl))
            self.index = before
        if self.eat("if"):
            kind = "if_constexpr" if self.eat("constexpr") else "if"
            cond, yes = self.condition(), self.block()
            no = None
            if self.eat("else"):
                no = self.statement() if self.here.text == "if" else self.block()
            return Node(t, kind, (cond, yes, no))
        if self.eat("match"):
            subject = self.condition()
            self.expect("{")
            arms = []
            while not self.eat("}"):
                self.expect("case")
                owner = self.take()
                if owner.text == "_":
                    case = None
                else:
                    if owner.text not in self.types:
                        raise Error(owner, "expected a union type")
                    self.expect("::")
                    case = (owner, self.name())
                patterns = []
                if case and self.eat("(") and not self.eat(")"):
                    while True:
                        mode = self.take()
                        if mode.text == "_":
                            patterns.append(("_", None))
                        elif mode.text in ("value", "ref", "move"):
                            patterns.append((mode.text, self.name()))
                        else:
                            raise Error(mode, "invalid payload pattern")
                        if not self.eat(","):
                            break
                    self.expect(")")
                arms.append((case, patterns, self.block()))
            return Node(t, "match", (subject, arms))
        if self.eat("switch"):
            value = self.condition()
            self.expect("{")
            arms = []
            while not self.eat("}"):
                if self.eat("case"):
                    case = self.expr()
                else:
                    self.expect("default")
                    case = None
                self.expect(":")
                arms.append((case, self.block()))
            return Node(t, "switch", (value, tuple(arms)))
        if self.eat("fallthrough"):
            self.expect(";")
            return Node(t, "fallthrough")
        if self.eat("while"):
            return Node(t, "while", (self.condition(), self.block()))
        if self.eat("do"):
            body = self.block()
            self.expect("while")
            cond = self.condition()
            self.expect(";")
            return Node(t, "do", (cond, body))
        if self.eat("for"):
            self.expect("(")
            init = self.simple()
            cond = None if self.here.text == ";" else self.expr()
            self.expect(";")
            step = None if self.here.text == ")" else self.expr()
            self.expect(")")
            return Node(t, "for", (init, cond, step, self.block()))
        if self.eat("return"):
            value = None if self.here.text == ";" else self.expr()
            self.expect(";")
            return Node(t, "return", (value,))
        if self.eat("break") or self.eat("continue"):
            target = None if self.here.text == ";" else self.name()
            self.expect(";")
            return Node(t, t.text, (target,))
        return self.simple()

    def bindings(self):
        self.expect("(")
        if self.here.text == ")":
            raise Error(self.here, "empty configured prefix")
        return self.binding_list(")", ",")

    def binding_list(self, end, sep):
        pairs = {}
        while not self.eat(end):
            t = self.take()
            if not identifier(t.text):
                raise Error(t, "invalid configuration key")
            key = t.text
            while self.eat("."):
                member = self.take()
                if not identifier(member.text):
                    raise Error(member, "invalid configuration path")
                key += "." + member.text
            self.expect("=")
            if key in pairs:
                raise Error(t, f"duplicate configuration key '{key}'")
            pairs[key] = self.config_value()
            if sep == "," and self.eat(end):
                break
            self.expect(sep)
            if sep == "," and self.here.text == end:
                raise Error(self.here, "trailing configuration separator")
        return pairs

    def config_value(self):
        if self.eat("["):
            values = []
            if not self.eat("]"):
                while True:
                    values.append(self.config_value())
                    if not self.eat(","):
                        break
                self.expect("]")
            return values
        t = self.take()
        if INTEGER.fullmatch(t.text):
            return str(integer_value(t))
        if t.text.startswith('"') or identifier(t.text):
            return t.text
        raise Error(t, "invalid configuration value")

    def unit(self):
        while self.here.text != "<end>":
            yield from self.item()

    def generic_parameters(self):
        generic = []
        self.expect("<")
        while True:
            if self.eat("type"):
                kind = "type"
            else:
                self.expect("const")
                kind = self.typename()
            pack = self.eat("...")
            p = self.name()
            if any(p.text == param.name for param in generic):
                raise Error(p, "duplicate generic parameter")
            default = None
            if self.eat("="):
                if pack:
                    raise Error(p, "generic pack cannot have a default")
                default = self.typename() if kind == "type" else self.expr(generic=True)
            generic.append(GenericParameter(kind, p.text, default, pack))
            if kind == "type":
                self.types.add(p.text)
            if not self.eat(","):
                break
            if pack:
                raise Error(p, "generic pack must be the last parameter")
        self.close_generic()
        return generic

    def expression_requirement(self):
        # Chapter 15 assigns the last top-level arrow to the result type.
        depth, end, separator = 0, self.index, None
        while end < len(self.stream):
            text = self.stream[end].text
            if depth == 0:
                if text in (";", "}", "<end>"):
                    break
                if text == "->":
                    separator = end
            depth += (text in ("(", "[")) - (text in (")", "]"))
            end += 1
        if separator is None:
            raise Error(self.here, "expression requirement needs a result type")
        t = self.stream[separator]
        self.stream[separator] = Token("$result", t.line, t.column)
        expr = self.expr()
        self.expect("$result")
        result = self.typename()
        noexcept = self.eat("noexcept")
        self.expect(";")
        return expr, result, noexcept

    def constraint(self):
        name = self.name()
        old_types = self.types.copy()
        params = self.generic_parameters()
        self.expect("{")
        items = []
        while not self.eat("}"):
            if self.eat("requires"):
                items.append(("predicate", self.condition()))
                self.expect(";")
            elif self.eat("type"):
                items.append(("type", self.typename()))
                self.expect(";")
            else:
                self.expect("expression")
                self.expect("(")
                formals = self.parameters(allow_defaults=False)
                self.expect("{")
                expressions = []
                while not self.eat("}"):
                    expressions.append(self.expression_requirement())
                items.append(("expression", formals, expressions))
        self.expect(";")
        self.types = old_types
        if name.text in self.predicates:
            raise Error(name, "duplicate constraint")
        self.predicates[name.text] = params
        return Node(name, "constraint", (params, items))

    def item(self, foreign_scope=False):
        if self.here.text == "[":
            attributes = {}
            start = self.here
            while self.eat("["):
                self.expect("[")
                while True:
                    attr = self.name()
                    if attr.text not in ("static_id", "init_after"):
                        raise Error(attr, "unsupported declaration attribute")
                    if attr.text in attributes:
                        raise Error(attr, "duplicate declaration attribute")
                    self.expect("(")
                    if attr.text == "static_id":
                        value = self.take()
                        if not value.text.startswith('"'):
                            raise Error(value, "static_id requires one string literal")
                        attributes[attr.text] = quoted_text(value)
                    else:
                        names = []
                        while True:
                            root = self.eat("::")
                            components = [self.name().text]
                            while self.eat("::"):
                                components.append(self.name().text)
                            names.append(("::" if root else "") + "::".join(components))
                            if not self.eat(","):
                                break
                        attributes[attr.text] = tuple(names)
                    self.expect(")")
                    if not self.eat(","):
                        break
                self.expect("]")
                self.expect("]")
            declarations = tuple(self.item(foreign_scope))
            if (
                len(declarations) != 1
                or not isinstance(declarations[0], Node)
                or declarations[0].kind != "object"
            ):
                raise Error(
                    start, "static object attribute requires a static object definition"
                )
            yield Node(start, "static_attributes", (attributes, declarations[0]))
            return
        if self.here.text == "configured":
            t = self.take()
            pairs = self.bindings()
            yield Node(t, "configured_decl", (pairs, tuple(self.item(foreign_scope))))
            return
        if self.eat("constraint"):
            yield self.constraint()
            return
        if self.eat("namespace"):
            name = self.name()
            self.expect("{")
            original = self.types.copy()
            prefix = name.text + "::"
            previous_namespace = self.namespace
            self.namespace += prefix
            self.types.update(
                t[len(prefix) :] for t in original if t.startswith(prefix)
            )
            items = []
            while not self.eat("}"):
                if self.here.text == "configuration":
                    raise Error(
                        self.here, "configuration declaration outside file scope"
                    )
                items.extend(self.item(foreign_scope))
            self.types = original | {prefix + t for t in self.types - original}
            self.namespace = previous_namespace
            yield Node(name, "namespace", tuple(items))
            return
        t = self.here
        if t.text == "declare" and self.stream[self.index + 1].text in (
            "struct",
            "class",
            "union",
            "enum",
        ):
            self.take()
            kind = self.take().text
            name = self.tag_name(kind, defining=False)
            underlying = None
            if kind == "enum":
                self.expect(":")
                underlying = self.typename()
            self.expect(";")
            yield Node(name, "incomplete", (kind, underlying))
            return
        if self.eat("configuration"):
            self.expect("{")
            pairs = self.binding_list("}", ";")
            self.expect(";")
            yield Node(t, "config", (pairs,))
            return
        if self.eat("union"):
            name = self.tag_name("union", defining=True)
            self.expect("{")
            cases = []
            while not self.eat("}"):
                default = self.eat("default")
                self.expect("case")
                case = self.name()
                fields = []
                if self.eat("("):
                    while True:
                        fields.append((self.typename(), self.name()))
                        if not self.eat(","):
                            break
                    self.expect(")")
                self.expect(";")
                cases.append((case, default, fields))
            self.expect(";")
            self.types.add(name.text)
            yield Node(name, "union", tuple(cases))
            return
        if self.eat("enum"):
            name = self.tag_name("enum", defining=True)
            self.expect(":")
            underlying = self.typename()
            self.expect("{")
            cases = []
            while True:
                self.expect("case")
                case = self.name()
                self.expect("(")
                value = self.expr()
                self.expect(")")
                cases.append((case, value))
                if not self.eat(",") or self.here.text == "}":
                    break
            self.expect("}")
            self.expect(";")
            self.types.add(name.text)
            yield Node(name, "enum", (underlying, cases))
            return
        if self.eat("alias"):
            name = self.name()
            self.expect("=")
            target = self.typename()
            self.expect(";")
            self.types.add(name.text)
            yield Node(name, "alias", (target,))
            return
        foreign = foreign_scope
        if self.eat("extern"):
            self.expect('"C"')
            if self.eat("{"):
                while not self.eat("}"):
                    yield from self.item(True)
                return
            foreign = True
        definition = foreign and self.eat("define")
        generic = []
        requirement = None
        old_types = self.types.copy()
        if self.eat("generic"):
            generic = self.generic_parameters()
            if self.eat("requires"):
                requirement = self.condition()
        if self.here.text in ("struct", "class"):
            t = self.take()
            manual_all = (
                t.text == "class"
                and self.here.text == "Manual"
                and self.stream[self.index + 1].text != "{"
                and self.eat("Manual")
            )
            name = self.tag_name(t.text, defining=True)
            if generic:
                self.record_families[name.text] = generic
            final = self.eat("final")
            bases = []
            if self.eat(":"):
                while True:
                    if self.eat("virtual"):
                        raise Error(name, "virtual base layout is unavailable")
                    bases.append(self.typename())
                    if not self.eat(","):
                        break
            self.expect("{")
            fields, ctors, methods = [], [], []
            specials = {}
            manual = set()
            dtor = cleanup = None
            destructor_spec = (False, False, False, False)
            public = t.text == "struct"
            while not self.eat("}"):
                if self.here.text in ("public", "private", "protected"):
                    public = self.take().text == "public"
                    self.expect(":")
                elif (
                    self.here.text == "Complete"
                    and self.stream[self.index + 1].text != "("
                ):
                    marker = self.take()
                    if self.eat(";"):
                        if "*" in manual:
                            raise Error(marker, "duplicate Complete declaration")
                        manual.add("*")
                    else:
                        field = self.initialization_target()
                        if field.text in manual:
                            raise Error(field, "duplicate Complete member")
                        manual.add(field.text)
                        self.expect(";")
                elif self.here.text == "~" or (
                    self.here.text == "virtual"
                    and self.stream[self.index + 1].text == "~"
                ):
                    virtual = self.eat("virtual")
                    self.expect("~")
                    self.expect(name.text)
                    self.expect("(")
                    self.expect(")")
                    if dtor:
                        raise Error(self.here, "duplicate destructor")
                    destructor_spec = (
                        virtual,
                        self.eat("noexcept"),
                        self.eat("override"),
                        self.eat("final"),
                    )
                    dtor = self.block()
                    if self.eat("cleanup"):
                        cleanup = self.block()
                elif (
                    self.here.text == name.text
                    and self.stream[self.index + 1].text == "("
                ):
                    self.take()
                    self.expect("(")
                    params = self.parameters()
                    self.eat("noexcept")
                    if self.eat("="):
                        self.special_control(
                            name, specials, params, "constructor", public
                        )
                        continue
                    self.expect("{")
                    producers, body = {}, []
                    while not self.eat("}"):
                        if self.eat("init"):
                            member = self.initialization_target()
                            self.expect("(")
                            if member.text in producers:
                                raise Error(member, "duplicate initialization producer")
                            producers[member.text] = self.arguments()
                            self.expect(";")
                        else:
                            body.append(self.statement())
                    ctors.append(
                        (params, producers, Node(name, "block", tuple(body)), public)
                    )
                else:
                    virtual = self.eat("virtual")
                    typ = self.typename()
                    if self.eat("operator"):
                        if virtual:
                            raise Error(
                                self.here,
                                "virtual assignment requires an authored slot",
                            )
                        self.expect("=")
                        if typ != name.text + "&":
                            raise Error(
                                name,
                                "assignment must return an lvalue reference to the record",
                            )
                        self.expect("(")
                        params = self.parameters()
                        self.eat("noexcept")
                        self.expect("=")
                        self.special_control(
                            name, specials, params, "assignment", public
                        )
                        continue
                    member = self.name()
                    if self.function_body_follows():
                        self.expect("(")
                        params = self.parameters()
                        readonly = self.eat("const")
                        category = (
                            self.take().text if self.here.text in ("&", "&&") else ""
                        )
                        noexcept = self.eat("noexcept")
                        override, closed = self.eat("override"), self.eat("final")
                        methods.append(
                            (
                                Function(
                                    member,
                                    typ,
                                    params,
                                    self.block(),
                                    False,
                                    [],
                                    noexcept,
                                    receiver_category=category,
                                    virtual=virtual,
                                    override=override,
                                    final=closed,
                                ),
                                readonly,
                                public,
                            )
                        )
                    else:
                        if virtual:
                            raise Error(member, "virtual requires a member function")
                        fields.append(
                            (self.object_decl(member, "", typ, member), public)
                        )
            self.expect(";")
            self.types = old_types | {name.text}
            decl = Node(
                name,
                "record",
                (
                    fields,
                    ctors,
                    dtor,
                    cleanup,
                    methods,
                    specials,
                    manual | ({"$members"} if manual_all else set()),
                    bases,
                    final,
                    destructor_spec,
                ),
            )
            yield (
                Node(name, "record_family", (generic, decl, requirement))
                if generic
                else decl
            )
            return
        proto = self.eat("declare")
        static_object = not proto and not foreign and self.eat("static")
        q = (
            self.take().text
            if self.here.text in ("const", "constexpr", "consteval")
            and self.stream[self.index + 1].text != "<"
            else ""
        )
        typ = "auto" if self.eat("auto") else self.typename()
        name = self.name()
        # Ordinary semicolon-only forms without 'declare' denote objects.
        if foreign and (definition or self.here.text == ";"):
            if proto or generic or typ == "auto" or q == "constexpr":
                raise Error(name, "invalid external object declaration")
            obj = self.object_decl(t, q, typ, name)
            yield Node(name, "foreign_object", (definition, obj))
            return
        is_fn = proto or foreign or bool(generic)
        is_fn = is_fn or self.function_body_follows(member=False)
        if not is_fn:
            if q == "consteval":
                raise Error(t, "consteval requires a function")
            yield self.object_decl(t, q, typ, name)
            return
        if static_object:
            raise Error(t, "static function modifier requires a record member")
        if q == "const" or typ == "auto" or (foreign and (proto or generic)):
            raise Error(t, "unsupported function declaration")
        if generic:
            self.function_families[name.text] = generic
        self.expect("(")
        params = self.parameters()
        noexcept = self.eat("noexcept")
        if proto or (foreign and self.here.text == ";"):
            self.expect(";")
            body = None
        else:
            body = self.block()
        self.types = old_types
        yield Function(
            name, typ, params, body, foreign, generic, noexcept, q, requirement
        )
