"""Non-inheriting record destruction: body, reverse prefix, Cleanup and remainder."""

from syntax import Error, Function
from numeric import Value, irtype, record


def register_array_destruction(module, typ, element, count):
    if typ in module.destructors or not count or element not in module.destructors:
        return
    symbol = f"drop.array.{next(module.ids)}"
    module.destructors[typ] = symbol
    module.ir.append(f"""define internal void @{symbol}(ptr %array) {{
entry:
  br label %element
element:
  %remaining = phi i64 [ {count}, %entry ], [ %index, %element ]
  %index = sub i64 %remaining, 1
  %slot = getelementptr {irtype(typ)}, ptr %array, i64 0, i64 %index
  call void @{module.destructors[element]}(ptr %slot)
  %finished = icmp eq i64 %index, 0
  br i1 %finished, label %done, label %element
done:
  ret void
}}""")


def emit_destruction(module, decl, typ, fields, manual, dtor, cleanup):
    from compiler import Definition, Emitter

    drop = f"drop.{typ}"
    module.destructors[typ] = drop
    coordinator = Emitter(module)
    coordinator.site = decl.token
    coordinator.install_tables(typ, "%self")
    fields = {name: value for name, value in fields.items() if name != "$vtable"}
    live = coordinator.allocate(f"bool[{max(1, len(fields))}]")
    flags = {}
    slots = {}
    for index, (name, v) in enumerate(fields.items()):
        flag = coordinator.temp(f"getelementptr i1, ptr {live}, i32 {index}")
        coordinator.emit(f"store i1 true, ptr {flag}")
        flags[name] = flag
        slots[name] = coordinator.temp(
            f"getelementptr %{typ}, ptr %self, i32 0, i32 {index}"
        )

    def helper(phase, statements):
        if not statements:
            return
        f = Function(decl.token, "void", [], statements, False, [])
        d = Definition(
            f,
            "void",
            (),
            f"{drop}.{phase}",
            module.types.copy(),
            module.names.copy(),
            module.policy,
            module.default_int,
            receiver=typ,
        )
        d.phase = phase
        module.ir.append(Emitter(module, d).function_ir())
        coordinator.emit(f"call void @{d.symbol}(ptr %self, ptr {live})")

    def sweep(name):
        valid = coordinator.temp(f"load i1, ptr {flags[name]}")
        yes, done = coordinator.ident(), coordinator.ident()
        coordinator.emit(f"br i1 {valid}, label %{yes}, label %{done}")
        coordinator.label(yes)
        coordinator.emit(f"store i1 false, ptr {flags[name]}")
        coordinator.drop(fields[name].type, slots[name])
        coordinator.jump(done)
        coordinator.label(done)

    helper("body", dtor)
    barrier = coordinator.ident()
    for name in reversed(fields):
        if name in manual:
            valid = coordinator.temp(f"load i1, ptr {flags[name]}")
            skip = coordinator.ident()
            coordinator.emit(f"br i1 {valid}, label %{barrier}, label %{skip}")
            coordinator.label(skip)
        else:
            sweep(name)
    coordinator.jump(barrier)
    coordinator.label(barrier)
    helper("cleanup", cleanup)
    for name in reversed(fields):
        sweep(name)
    coordinator.emit("ret void")
    module.ir.append(
        "\n".join(
            [
                f"define internal void @{drop}(ptr %self) {{",
                "entry:",
                *coordinator.entry,
                *coordinator.lines,
                "}",
            ]
        )
    )


class MemberLifetime:
    def construct_array(self, typ, args, tok):
        element, length = typ[:-1].rsplit("[", 1)
        count = int(length)
        base = (
            element[6:-1]
            if element.startswith("const<") and element.endswith(">")
            else element
        )
        values = "zeroinitializer"
        for index, arg in enumerate(args):
            value = self.expr(arg, base)
            if len(args) == 1 and value.type == typ:
                return self.convert(value, typ, tok)
            if index >= count:
                raise Error(tok, "too many array initializers")
            value = self.convert(value, base, tok)
            values = self.temp(
                f"insertvalue {irtype(typ)} {values}, {irtype(element)} {value.ir}, {index}"
            )
            self.consume(value)
        if len(args) == count:
            return self.temporary(Value(typ, values))

        # Scalar defaults are canonical zero. Validate the default even when
        # its representation does not need a run-time store (e.g. closed enums).
        if not record(base) and not base.endswith("]"):
            self.zero(base)
            return Value(typ, values)
        destination = self.allocate(typ)
        self.store(Value(typ, values), destination)
        slot = self.allocate("usize")
        self.emit(f"store i64 {len(args)}, ptr {slot}")
        body, done = self.ident(), self.ident()
        self.jump(body)
        self.label(body)
        index = self.temp(f"load i64, ptr {slot}")
        address = self.temp(
            f"getelementptr {irtype(typ)}, ptr {destination}, i64 0, i64 {index}"
        )
        value = self.construct(base, (), tok)
        self.store(value, address)
        self.consume(value)
        next_index = self.temp(f"add i64 {index}, 1")
        self.emit(f"store i64 {next_index}, ptr {slot}")
        finished = self.temp(f"icmp eq i64 {next_index}, {count}")
        self.emit(f"br i1 {finished}, label %{done}, label %{body}")
        self.label(done)
        result = Value(typ, self.temp(f"load {irtype(typ)}, ptr {destination}"))
        return self.temporary(result, destination)

    def field_name(self, node):
        if not self.d or not self.d.phase:
            return None
        if node.kind == "name" and node.token.text in self.field_flags:
            cell = self.lookup(node.token)
            if cell.address == self.field_flags[node.token.text][0]:
                return node.token.text
        if node.kind == "member":
            base = node.args[0]
            if (
                base.kind == "prefix"
                and base.token.text == "*"
                and base.args[0].token.text == "this"
            ):
                return node.token.text
        return None

    def field_live(self, name, tok):
        _, flag = self.field_flags[name]
        valid = self.temp(f"load i1, ptr {flag}")
        self.guard(self.temp(f"xor i1 {valid}, true"))

    def end_field(self, name, t):
        addr, flag = self.field_flags[name]
        # A Cleanup request may consume only the current reverse frontier.
        if self.d.phase == "cleanup":
            if t.text == "abandon":
                raise Error(t, "LIFE005: cannot abandon a member during Cleanup")
            names = list(self.field_flags)
            for other in names[names.index(name) + 1 :]:
                next_flag = self.field_flags[other][1]
                self.guard(self.temp(f"load i1, ptr {next_flag}"))
        self.field_live(name, t)
        self.emit(f"store i1 false, ptr {flag}")
        typ = self.module.records[self.d.receiver][name].type
        if t.text == "destroy":
            self.drop(typ, addr)
        else:
            self.module.warn(
                t,
                "abandon ends the member generation",
                "ANOMALY",
                "LIFE004" if typ in self.module.destructors else "",
            )
        return Value("void")
