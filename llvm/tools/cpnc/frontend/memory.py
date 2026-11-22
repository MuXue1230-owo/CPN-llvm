"""Local storage extents and generation-sensitive lowering (chapters 6 and 12)."""

from dataclasses import dataclass, replace

from numeric import Value, handle, irtype, record, width
from syntax import Error


@dataclass
class Extent:
    type: str
    current_type: str
    scope: int
    generation: int | str | None = 1
    active: bool | None = True
    stamp: str = ""
    destructor: str = ""


def uses_storage(tree):
    from syntax import Node

    if isinstance(tree, Node):
        if tree.kind == "call" and tree.token.text in (
            "abandon",
            "destroy",
            "construct_at",
        ):
            return True
        return uses_storage(tree.args)
    if isinstance(tree, (list, tuple)):
        return any(uses_storage(child) for child in tree)
    return False


class MemoryLowering:
    def layout(self, typ):
        if typ in self.module.incomplete:
            raise Error(self.site, "layout requires a complete object type")
        if typ.endswith("]"):
            element, count = typ[:-1].rsplit("[", 1)
            size, alignment = self.layout(element)
            return max(size * int(count), alignment), alignment
        if typ.startswith("const<") and typ.endswith(">"):
            return self.layout(typ[6:-1])
        if record(typ):
            size, alignment = 0, 1
            for field in self.module.records[typ].values():
                n, a = self.layout(field.type)
                size = (size + a - 1) // a * a + n
                alignment = max(alignment, a)
            return max(1, (size + alignment - 1) // alignment * alignment), alignment
        if handle(typ):
            return (1, 1) if typ == "nullptr_t" else (8, 8)
        n = max(1, width(typ) // 8)
        return n, n

    def register(self, typ, ptr, scope):
        extent = Extent(typ, typ, id(scope))
        if self.tracking:
            extent.stamp = self.allocate("i64")
            extent.destructor = self.allocate("void*")
            self.emit(f"store i64 1, ptr {extent.stamp}")
            self.set_destructor(extent, typ)
        self.extents[ptr] = extent

    def set_destructor(self, extent, typ):
        symbol = self.module.destructors.get(typ)
        fn = "@" + symbol if symbol else "null"
        self.emit(f"store ptr {fn}, ptr {extent.destructor}")

    def live(self, owner, generation, tok):
        if not owner:
            return
        extent = self.extents.get(owner)
        if not extent or extent.active is False:
            raise Error(tok, "LIFE002: access to an ended object generation")
        if extent.generation == generation and extent.active is True:
            return
        if isinstance(extent.generation, int) and isinstance(generation, int):
            raise Error(tok, "LIFE002: access to an ended object generation")
        stamp = self.temp(f"load i64, ptr {extent.stamp}")
        self.guard(self.temp(f"icmp ne i64 {stamp}, {generation}"))

    def forget_lifetimes(self):
        if self.tracking:
            for extent in self.extents.values():
                extent.generation = extent.active = None
                extent.current_type = ""

    def facts(self):
        return {p: replace(e) for p, e in self.extents.items()}

    def merge_facts(self, other):
        for p, e in self.extents.items():
            prev = other[p]
            if e.active != prev.active:
                e.active = None
            if e.generation != prev.generation:
                e.generation = None
            if e.current_type != prev.current_type:
                e.current_type = ""

    def place(self, node):
        if node.kind == "group":
            return self.place(node.args[0])
        if node.kind == "name":
            v = self.lookup(node.token)
        elif node.kind == "prefix" and node.token.text == "*":
            ptr = self.expr(node.args[0])
            if not ptr.type.endswith("*") or ptr.type == "void*":
                raise Error(node.token, "typed object pointer required")
            self.live(ptr.owner, ptr.generation, node.token)
            if ptr.ir == "null":
                raise Error(node.token, "null pointer access")
            if not ptr.owner:
                self.guard(self.temp(f"icmp eq ptr {ptr.ir}, null"))
            pointee = ptr.type[:-1]
            if pointee in self.module.signatures:
                raise Error(node.token, "function designator requires a call")
            readonly = pointee.startswith("const<") and pointee.endswith(">")
            if readonly:
                pointee = pointee[6:-1]
            v = Value(pointee, address=ptr.ir, readonly=readonly)
        else:
            v = self.expr(node)
        if not isinstance(v, Value) or not v.address:
            raise Error(node.token, "object lvalue required")
        return v

    def index(self, node):
        obj = self.expr(node.args[0])
        if not obj.address or not obj.type.endswith("]"):
            raise Error(node.token, "indexing needs an array lvalue")
        typ, extent = obj.type[:-1].rsplit("[", 1)
        index = self.expr(node.args[1])
        if (
            index.type != "integer"
            and index.type not in ("usize", "isize")
            and not (index.type[:1] in ("u", "i") and index.type[1:].isdigit())
        ):
            raise Error(node.token, "integer index required")
        if index.constant is not None:
            if not 0 <= index.constant < int(extent):
                raise Error(node.token, "array index outside extent")
        elif int(extent) < (1 << width(index.type)):
            self.guard(self.temp(f"icmp uge {irtype(index.type)} {index.ir}, {extent}"))
        elif index.type.startswith("i"):
            self.guard(self.temp(f"icmp slt {irtype(index.type)} {index.ir}, 0"))
        idx = self.cast_bits(index, 64)
        ptr = self.temp(
            f"getelementptr {irtype(obj.type)}, ptr {obj.address}, i64 0, i64 {idx}"
        )
        immutable = typ.startswith("const<") and typ.endswith(">")
        return self.load(
            Value(
                typ[6:-1] if immutable else typ,
                address=ptr,
                readonly=obj.readonly or immutable,
            )
        )

    def local_extent(self, node, tok):
        while node.kind == "group":
            node = node.args[0]
        if node.kind != "name":
            raise Error(tok, "this storage operation requires a named automatic object")
        obj = self.lookup(node.token)
        if not isinstance(obj, Value) or obj.address not in self.extents:
            raise Error(tok, "automatic storage extent required")
        return obj, self.extents[obj.address]

    def storage_op(self, node):
        t = node.token
        explicit, args = node.args
        if t.text == "construct_at":
            if len(explicit) != 1 or not isinstance(explicit[0], str) or not args:
                raise Error(t, "construct_at requires a type and a storage view")
            storage = self.expr(args[0])
            if storage.type != "storage" or storage.owner not in self.extents:
                raise Error(t, "live local storage view required")
            extent = self.extents[storage.owner]
            if extent.active is None:
                stamp = self.temp(f"load i64, ptr {extent.stamp}")
                self.guard(self.temp(f"trunc i64 {stamp} to i1"))
            if extent.active is True:
                raise Error(t, "storage contains a live generation")
            typ = self.resolve(explicit[0])
            if typ == "void" or typ.endswith("&"):
                raise Error(t, "construct_at requires an object type")
            size, alignment = self.layout(typ)
            n, a = self.layout(extent.type)
            if size > n or alignment > a:
                raise Error(t, "insufficient storage capacity or alignment")
            val = self.construct(typ, args[1:], t)
            self.store(val, storage.owner)
            self.consume(val)
            extent.active = True
            prev = self.temp(f"load i64, ptr {extent.stamp}")
            stamp = self.temp(f"add i64 {prev}, 1")
            self.emit(f"store i64 {stamp}, ptr {extent.stamp}")
            extent.generation = (
                extent.generation + 1 if isinstance(extent.generation, int) else stamp
            )
            self.set_destructor(extent, typ)
            extent.current_type = typ
            return Value(
                typ + "*",
                storage.owner,
                owner=storage.owner,
                generation=extent.generation,
            )
        if len(args) != 1 or explicit:
            raise Error(t, "storage operation requires one object")
        if t.text == "storage_of":
            obj, _ = self.local_extent(args[0], t)
            return Value("storage", obj.address, owner=obj.address)
        field = self.field_name(args[0])
        if field:
            return self.end_field(field, t)
        if args[0].kind == "prefix" and args[0].token.text == "*":
            ptr = self.expr(args[0].args[0])
            view = ptr.type[:-1]
            if view.startswith("const<") and view.endswith(">"):
                view = view[6:-1]
            if ptr.subobject and view not in self.module.virtual_destructors:
                raise Error(
                    t,
                    "complete destruction through a base view requires virtual destruction",
                )
            if not ptr.type.endswith("*") or ptr.owner not in self.extents:
                raise Error(t, "destruction requires a complete local object")
            owner, gen = ptr.owner, ptr.generation
        else:
            obj, _ = self.local_extent(args[0], t)
            owner, gen = obj.address, 1
        self.live(owner, gen, t)
        extent = self.extents[owner]
        if t.text == "destroy":
            self.drop_registered(extent, owner)
        else:
            self.module.warn(
                t,
                "abandon ends this generation without destruction",
                "ANOMALY",
                "LIFE004" if extent.current_type in self.module.destructors else "",
            )
        stamp = self.temp(f"add i64 {gen}, 1")
        self.emit(f"store i64 {stamp}, ptr {extent.stamp}")
        extent.generation = gen + 1 if isinstance(gen, int) else stamp
        self.set_destructor(extent, None)
        extent.active = False
        return Value("void")

    def drop_registered(self, extent, ptr):
        if extent.active is False:
            return
        if extent.active is True and extent.current_type:
            self.drop(extent.current_type, ptr)
            return
        callback = self.temp(f"load ptr, ptr {extent.destructor}")
        needs_drop = self.temp(f"icmp ne ptr {callback}, null")
        run, done = self.ident(), self.ident()
        self.emit(f"br i1 {needs_drop}, label %{run}, label %{done}")
        self.label(run)
        self.emit(f"call void {callback}(ptr {ptr})")
        self.jump(done)
        self.label(done)

    def drop(self, typ, address):
        if typ in self.module.destructors:
            self.emit(f"call void @{self.module.destructors[typ]}(ptr {address})")

    def cleanup(self, depth, leaving=False):
        for scope in reversed(self.scopes[depth:]):
            for ptr, e in reversed(list(self.extents.items())):
                if e.scope != id(scope):
                    continue
                self.drop_registered(e, ptr)
                if leaving:
                    del self.extents[ptr]
