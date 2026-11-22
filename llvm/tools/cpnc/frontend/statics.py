"""Single-root static initialization, publication and reverse shutdown (chapter 8)."""

from dataclasses import dataclass

from numeric import irtype
from syntax import Error


@dataclass(frozen=True)
class StaticObject:
    identity: tuple
    name: str
    dependencies: tuple
    token: object
    address: str
    type: str
    initializer: str | None
    ready: str | None


def define_static(emitter, name, typ, value, destination, qualifier):
    module = emitter.module
    ordinal = len(module.statics)
    local_id = (module.logical_path, ordinal, ())
    if "static_id" in module.static_attributes:
        local_id = (module.static_attributes["static_id"],)
    identity = ("cpnc", module.root_id, *local_id)
    dynamic = bool(emitter.lines)
    initializer = f"cpn.static.init.{ordinal}" if dynamic else None
    needs_drop = typ in module.destructors
    flag = f"@cpn.static.ready.{ordinal}" if dynamic or needs_drop else None
    if dynamic and qualifier == "constexpr":
        raise Error(name, "constexpr static requires constant initialization")
    storage = "constant" if qualifier and not dynamic and not needs_drop else "global"
    initial = "zeroinitializer" if dynamic else value.ir
    module.ir.append(f"{destination} = internal {storage} {irtype(typ)} {initial}")
    if flag:
        module.ir.append(
            f"{flag} = internal global i1 {'false' if dynamic else 'true'}"
        )
        module.static_flags[destination] = flag
    if dynamic:
        if value.temporary != destination:
            emitter.store(value, destination)
        emitter.consume(value)
        emitter.finish_expression()
        emitter.emit(f"store i1 true, ptr {flag}")
        emitter.emit("ret void")
        module.ir.append(
            "\n".join(
                [
                    f"define internal void @{initializer}() {{",
                    "entry:",
                    *emitter.entry,
                    *emitter.lines,
                    "}",
                ]
            )
        )
    module.statics.append(
        StaticObject(
            identity,
            module.prefix + name.text,
            module.static_attributes.get("init_after", ()),
            name,
            destination,
            typ,
            initializer,
            flag,
        )
    )


def emit_domain(module):
    ranks = {obj.name: i for i, obj in enumerate(module.statics)}
    identities = set()
    for i, obj in enumerate(module.statics):
        if obj.identity in identities:
            raise Error(obj.token, "STAT001: duplicate static object identity")
        identities.add(obj.identity)
        for name in obj.dependencies:
            path = obj.name.split("::")[:-1]
            candidates = (
                [name[2:]]
                if name.startswith("::")
                else ["::".join(path[:n] + [name]) for n in range(len(path), -1, -1)]
            )
            rank = next((ranks[c] for c in candidates if c in ranks), None)
            if rank is None:
                raise Error(obj.token, f"unknown static dependency '{name}'")
            # A single logical file already has every consecutive precedence edge.
            if rank >= i:
                raise Error(
                    obj.token, "STAT001: cyclic static initialization dependency"
                )
    startup = [
        f"call void @{obj.initializer}()" for obj in module.statics if obj.initializer
    ]
    shutdown = []
    for obj in reversed(module.statics):
        drop = module.destructors.get(obj.type)
        if drop:
            shutdown.append(f"call void @{drop}(ptr {obj.address})")
        if obj.ready:
            shutdown.append(f"store i1 false, ptr {obj.ready}")
    for name, hook, body in (
        ("startup", "ctors", startup),
        ("shutdown", "dtors", shutdown),
    ):
        if not body:
            continue
        symbol = f"@cpn.static.{name}"
        module.ir.append(
            "\n".join(
                [
                    f"define internal void {symbol}() {{",
                    "entry:",
                    *("  " + line for line in body),
                    "  ret void",
                    "}",
                ]
            )
        )
        entry = "{ i32, ptr, ptr }"
        module.ir.append(
            f"@llvm.global_{hook} = appending global [1 x {entry}] "
            f"[{entry} {{ i32 65535, ptr {symbol}, ptr null }}]"
        )
