"""CPN virtual slots and receiver adjustment for the native nonvirtual-base layout."""

from dataclasses import replace

from numeric import irtype
from syntax import Error


def signature(method):
    return (
        method.syntax.name.text,
        method.params,
        method.readonly,
        method.syntax.receiver_category,
    )


def base_views(module, typ, path=(), lineage=()):
    lineage = (*lineage, typ)
    yield typ, path, lineage
    for i, base in enumerate(module.bases.get(typ, ())):
        yield from base_views(module, base, (*path, i), lineage)


def dispatch_thunk(module, receiver, path, target, result, params):
    if not path:
        return "@" + target
    symbol = f"cpn.thunk.{next(module.ids)}"
    indices = ", ".join(f"i32 {i}" for i in (0, *path))
    offset = (
        f"ptrtoint (ptr getelementptr ({irtype(receiver)}, ptr null, {indices}) to i64)"
    )
    formals = [f"{irtype(t)} %a{i}" for i, t in enumerate(params)]
    arguments = ", ".join(["ptr %receiver", *formals])
    call = f"call {irtype(result)} @{target}({arguments})"
    body = [
        f"define internal {irtype(result)} @{symbol}({', '.join(['ptr %view', *formals])}) {{",
        f"  %delta = sub i64 0, {offset}",
        "  %receiver = getelementptr i8, ptr %view, i64 %delta",
    ]
    if result == "void":
        body += ["  " + call, "  ret void"]
    else:
        body += ["  %result = " + call, f"  ret {irtype(result)} %result"]
    module.ir.append("\n".join([*body, "}"]))
    return "@" + symbol


def build_tables(module, typ, methods, destructor, token):
    views = list(base_views(module, typ))
    inherited = [
        m for base, _, _ in views[1:] for m in module.virtual_methods.get(base, ())
    ]
    own = []
    for m in methods:
        f = m.syntax
        roots = [b for b in inherited if signature(b) == signature(m)]
        if roots:
            if not f.override or any(
                b.syntax.final
                or b.result != m.result
                or (b.syntax.noexcept and not f.noexcept)
                for b in roots
            ):
                raise Error(f.name, "invalid override of inherited virtual slot")
        elif f.override:
            raise Error(f.name, "override has no matching inherited virtual slot")
        if f.final and not (roots or f.virtual):
            raise Error(f.name, "final requires a virtual slot")
        if roots or f.virtual:
            m.slot = len(own)
            own.append(m)
    module.virtual_methods[typ] = own

    virtual, noexcept, override, final = destructor
    parent_drops = [
        module.virtual_destructors[b]
        for b in module.bases[typ]
        if b in module.virtual_destructors
    ]
    if override and not parent_drops or final and not (virtual or parent_drops):
        raise Error(token, "invalid virtual destructor selector")
    if any(closed for _, closed in parent_drops):
        raise Error(token, "cannot override a final destructor")
    if virtual or parent_drops:
        module.virtual_destructors[typ] = (
            noexcept or any(n for n, _ in parent_drops),
            final,
        )

    tables = []
    for view, path, lineage in views:
        if "$vtable" not in module.records[view]:
            continue
        entries = []
        for slot in module.virtual_methods[view]:
            key = signature(slot)
            depth, target = next(
                (i, m)
                for i, layer in enumerate(lineage)
                for m in module.virtual_methods[layer]
                if signature(m) == key
            )
            entries.append(
                dispatch_thunk(
                    module,
                    target.receiver,
                    path[depth:],
                    target.symbol,
                    target.result,
                    target.params,
                )
            )
        if view in module.virtual_destructors:
            entries.append(dispatch_thunk(module, typ, path, "drop." + typ, "void", ()))
        symbol = f"@cpn.vtable.{next(module.ids)}"
        contents = ", ".join("ptr " + entry for entry in entries)
        module.ir.append(
            f"{symbol} = private constant [{len(entries)} x ptr] [{contents}]"
        )
        index = list(module.records[view]).index("$vtable")
        tables.append(((*path, index), symbol))
    module.vtables[typ] = tables


class VirtualCalls:
    def install_tables(self, typ, address):
        for path, table in self.module.vtables.get(typ, ()):
            slot = self.subobject_address(address, typ, path)
            self.emit(f"store ptr {table}, ptr {slot}")

    def value_tables(self, value, destination=None):
        ir = value.ir
        for path, table in self.module.vtables.get(value.type, ()):
            if destination:
                slot = self.subobject_address(destination, value.type, path)
                table = self.temp(f"load ptr, ptr {slot}")
            indices = ", ".join(map(str, path))
            ir = self.temp(
                f"insertvalue {irtype(value.type)} {ir}, ptr {table}, {indices}"
            )
        return replace(value, ir=ir)

    def virtual_target(self, d, address):
        index = list(self.module.records[d.receiver]).index("$vtable")
        field = self.subobject_address(address, d.receiver, (index,))
        table = self.temp(f"load ptr, ptr {field}")
        entry = self.temp(f"getelementptr ptr, ptr {table}, i64 {d.slot}")
        return self.temp(f"load ptr, ptr {entry}")
