"""Resolve constructor delegation and schedule declarative producers in slot order."""

from numeric import Value, record
from syntax import Error, Node


def delegation_sites(tree, conditional=False):
    if isinstance(tree, (tuple, list)):
        return sum((delegation_sites(child, conditional) for child in tree), [])
    if not isinstance(tree, Node):
        return []
    if tree.kind == "delegate":
        if conditional:
            raise Error(tree.token, "delegation must be unconditional")
        return [tree]
    restricted = tree.kind in ("if", "for", "while", "do", "match", "switch")
    return delegation_sites(tree.args, conditional or restricted)


def bind_constructors(module, constructors):
    from compiler import Emitter

    edges = {}
    for d in constructors:
        if delegation_sites(d.syntax.body):
            probe = Emitter(module, d)
            probe.probing_delegation = True
            probe.function_ir()
            if probe.delegate_edge:
                edges[d.symbol] = probe.delegate_edge
    for root in constructors:
        chain, seen, arities = [root], {root.symbol}, [len(root.params)]
        while chain[-1].symbol in edges:
            target, n = edges[chain[-1].symbol]
            if target.symbol in seen:
                raise Error(root.syntax.name, "cyclic constructor delegation")
            seen.add(target.symbol)
            chain.append(target)
            arities.append(n)
        plan = Plan(module, chain, arities)
        module.plans[root.symbol] = plan
        for i in range(1, len(chain)):
            emitter = Emitter(module, chain[i])
            emitter.plan, emitter.depth = plan, i
            module.ir.append(
                emitter.function_ir(arity=arities[i], symbol=plan.symbols[i])
            )
        module.ir.append(Emitter(module, root).function_ir())


class Plan:
    def __init__(self, module, chain, arities):
        self.chain, self.arities = chain, arities
        self.symbols = [
            chain[0].symbol,
            *(f"cpn.activation.{next(module.ids)}" for _ in chain[1:]),
        ]
        self.offsets = []
        self.nparams = 0
        owners = {}
        for i, d in enumerate(chain):
            self.offsets.append(self.nparams)
            self.nparams += len(d.params)
            for slot in d.producers:
                if slot in owners:
                    raise Error(
                        d.syntax.name,
                        "duplicate initialization producer in delegation chain",
                    )
                owners[slot] = i
        self.steps = []
        ready = 0
        typ = chain[0].receiver
        for slot, default in module.records[typ].items():
            if slot == "$vtable":
                continue
            owner = owners.get(slot, 0)
            ready = max(ready, owner)
            self.steps.append((slot, default, owner, ready))
        self.bases = len(module.bases[typ])

    def initialize(self, em, fields, cells):
        depth = em.depth
        if depth == 0:
            em.environment = em.allocate(f"void*[{max(1, self.nparams)}]")
        else:
            em.environment = "%activation"
        for i, cell in enumerate(cells, self.offsets[depth]):
            slot = em.temp(f"getelementptr ptr, ptr {em.environment}, i64 {i}")
            em.emit(f"store ptr {cell.address}, ptr {slot}")

        em.construction_fields = fields
        em.slot_addresses = {slot: fields[slot] for slot, *_ in self.steps}
        for slot, _, _, ready in self.steps:
            if ready >= depth:
                fields[slot] = None
        if depth == 0 and self.bases == 0:
            em.install_tables(em.d.receiver, "%self")
        for i, (slot, default, owner, ready) in enumerate(self.steps):
            if ready != depth:
                continue
            source = self.chain[owner]
            address = em.slot_addresses[slot].address
            if slot in source.producers:
                # Capture addresses rather than snapshots: a delegate prelude may
                # have changed an earlier activation's parameter before its turn.
                parameters = {}
                for j, (p, typ) in enumerate(
                    zip(source.syntax.params, source.params), self.offsets[owner]
                ):
                    if p.name:
                        loc = em.temp(
                            f"getelementptr ptr, ptr {em.environment}, i64 {j}"
                        )
                        ptr = em.temp(f"load ptr, ptr {loc}")
                        base = typ.rstrip("&")
                        const = base.startswith("const<") and base.endswith(">")
                        parameters[p.name.text] = Value(
                            base[6:-1] if const else base,
                            address=ptr,
                            readonly=const or p.readonly,
                        )
                saved = em.scopes, em.names, em.types, em.policy, em.default_int
                em.scopes = [fields, parameters]
                em.names, em.types, em.policy, em.default_int = (
                    source.names,
                    source.types,
                    source.policy,
                    source.default_int,
                )
                try:
                    value = em.construct(
                        default.type,
                        source.producers[slot],
                        source.syntax.name,
                        destination=address,
                    )
                finally:
                    em.scopes, em.names, em.types, em.policy, em.default_int = saved
            elif record(default.type) or default.type.endswith("]"):
                value = em.construct(
                    default.type, (), source.syntax.name, destination=address
                )
            else:
                value = default
            if value.temporary != address:
                em.store(value, address)
            em.consume(value)
            em.finish_expression()
            fields[slot] = em.slot_addresses[slot]
            if i + 1 == self.bases:
                em.install_tables(em.d.receiver, "%self")

    def delegate(self, em, values, tok):
        index = em.depth + 1
        target = self.chain[index]
        args = em.call_args(target, values, tok)
        operands = ["ptr %self", "ptr " + em.environment, *args]
        em.emit(f"call void @{self.symbols[index]}({', '.join(operands)})")
        em.finish_expression()
        em.construction_fields.update(em.slot_addresses)
