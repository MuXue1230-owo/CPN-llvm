"""Validate label edges against the initialized automatic objects at each endpoint."""

from syntax import Error, Node


def bind_names(tree, visible, types, families):
    """Bind lexical names even in discarded branches and unused generic bodies."""
    scopes = [set(visible)]
    intrinsics = {
        "std::move",
        "std::forward",
        "storage_of",
        "destroy",
        "abandon",
        "construct_at",
        "destroy_base",
        "abandon_base",
    }

    def visit(node):
        if isinstance(node, (list, tuple)):
            for child in node:
                visit(child)
            return
        if not isinstance(node, Node):
            return
        k, args = node.kind, node.args
        if k in ("name", "call"):
            word = node.token.text
            if not (
                any(word in s for s in reversed(scopes))
                or word in types
                or word.partition("<")[0] in families
                or (k == "call" and word in intrinsics)
                or ("::" in word and word.partition("::")[0] in types)
            ):
                raise Error(node.token, f"unknown name '{word}'")
        if k == "object":
            name = args[2]
            if name.text in scopes[-1]:
                raise Error(name, f"duplicate declaration '{name.text}'")
            scopes[-1].add(name.text)
        if k == "match":
            visit(args[0])
            for _, patterns, body in args[1]:
                scopes.append({t.text for _, t in patterns if t})
                visit(body)
                scopes.pop()
            return
        if k in ("block", "for"):
            scopes.append(set())
            visit(args)
            scopes.pop()
        else:
            visit(args)

    visit(tree)


def label_edges(body):
    labels = {}
    jumps = []

    def visit(stmt, active, arms):
        k, args = stmt.kind, stmt.args
        if k == "label":
            name = stmt.token.text
            if name in labels:
                raise Error(stmt.token, "duplicate statement label")
            labels[name] = (tuple(active), arms)
            visit(args[0], active, arms)
        elif k == "goto":
            jumps.append((stmt, tuple(active), arms))
        elif k == "object":
            active.append(id(stmt))
        elif k == "block":
            locals_ = list(active)
            for child in args:
                visit(child, locals_, arms)
        elif k in ("if", "if_constexpr"):
            for branch in args[1:]:
                if branch:
                    frontier = arms + (id(branch),) if k == "if_constexpr" else arms
                    visit(branch, list(active), frontier)
        elif k in ("for", "while", "do"):
            locals_ = list(active)
            if k == "for":
                visit(args[0], locals_, arms)
            visit(args[-1], locals_, arms)
        elif k == "match":
            for _, _, arm in args[1]:
                visit(arm, list(active), arms + (id(arm),))
        elif k == "switch":
            for _, arm in args[1]:
                visit(arm, list(active), arms + (id(arm),))
        elif k == "configured_block":
            visit(args[1], active, arms)

    visit(body, [], ())
    cleanup = {}
    for stmt, source, arms in jumps:
        target = stmt.args[0]
        if target.text not in labels:
            raise Error(target, "unknown statement label")
        dest, dest_arms = labels[target.text]
        if source[: len(dest)] != dest or arms[: len(dest_arms)] != dest_arms:
            raise Error(target, "goto enters an unexecuted initializer or another arm")
        cleanup[id(stmt)] = source[len(dest) :]
    return labels, cleanup
