"""Nonvirtual base layout, member lookup and base-subobject conversions."""

from dataclasses import replace

from numeric import Value, irtype
from syntax import Error, NoOperation


def base_paths(module, derived, target):
    if derived == target:
        return [()]
    return [
        (i, *path)
        for i, base in enumerate(module.bases.get(derived, ()))
        for path in base_paths(module, base, target)
    ]


def member_paths(module, owner, name):
    if name in module.records.get(owner, {}) or (owner, name) in module.methods:
        return [((), owner)]
    return [
        ((i, *path), declaring)
        for i, base in enumerate(module.bases.get(owner, ()))
        for path, declaring in member_paths(module, base, name)
    ]


class BaseSubobjects:
    def member_owner(self, obj, tok):
        matches = member_paths(self.module, obj.type, tok.text)
        if len(matches) > 1:
            raise Error(tok, f"ambiguous inherited member '{tok.text}'")
        if not matches:
            raise NoOperation(tok, f"unknown member '{tok.text}' of {obj.type}")
        path, owner = matches[0]
        if not path:
            return obj
        if self.d and obj.address == "%self" and obj.type == self.d.receiver:
            slot = "$base:" + self.module.bases[obj.type][path[0]]
            if self.d.phase:
                self.field_live(slot, tok)
            if self.d.producers is not None and any(
                slot in scope and scope[slot] is None for scope in self.scopes
            ):
                raise Error(tok, "access before base initialization")
        pointer = obj.address or obj.temporary
        if not pointer:
            pointer = self.allocate(obj.type)
            self.store(obj, pointer)
        addr = self.subobject_address(pointer, obj.type, path)
        return Value(owner, address=addr, readonly=obj.readonly, expiring=obj.expiring)

    def subobject_address(self, ptr, derived, path):
        if not path:
            return ptr
        indices = ", ".join(f"i32 {index}" for index in (0, *path))
        return self.temp(f"getelementptr {irtype(derived)}, ptr {ptr}, {indices}")

    def base_pointer_path(self, source, target):
        if not source.endswith("*") or not target.endswith("*"):
            return None
        old, new = source[:-1], target[:-1]
        old_const = old.startswith("const<") and old.endswith(">")
        new_const = new.startswith("const<") and new.endswith(">")
        if old_const and not new_const:
            return None
        derived = old[6:-1] if old_const else old
        base = new[6:-1] if new_const else new
        if derived not in self.module.bases or derived == base:
            return None
        paths = base_paths(self.module, derived, base)
        return (derived, paths[0]) if len(paths) == 1 else None

    def upcast_pointer(self, v, target, conversion):
        if v.ir == "null":
            return Value(target, "null")
        derived, path = conversion
        address = self.subobject_address(v.ir, derived, path)
        null = self.temp(f"icmp eq ptr {v.ir}, null")
        result = self.temp(f"select i1 {null}, ptr null, ptr {address}")
        return replace(
            v, type=target, ir=result, address="", temporary="", subobject=True
        )
