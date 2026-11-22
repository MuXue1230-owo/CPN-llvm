"""Generate immutable C++ lookup tables from cpnc's pinned Unicode 17 data."""

import gzip
import json
import sys

with gzip.open(sys.argv[1], "rt", encoding="utf-8") as source:
    db = json.load(source)
with open(sys.argv[2], "w", encoding="utf-8") as f:
    for prop, name in [
        ("XID_Start", "Start"),
        ("XID_Continue", "Continue"),
        ("Default_Ignorable_Code_Point", "Ignorable"),
    ]:
        print(f"static constexpr uint32_t {name}[] = {{", file=f)
        print(",".join(map(str, db[prop])), "};", file=f)
    for prop, name in [
        ("ccc", "Ranks"),
        ("decompose", "Decomp"),
        ("compose", "Compositions"),
    ]:
        entries = []
        for key, value in db[prop].items():
            if prop == "ccc":
                row = [ord(key), value]
            elif prop == "decompose":
                row = [ord(key)] + list(map(ord, value))
            else:
                row = [(ord(key[0]) << 21) | ord(key[1]), ord(value)]
            entries.append(row)
        print(f"static constexpr Entry {name}[] = {{", file=f)
        for row in sorted(entries):
            print("{" + ",".join(map(str, row)) + "},", file=f)
        print("};", file=f)
