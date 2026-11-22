"""Generate unicode/ucd17.json.gz from the Unicode 17.0.0 UCD text files.

Usage: python3 utils/build_ucd.py <ucd-directory> <output.gz>
Inputs: https://www.unicode.org/Public/17.0.0/ucd/
"""

import gzip
import hashlib
import json
from pathlib import Path
import sys

HASHES = {
    "DerivedCoreProperties": "24c7fed1195c482faaefd5c1e7eb821c5ee1fb6de07ecdbaa64b56a99da22c08",
    "DerivedNormalizationProps": "71fd6a206a2c0cdd41feb6b7f656aa31091db45e9cedc926985d718397f9e488",
    "UnicodeData": "2e1efc1dcb59c575eedf5ccae60f95229f706ee6d031835247d843c11d96470c",
}


def lines(stem):
    data = (Path(sys.argv[1]) / (stem + ".txt")).read_bytes()
    if hashlib.sha256(data).hexdigest() != HASHES[stem]:
        raise ValueError("unexpected Unicode data: " + stem)
    for line in data.decode().splitlines():
        line = line.split("#")[0].strip()
        if line:
            yield [field.strip() for field in line.split(";")]


def property_ranges(stem, prop):
    bounds = []
    for codes, name, *_ in lines(stem):
        if name != prop:
            continue
        parts = codes.split("..")
        lo, hi = int(parts[0], 16), int(parts[-1], 16) + 1
        if bounds and lo == bounds[-1]:
            bounds[-1] = hi
        else:
            bounds.extend((lo, hi))
    return bounds


if __name__ == "__main__":
    from bisect import bisect_right

    excluded = property_ranges(
        "DerivedNormalizationProps", "Full_Composition_Exclusion"
    )
    table = {
        p: property_ranges("DerivedCoreProperties", p)
        for p in ("XID_Start", "XID_Continue", "Default_Ignorable_Code_Point")
    }
    ccc, decomposition, composition = {}, {}, {}
    for fields in lines("UnicodeData"):
        cp = int(fields[0], 16)
        if int(fields[3]):
            ccc[chr(cp)] = int(fields[3])
        if fields[5] and not fields[5].startswith("<"):
            parts = "".join(chr(int(x, 16)) for x in fields[5].split())
            decomposition[chr(cp)] = parts
            if len(parts) == 2 and not bisect_right(excluded, cp) % 2:
                composition[parts] = chr(cp)
    table.update(ccc=ccc, decompose=decomposition, compose=composition)
    data = json.dumps(table, separators=(",", ":"), ensure_ascii=False).encode()
    Path(sys.argv[2]).write_bytes(gzip.compress(data, mtime=0))
