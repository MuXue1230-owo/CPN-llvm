"""Unicode 17 identifier classes and canonical normalization (UAX #15)."""

from bisect import bisect_right
from functools import cache
import gzip
import json
import pkgutil


@cache
def data():
    return json.loads(gzip.decompress(pkgutil.get_data(__name__, "ucd17.json.gz")))


def admitted(ch, first=False):
    if ch.isascii():
        return ch == "_" or ch.isalpha() or (not first and ch.isdigit())
    cp = ord(ch)
    prop = "XID_Start" if first else "XID_Continue"
    return (
        bisect_right(data()[prop], cp) % 2 == 1
        and bisect_right(data()["Default_Ignorable_Code_Point"], cp) % 2 == 0
    )


def nfc(text):
    if text.isascii():
        return text
    db = data()
    decomposed = []

    def expand(ch):
        s = ord(ch) - 0xAC00
        if 0 <= s < 11172:
            decomposed.extend((chr(0x1100 + s // 588), chr(0x1161 + s % 588 // 28)))
            if s % 28:
                decomposed.append(chr(0x11A7 + s % 28))
        elif ch in db["decompose"]:
            for child in db["decompose"][ch]:
                expand(child)
        else:
            decomposed.append(ch)

    for ch in text:
        expand(ch)
    rank = db["ccc"].get
    ordered = []
    pending = []
    for ch in decomposed:
        if rank(ch, 0) == 0:
            ordered.extend(sorted(pending, key=lambda c: rank(c, 0)))
            pending.clear()
            ordered.append(ch)
        else:
            pending.append(ch)
    ordered.extend(sorted(pending, key=lambda c: rank(c, 0)))
    result = []
    starter = None
    last = 0
    for ch in ordered:
        cc = rank(ch, 0)
        if starter is not None and (not last or last < cc):
            base = result[starter]
            joined = db["compose"].get(base + ch)
            l, v = ord(base) - 0x1100, ord(ch) - 0x1161
            s, t = ord(base) - 0xAC00, ord(ch) - 0x11A7
            if 0 <= l < 19 and 0 <= v < 21:
                joined = chr(0xAC00 + 588 * l + 28 * v)
            elif 0 <= s < 11172 and s % 28 == 0 and 0 < t < 28:
                joined = chr(ord(base) + t)
            if joined:
                result[starter] = joined
                continue
        if not cc:
            starter = len(result)
        result.append(ch)
        last = cc
    return "".join(result)
