#!/usr/bin/env python3
"""Write a frozen-statement file restating a support theorem.

Usage: frozen_from_support.py <spec.json>; the spec lists nodes with fields
`file` (under SpherePackings/Frozen), `name` (frozen declaration, without the namespace),
`source` (support file), `theorem` (support theorem, short name as written in its file),
`full` (its full name), `import`, `opens`, `prefix` (extra leading binders, e.g. variables of the
support file), `doc`.  The frozen statement copies the support theorem's binders and conclusion;
its proof applies the support theorem to the explicit binders.
"""
import json
import re
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]


def signature(text: str, name: str) -> str:
    m = re.search(rf"theorem {re.escape(name)}(?=[\s(\[{{])", text)
    if not m:
        raise SystemExit(f"theorem {name} not found")
    k = m.end()
    depth = 0
    j = k
    while j < len(text):
        c = text[j]
        if c in "([{⦃":
            depth += 1
        elif c in ")]}⦄":
            depth -= 1
        elif depth == 0 and (text.startswith(":= by\n", j) or text.startswith(":=\n", j)):
            break
        j += 1
    return text[k:j].rstrip()


def explicit_names(sig: str) -> list[str]:
    """Names bound by top-level `( ... )` groups before the final colon."""
    names = []
    depth = 0
    j = 0
    while j < len(sig):
        c = sig[j]
        if c in "([{⦃":
            if depth == 0 and c == "(":
                close = j
                d2 = 0
                while True:
                    ch = sig[close]
                    if ch in "([{⦃":
                        d2 += 1
                    elif ch in ")]}⦄":
                        d2 -= 1
                        if d2 == 0:
                            break
                    close += 1
                group = sig[j + 1:close]
                if ":" in group:
                    names += group.split(":", 1)[0].split()
                j = close + 1
                continue
            depth += 1
        elif c in ")]}⦄":
            depth -= 1
        elif depth == 0 and c == ":":
            break
        j += 1
    return names


def main() -> None:
    for spec in json.loads(pathlib.Path(sys.argv[1]).read_text()):
        text = (ROOT / spec["source"]).read_text()
        sig = signature(text, spec["theorem"])
        pre = spec.get("prefix", "")
        args = " ".join(explicit_names(pre + " " + sig))
        stmt = f"theorem SpherePackings.Frozen.{spec['name']} {pre}{sig.strip()}"
        out = (f"/-\n{spec['doc']}\n-/\n{spec['import']}\n\n{spec['opens']}\n"
               f"-- FROZEN-STATEMENT-BEGIN\n{stmt}\n-- FROZEN-STATEMENT-END\n"
               f":= {spec['full']} {args}\n").replace(" \n", "\n")
        (ROOT / "SpherePackings/Frozen" / spec["file"]).write_text(out)
        print(spec["file"])


if __name__ == "__main__":
    main()
