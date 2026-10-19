#!/usr/bin/env python3
"""Check the manifest against the frozen files and scan the production tree.

1. every node's file holds exactly one frozen block, whose SHA-256 is the manifest's
   `frozen_sha256` and which declares exactly the node's export;
2. every file in `SpherePackings/Frozen/` belongs to exactly one node;
3. the paper source and the corrected source match their pinned SHA-256;
4. `SpherePackings/`, `SpherePackings.lean` and `BouRabeeGwynne/` contain no `sorry`, `admit`,
   `axiom`, `sorryAx`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `opaque`,
   `ofReduceBool`, `reduceBool` or `skipKernelTC` outside comments and strings;
5. every file of `BouRabeeGwynne/` carries the acknowledgment header naming its source.
"""
import re
import sys

import yaml

from common import ROOT, frozen_block, mask_comments, sha256

FORBIDDEN = re.compile(r"\b(sorry|admit|sorryAx|native_decide|implemented_by|axiom|extern|unsafe|opaque|"
                       r"ofReduceBool|reduceBool|skipKernelTC)\b")
HEADER = ("-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,\n"
          "-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne\n")


def main() -> int:
    errors = []
    man = yaml.safe_load((ROOT / "ledger/manifest.yaml").read_text(encoding="utf-8"))
    for pin in ("source_pin", "corrected_source_pin"):
        paper = ROOT / man[pin]["file"]
        if sha256(paper.read_text(encoding="utf-8")) != man[pin]["sha256"]:
            errors.append(f"{paper.name}: SHA-256 differs from the pin")
    owned = set()
    for node in man["nodes"]:
        path = ROOT / node["file"]
        owned.add(path.resolve())
        try:
            block = frozen_block(path)
        except (OSError, ValueError) as e:
            errors.append(str(e))
            continue
        if sha256(block) != node["frozen_sha256"]:
            errors.append(f"{node['id']}: frozen block hash changed")
        decls = re.findall(r"^theorem (\S+)", block, re.M)
        if decls != [node["export"]]:
            errors.append(f"{node['id']}: frozen block declares {decls}, expected [{node['export']}]")
    for path in sorted((ROOT / "SpherePackings/Frozen").rglob("*.lean")):
        if path.resolve() not in owned:
            errors.append(f"{path.relative_to(ROOT)}: not owned by a manifest node")
    files = [ROOT / "SpherePackings.lean"] + sorted((ROOT / "SpherePackings").rglob("*.lean")) \
        + sorted((ROOT / "BouRabeeGwynne").rglob("*.lean"))
    for path in files:
        text = path.read_text(encoding="utf-8")
        for m in FORBIDDEN.finditer(mask_comments(text)):
            line = text[:m.start()].count("\n") + 1
            errors.append(f"{path.relative_to(ROOT)}:{line}: forbidden token `{m.group(0).strip()}`")
        if path.is_relative_to(ROOT / "BouRabeeGwynne") and not text.startswith(HEADER):
            errors.append(f"{path.relative_to(ROOT)}: missing the acknowledgment header")
    for e in errors:
        print("check_manifest:", e)
    if errors:
        return 1
    print(f"check_manifest: OK ({len(man['nodes'])} nodes, {len(files)} files scanned)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
