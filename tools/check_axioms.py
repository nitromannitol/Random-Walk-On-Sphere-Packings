#!/usr/bin/env python3
"""Run `#print axioms` on every manifest export and guard; fail on any non-standard axiom."""
import sys

import yaml

from common import ROOT, STANDARD_AXIOMS, parse_axioms, run_lean_file


def main() -> int:
    man = yaml.safe_load((ROOT / "ledger/manifest.yaml").read_text(encoding="utf-8"))
    entries = [(n["export"], n["file"]) for n in man["nodes"]] + \
        [(g["export"], g["file"]) for g in man["guards"]]
    mods = sorted({f[:-5].replace("/", ".") for _, f in entries})
    src = "".join(f"import {m}\n" for m in mods) + "".join(f"#print axioms {e}\n" for e, _ in entries)
    result = run_lean_file(src)
    if result.returncode:
        print(result.stdout[-4000:], result.stderr[-4000:])
        print("check_axioms: FAIL: Lean exited with an error")
        return 1
    found = parse_axioms(result.stdout)
    bad = 0
    for e, _ in entries:
        if e not in found:
            print(f"check_axioms: no axiom report for {e}")
            bad = 1
        elif not found[e] <= STANDARD_AXIOMS:
            print(f"check_axioms: {e} uses {sorted(found[e] - STANDARD_AXIOMS)}")
            bad = 1
    if not bad:
        print(f"check_axioms: OK ({len(entries)} declarations; only propext, Classical.choice, Quot.sound)")
    return bad


if __name__ == "__main__":
    sys.exit(main())
