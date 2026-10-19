#!/usr/bin/env python3
"""Every labelled theorem, lemma and proposition of the paper is registered or listed as not formalized."""
import re
import sys

import yaml

from common import ROOT

ENVS = r"(theoremA|theorem|lemma|prop)"


def main() -> int:
    tex = (ROOT / "paper/rw-spheres.tex").read_text(encoding="utf-8").split("\n")
    results = []
    for i, line in enumerate(tex, 1):
        if line.lstrip().startswith("%"):
            continue
        m = re.search(r"\\begin\{" + ENVS + r"\}", line)
        if m:
            lab = re.search(r"\\label\{([^}]*)\}", " ".join(tex[i - 1:i + 2]))
            results.append((i, m.group(1), lab.group(1) if lab else None))
    man = yaml.safe_load((ROOT / "ledger/manifest.yaml").read_text(encoding="utf-8"))
    claimed = {n["source"].split("label ")[1].rstrip(")") for n in man["nodes"]}
    claimed |= {x["label"] for x in man["not_formalized"] if x["label"]}
    starts = {int(x["source"].split(":")[1].split("-")[0]) for x in man["not_formalized"]}
    starts |= {int(n["source"].split(":")[1].split("-")[0]) for n in man["nodes"]}
    bad = 0
    for line, env, label in results:
        ok = (label in claimed) if label else any(abs(line - s) <= 2 for s in starts)
        if not ok:
            print(f"check_coverage: {env} at rw-spheres.tex:{line} ({label}) is neither registered nor listed")
            bad = 1
    if not bad:
        print(f"check_coverage: OK ({len(results)} labelled results)")
    return bad


if __name__ == "__main__":
    sys.exit(main())
