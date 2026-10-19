#!/usr/bin/env python3
"""The comparator vocabulary modules are verbatim copies of the repository declarations.

Re-runs `tools/audit/DumpVocabulary.lean` on the statements of the comparator pairs and compares
`SpherePackingsAudit/Vocabulary/` with what `tools/audit/build_vocabulary.py` generates.
"""
import subprocess
import sys

from common import ROOT, lean_env

PAIRS = {
    "BouRabeeGwynne.TheoremAStatement": "BouRabeeGwynne.TheoremAStatement",
    "BouRabeeGwynne.TheoremBStatement": "BouRabeeGwynne.TheoremBStatement",
    "SpherePackings.MainTheorems": "SpherePackings.prop_1_1,SpherePackings.prop_1_1_theorems_A_B,"
                                   "SpherePackings.theorem_6_1,SpherePackings.theorem_4_1",
}


def main() -> int:
    mods = ",".join(PAIRS)
    roots = ",".join(PAIRS.values())
    dump = ROOT / "scratch" / "vocabulary.jsonl"
    dump.parent.mkdir(exist_ok=True)
    r = subprocess.run(["lake", "env", "lean", "--run", "tools/audit/DumpVocabulary.lean", mods, roots,
                        str(dump)], cwd=ROOT, capture_output=True, text=True, env=lean_env(), timeout=3600)
    if r.returncode:
        print(r.stdout, r.stderr)
        print("check_vocabulary: FAIL: dump failed")
        return 1
    c = subprocess.run([sys.executable, "tools/audit/build_vocabulary.py", str(dump), "--check"], cwd=ROOT)
    if c.returncode:
        print("check_vocabulary: FAIL: vocabulary differs from the repository declarations")
        return 1
    print("check_vocabulary: OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
