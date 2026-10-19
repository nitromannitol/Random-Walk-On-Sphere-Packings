#!/usr/bin/env python3
"""Run every check, stopping at the first failure."""
import subprocess
import sys

from common import ROOT, lean_env

CHECKS = ("check_manifest", "check_coverage", "sync_docs", "check_warnings", "check_axioms",
          "check_vocabulary")


def main() -> int:
    for name in CHECKS:
        cmd = [sys.executable, f"tools/{name}.py"]
        print("\n" + " ".join(cmd), flush=True)
        if subprocess.run(cmd, cwd=ROOT, env=lean_env()).returncode:
            return 1
    cmd = [sys.executable, "tools/certificate.py", "--check"]
    print("\n" + " ".join(cmd), flush=True)
    if subprocess.run(cmd, cwd=ROOT, env=lean_env()).returncode:
        return 1
    print("\nverify: all checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
