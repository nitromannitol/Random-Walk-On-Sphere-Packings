#!/usr/bin/env python3
"""`lake build SpherePackings` emits no warning in this repository's own modules.

leobon12's files under `BouRabeeGwynne/` are kept byte-for-byte (apart from a header) and are
exempt: they emit linter and deprecation warnings under this toolchain.
"""
import re
import subprocess
import sys

from common import ROOT, lean_env


def main() -> int:
    result = subprocess.run(["lake", "build", "SpherePackings"], cwd=ROOT, capture_output=True,
                            text=True, env=lean_env(), timeout=14400)
    out = result.stdout + result.stderr
    if result.returncode:
        print(out[-4000:])
        print("check_warnings: FAIL: build failed")
        return 1
    own = [l for l in out.splitlines() if re.match(r"^warning: SpherePackings", l)]
    for l in own:
        print("check_warnings:", l)
    if own:
        return 1
    print("check_warnings: OK (no warning in SpherePackings modules)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
