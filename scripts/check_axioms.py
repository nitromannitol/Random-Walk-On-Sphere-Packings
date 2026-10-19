#!/usr/bin/env python3
"""Require one exact standard-axiom report for each main theorem printed by the axiom audit.

Usage: check_axioms.py LOG, where LOG is the output of
`lake env lean SpherePackings/Meta/AxiomsAudit.lean`.  `tools/check_axioms.py` (run by
`tools/verify.py`) checks, in addition, every registered statement and guard.
"""
import pathlib
import re
import sys

expected = {
    'SpherePackings.theorem_A',
    'SpherePackings.theorem_B_a',
    'SpherePackings.theorem_B_b',
    'SpherePackings.prop_1_1',
    'SpherePackings.prop_1_1_theorems_A_B',
    'SpherePackings.theorem_6_1',
    'SpherePackings.theorem_4_1',
}
standard = {'propext', 'Classical.choice', 'Quot.sound'}
log = pathlib.Path(sys.argv[1]).read_text()
if re.search(r'warning:|sorryAx|declaration uses .sorry|error:', log, re.IGNORECASE):
    raise SystemExit('Axiom audit emitted a warning or an error, or reported sorryAx')
reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log)
seen = set()
for theorem, axioms in reports:
    if theorem not in expected or theorem in seen:
        raise SystemExit('Unexpected or duplicate axiom report: ' + theorem)
    actual = [a.strip() for a in axioms.split(',')]
    if len(actual) != 3 or set(actual) != standard:
        raise SystemExit('Unexpected axioms for ' + theorem + ': ' + axioms)
    seen.add(theorem)
if seen != expected:
    raise SystemExit('Missing axiom reports: ' + ', '.join(sorted(expected - seen)))
print('The %d main theorems use exactly propext, Classical.choice and Quot.sound.' % len(expected))
