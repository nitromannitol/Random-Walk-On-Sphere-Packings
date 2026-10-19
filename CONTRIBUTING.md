# Contributing and building

This repository is mainly a finished artifact, the formalization of one paper, but issues and pull
requests are welcome.

## Building locally

```bash
lake exe cache get   # prebuilt mathlib oleans
lake build           # compile leobon12's BouRabeeGwynne/ and this repository's SpherePackings/
```

The toolchain is pinned in `lean-toolchain` and managed by
[elan](https://github.com/leanprover/elan).  This repository's modules must build with **no
warnings**; leobon12's files under `BouRabeeGwynne/` emit linter and deprecation warnings under
this toolchain, which the warning check exempts.  The only files that contain a `sorry` are the six
comparator challenges under `SpherePackingsAudit/*/Challenge.lean`, each with exactly one, in its
final theorem.

`lake build SpherePackingsAudit` builds the comparator files.  The checkers need Python 3.10 or
newer and PyYAML (`python3 -m pip install -r tools/requirements.txt`); `python3 tools/verify.py`
runs them all.

- **Never run `lake clean`.**  It wipes the Mathlib oleans.  To force a project-only rebuild,
  delete `.lake/build/lib/lean/SpherePackings` (and `.lake/build/ir/SpherePackings`).

## The main results and the axiom audit

The main theorems are in `SpherePackings/MainTheorems.lean`: `theorem_A`, `theorem_B_a`,
`theorem_B_b`, `prop_1_1`, `prop_1_1_theorems_A_B`, `theorem_4_1` and `theorem_6_1`.  Their axiom
reports must consist of exactly `propext`, `Classical.choice` and `Quot.sound`:

```bash
lake env lean SpherePackings/Meta/AxiomsAudit.lean 2>&1 | tee .lake/axioms-audit.log
python3 scripts/check_axioms.py .lake/axioms-audit.log
```

The check script fails on `sorryAx`, on any other axiom, on a warning and on a missing, unexpected
or duplicate report.  `python3 tools/check_axioms.py` checks, in addition, every registered
statement and guard.

## The registry

- **Frozen statements.**  The text between `-- FROZEN-STATEMENT-BEGIN` and
  `-- FROZEN-STATEMENT-END` in `SpherePackings/Frozen/` is pinned by the SHA-256 recorded in
  `ledger/manifest.yaml`, which `python3 tools/sync_docs.py --write` regenerates from
  `tools/nodes.py`.  The frozen files are generated from the support theorems by
  `python3 tools/gen/frozen_from_support.py tools/gen/frozen_specs.json` (Theorems A and B and
  Proposition 1.1 restate leobon12's or the support statements directly).
- **The paper.**  `paper/rw-spheres.tex` (arXiv v2, unchanged) and `paper/rw-spheres-corrected.tex`
  are pinned by SHA-256 in `tools/nodes.py`; refer to a result of the paper by its LaTeX label and
  to the arXiv source by line number, as [`CORRESPONDENCE.md`](CORRESPONDENCE.md) does.

## Conventions for Lean files

- **`BouRabeeGwynne/` is a copy** of leobon12's files, unchanged apart from a header naming the
  source and, in 13 walk files, `omit [Fintype V] in` before declarations that do not use
  finiteness.  Do not edit it: `tools/check_manifest.py` checks the header, and the comparator
  vocabulary under `SpherePackingsAudit/Vocabulary/` must stay byte-identical to its declarations
  (`python3 tools/check_vocabulary.py`).
- No `sorry`, `admit`, `native_decide` or new `axiom` anywhere in the library
  (`tools/check_manifest.py` lists every forbidden token), and no `set_option maxHeartbeats` in
  `SpherePackings/` (three of leobon12's files raise it).
- New files follow the conventions of the existing ones: Mathlib naming, a module docstring
  citing the paper's label, files under 700 lines, no warnings, and a header naming leobon12's
  source when the file adapts his code.

## Comparators

Each pair under `SpherePackingsAudit/` has a mathlib-only `Challenge.lean` (through the vocabulary
modules), a `Solution.lean` that proves the same statement from the library, and a
`comparator.json` that permits exactly `propext`, `Classical.choice` and `Quot.sound` and enables
the nanoda kernel.  Do not add a declaration to a challenge that the statement does not need, and
do not change a challenge without checking it against the paper's statement.  After changing a
statement, regenerate the vocabulary (`lake env lean --run tools/audit/DumpVocabulary.lean
<modules> <roots> <dump>` and `python3 tools/audit/build_vocabulary.py <dump>`) and the pairs
(`python3 tools/audit/make_pairs.py`).  Run all pairs with `scripts/run_comparators.sh`, as
described in the README; a missing pair, a missing tool or a failed kernel check is a failure.
Logs are kept under `.lake/comparator-logs/`.

## Continuous integration

`.github/workflows/build.yml` builds the library, rejects any warning in this repository's modules,
runs the axiom audit and `tools/verify.py`.  `.github/workflows/comparator.yml` runs the
comparators, one job per pair; see [`CI_ARTIFACTS.md`](CI_ARTIFACTS.md).
