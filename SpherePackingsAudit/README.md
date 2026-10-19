# SpherePackingsAudit comparator surface

Mathlib-only comparator challenges for the main results of the formalization of *Random walk on
sphere packings and Delaunay triangulations in arbitrary dimension* (Ahmed Bou-Rabee and Ewain
Gwynne).  Each pair lives in its own subdirectory:

| Directory | Paper statement | Checked theorem | Library theorem |
| --- | --- | --- | --- |
| `TheoremA/` | Theorem A, `theorem:convergence-of-rw-trace` | `SpherePackingsAudit.theoremA` | `SpherePackings.theorem_A` |
| `TheoremB/` | Theorem B, both alternatives | `SpherePackingsAudit.theoremB` | `SpherePackings.theorem_B_a`, `SpherePackings.theorem_B_b` |
| `Prop11/` | Proposition 1.1, cell bounds | `SpherePackingsAudit.prop_1_1` | `SpherePackings.prop_1_1` |
| `Prop11TheoremsAB/` | Proposition 1.1, Theorems A and B for Poisson–Voronoi tilings | `SpherePackingsAudit.prop_1_1_theorems_A_B` | `SpherePackings.prop_1_1_theorems_A_B` |
| `Theorem61/` | Theorem 6.1, `theorem:counter-example` | `SpherePackingsAudit.theorem_6_1` | `SpherePackings.theorem_6_1` |
| `Theorem41/` | Theorem 4.1, `theorem:general-clt` | `SpherePackingsAudit.theorem_4_1` | `SpherePackings.theorem_4_1` |

## Design

Each `Challenge.lean` imports only Mathlib, through the vocabulary modules of `Vocabulary/`, states
the theorem, and ends with one `sorry`, the proof being checked.  It is the object of trust: a
reader checks what it says, not how it is proved.

The vocabulary differs from a renamed copy of the declarations because the statements involve
structures (polytopes, tilings, curves modulo time parametrization, networks).  A copy under a new
namespace would be a different type, and the solution would have to transport every structure.
Instead, `Vocabulary/<M>.lean` copies, **verbatim and under their repository names**, the
declarations of the repository module `M` that the statements need (their dependency closure,
through the types and values of definitions, including the lemmas inside definitions), with the
module's namespaces, `open` and `variable` commands, and nothing else.  Each vocabulary module
imports the Mathlib modules of `M` and of the repository modules below it, and the vocabulary copies
of those modules.  The module structure is kept because Lean shares auxiliary proofs within a module:
a single-file copy elaborates some definitions to different, if equivalent, terms.

`Solution.lean` imports the repository itself, restates the theorem with the challenge's bytes, and
proves it by `exact` of the library theorem.  The comparator then checks, constant by constant, that
the repository's declarations in the statement's closure are identical to the challenge's copies,
that the solution proves the challenge's statement, and that it uses only `propext`,
`Classical.choice` and `Quot.sound`.  `comparator.json` enables the nanoda kernel as well.

The vocabulary is generated from the repository by
`lake env lean --run tools/audit/DumpVocabulary.lean <modules> <roots> <dump>` (the dependency dump)
and `python3 tools/audit/build_vocabulary.py <dump>`; `python3 tools/check_vocabulary.py` re-derives
it and fails on any difference.  The challenges and solutions are written by
`python3 tools/audit/make_pairs.py`.

## Reproducing the checks

With the four companion tools built at the revisions in
[`../.github/workflows/comparator.yml`](../.github/workflows/comparator.yml) (`lean4export` must match
the project toolchain, `v4.34.0-rc2`):

```
lake build SpherePackingsAudit
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> COMPARATOR_NANODA=<nanoda_bin> \
  lake env <comparator>/.lake/build/bin/comparator SpherePackingsAudit/<Pair>/comparator.json
```

or all six pairs at once with `scripts/run_comparators.sh` (it reads the same four tool paths from
`COMPARATOR_BIN`, `COMPARATOR_LANDRUN`, `COMPARATOR_LEAN4EXPORT` and `COMPARATOR_NANODA`).  A pass
prints `nanoda kernel accepts the solution`, `Lean default kernel accepts the solution` and
`Your solution is okay!`.  See [`COMPARATOR_RUNS.md`](COMPARATOR_RUNS.md) for the recorded runs.
