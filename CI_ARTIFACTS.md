# Continuous integration: jobs, caches and artifacts

Both workflows run on GitHub-hosted `ubuntu-24.04` runners and build everything from source,
apart from the prebuilt Mathlib oleans fetched by `lake exe cache get`.  The pinned toolchain and
Mathlib are in [`lean-toolchain`](lean-toolchain) and [`lake-manifest.json`](lake-manifest.json);
every download of the toolchain and of the Mathlib cache is retried.

## CI ([`.github/workflows/build.yml`](.github/workflows/build.yml))

One job, on every push to `main` (and on demand):

1. **Build.**  `lake build` of the library, `SpherePackings/` and leobon12's `BouRabeeGwynne/`.
   The step fails on a warning in a `SpherePackings` module and on any `sorry`.  leobon12's files
   are kept unchanged apart from their headers and emit linter warnings under this toolchain, so
   the warning gate applies to this repository's own modules.
2. **Axiom audit.**  `lake env lean SpherePackings/Meta/AxiomsAudit.lean` prints the axioms of the
   seven main theorems, and [`scripts/check_axioms.py`](scripts/check_axioms.py) requires exactly
   `propext`, `Classical.choice` and `Quot.sound` for each, and fails on a missing, unexpected or
   repeated report, on `sorryAx` and on any warning or error.
3. **Registry checks.**  `python3 tools/verify.py`: the SHA-256 pins of the frozen statements and of
   the two paper sources, the coverage of the paper's labels, the generated parts of `README.md`
   and `CORRESPONDENCE.md`, the warning check, the axioms of every registered statement and guard,
   the byte-identity of the comparator vocabulary, and `CERTIFICATE.md`.

**Artifact:** `ci-logs-<commit>`, with `production-build.log`, `axioms-audit.log` and
`verify.log`.  **Cache:** the project's `.lake/build`, saved under a key of the toolchain, the
manifest and the commit, and restored from the most recent entry with the same toolchain and
manifest, so that an ordinary push rebuilds incrementally.  The save runs even when a later step
fails, so that a failed build still banks its completed modules.

## Comparator audit ([`.github/workflows/comparator.yml`](.github/workflows/comparator.yml))

On pushes to `main` that change Lean sources, the build configuration, the audit pairs or the
workflow, and on demand (the `pairs` input selects a subset; the default is all six).

1. **Plan** selects the pairs: `TheoremA`, `TheoremB`, `Prop11`, `Prop11TheoremsAB`, `Theorem61`
   and `Theorem41` (see [`SpherePackingsAudit/README.md`](SpherePackingsAudit/README.md)).
2. **Build** runs `lake build SpherePackingsAudit` once (the library, the Mathlib-only vocabulary,
   and the challenge and solution modules) and saves `.lake/build` under the exact commit.
3. **One job per pair** restores that build (a cache miss is an error: there is no fallback),
   builds or restores the four verification tools at the revisions pinned in the workflow
   (`leanprover/comparator`, `leanprover/lean4export` at the project's toolchain, the `nanoda`
   kernel and the `landrun` sandbox), and runs
   [`scripts/run_comparators.sh`](scripts/run_comparators.sh) on its pair.  The script checks
   that every configuration permits exactly the three standard axioms and enables the nanoda
   kernel, runs the comparator, and requires the verdicts `nanoda kernel accepts the solution`,
   `Lean default kernel accepts the solution` and `Your solution is okay!`.
4. **Every comparator pair passed** fails unless every pair job succeeded.

**Artifacts:** `comparator-build-<commit>` (the build log) and `comparator-<pair>-<commit>` (the
comparator log of each pair).  **Caches:** the project build of the run, and the built tools,
keyed by their four revisions.

## Why no prebuilt bundle

The whole library builds within one hosted job, so the comparator jobs reuse the build of the same
run rather than a separately produced bundle of compiled files.  The toolchain
`v4.34.0-rc2` bundles neither an exporter nor external kernels; the comparator therefore runs with
separately built tools rather than `lake comparator` and the kernels of a toolchain.  The trust in
a comparator result rests on its kernel replay and its comparison of the dependency closures, not
on the cached build.  The runs recorded on a local machine, with the same tool revisions, are in
[`SpherePackingsAudit/COMPARATOR_RUNS.md`](SpherePackingsAudit/COMPARATOR_RUNS.md).
