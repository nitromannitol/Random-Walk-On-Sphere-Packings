# Random walk on sphere packings and Delaunay triangulations in arbitrary dimension

[![CI](https://github.com/nitromannitol/Random-Walk-On-Sphere-Packings/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Random-Walk-On-Sphere-Packings/actions/workflows/build.yml)
[![Comparator audit](https://github.com/nitromannitol/Random-Walk-On-Sphere-Packings/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Random-Walk-On-Sphere-Packings/actions/workflows/comparator.yml)

A Lean 4 formalization of the paper

> Ahmed Bou-Rabee and Ewain Gwynne,
> [*Random walk on sphere packings and Delaunay triangulations in arbitrary dimension*](https://arxiv.org/abs/2405.11673),
> arXiv:2405.11673 (version 2).

The paper proves that random walk on a tiling of `ℝᵈ` by convex cells, with a natural choice of
conductances, converges to Brownian motion as the cells shrink, under mild regularity conditions.
Delaunay triangulations and sphere packings are examples, and the discrete Dirichlet problem
converges as well. Every labelled theorem, lemma and proposition of the paper is proved in Lean with
only the standard axioms, and no result from the literature is assumed. Where a printed statement is
false or not well defined, the Lean statement follows a corrected version of the paper.

The development is built on [mathlib](https://github.com/leanprover-community/mathlib4) and on
Leonardo Bonanno's (leobon12) formalization
[`lean-formalizations/results/bou-rabee-gwynne`](https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne),
which proves Theorem A and Theorem B(a); see [Acknowledgments](#acknowledgments). This
repository adds Theorem B(b), Proposition 1.1, Sections 5 and 6, and the statements of the results
of Sections 2 to 4 in the form of the paper.

## The paper

Cover a set `D ⊆ ℝᵈ` by convex polytopes `P_v` with disjoint interiors, each with a marked point
`v` in its interior. Two vertices `v` and `w` are neighbours if their cells meet in a facet of
dimension `d − 1`. The tiling is *orthogonal* if, for all neighbours, the vector `w − v` is
orthogonal to the common facet. Voronoi tessellations, whose dual graphs are the Delaunay
triangulations, and tangency graphs of sphere packings are orthogonal tilings.

The random walk on an orthogonal tiling jumps from `v` to a neighbour `w` with probability
proportional to the conductance `a(v, w) = vol_{d−1}(P_v ∩ P_w) / ‖w − v‖`. With these weights
the expected step of the walk is zero at every vertex whose cell is surrounded by the cells of its
neighbours (Lemma 2.2). The *mesh* `ε_n` of a tiling `G_n` is the largest diameter of its cells.
The paper's regularity hypotheses are mild; one of the following suffices:

- **(I)** planarity, `d = 2`;
- **(II)** no exponentially small tiles: the smallest tile of `G_n` has volume at least
  `exp(−o(ε_n⁻¹))`;
- **(III)** polynomial diameters: for some `α > 0`, every tile has
  `diam(P_v) = O(max_w ‖w − v‖^α vol_{d−1}(P_v ∩ P_w)^α)`, the maximum over the neighbours `w` of `v`.

Curves are compared modulo time parametrization:
`d(φ₁, φ₂) = inf_ψ sup_t |φ₁(t) − φ₂(ψ(t))|`, the infimum over increasing homeomorphisms `ψ`
between the time intervals. The main results are:

- **Theorem A.** As the mesh tends to zero, the walk stopped on leaving a bounded Lipschitz domain
  converges in law to Brownian motion stopped on leaving it, modulo time parametrization.
- **Theorem B.** Under the same hypotheses, the discrete harmonic extensions of a harmonic
  function converge to it uniformly.
- **Proposition 1.1.** The Voronoi tessellations of Poisson processes satisfy (II), so Theorems A
  and B apply to them.
- **Theorem 4.1.** Nearest-neighbour walks for which the discrete Dirichlet problem converges in
  balls (the paper's Assumption D) converge to Brownian motion modulo time parametrization.
- **Theorem 6.1.** In every dimension `d ≥ 3` there is a sphere packing of bounded degree on which
  *simple* random walk does not converge to Brownian motion.

Precisely, as in the corrected paper:

**Theorem A.** Let `U ⊂ ℝᵈ` be a bounded Lipschitz domain with `closure U ⊂ interior D`, and let
`G_n` be orthogonal tilings of `D`. For `z ∈ D` let `zⁿ` be a vertex of `G_n` nearest to `z`.
Assume that `ε_n + sup_{z ∈ D} ‖zⁿ − z‖ → 0` and that (I), (II) or (III) holds. Then, uniformly in
`z ∈ U`, the linearly interpolated walk started at `zⁿ` and stopped on leaving `U` converges in law
to standard Brownian motion started at `z` and stopped on leaving `U`.

**Theorem B.** Let `U` be a bounded domain with `closure U ⊂ interior D`, let `h_C` be harmonic on
`U`, and let `G_n` satisfy the hypotheses of Theorem A. Let `h_Dⁿ` be the discrete harmonic
function on the vertices in `U` with boundary values given by `h_C`. Then
`sup_{z ∈ V_n[U]} |h_Dⁿ(z) − h_C(z)| → 0` in either of two cases:

- (a) `h_C` is harmonic near `closure U`, and the boundary value at `v` is `h_C(v)`;
- (b) `U` is Lipschitz and `h_C` is continuous on `closure U`, and the boundary value at `v` is
  `h_C` at a nearest point of `closure U`.

**Proposition 1.1.** Let `U` be a bounded domain, and let `μ` satisfy
`r^{β⁺} ≤ μ(B_r(z)) ≤ r^{β⁻}` for all small `r` and all `z` in an open set `W ⊇ closure U`. Let `Λ_m`
be a Poisson point process of intensity `m μ`. Almost surely, for all large `m`, every Voronoi cell
`C_s` of `Λ_m` that meets `U` satisfies `B_{m^{−8/β⁻}}(s) ⊂ C_s ⊂ B_{m^{−1/(3β⁺)}}(s)`. In
particular, Theorem B and, if `U` is Lipschitz, Theorem A hold as `m → ∞` for the tilings of a
neighbourhood of `closure U` by the Voronoi cells that meet it.

**Theorem 4.1.** Assume Assumption D: for every ball `B` centred in a neighbourhood `B_δ(D)` of `D`,
intersected with that neighbourhood, the vertices approximate `B`, and the discrete Dirichlet
problem in `B` converges uniformly for data harmonic near `B`. Let `U ⊂ D` be a bounded
Lipschitz domain. Then the Prokhorov distance between the law of the walk started at `zⁿ`, stopped
on leaving `U`, and that of Brownian motion started at `z`, stopped on leaving `U`, tends to `0`
uniformly in `z ∈ U`.

**Theorem 6.1.** For every `d ≥ 3` there is a sphere packing in `ℝᵈ` with radii `1` and `1/2`, each
sphere tangent to boundedly many others, on which simple random walk does not converge to
Brownian motion modulo time parametrization.

## The main theorems in Lean

The main theorems are in [`SpherePackings/MainTheorems.lean`](SpherePackings/MainTheorems.lean).
Each restates, and is proved by, the corresponding statement in
[`SpherePackings/Frozen/`](SpherePackings/Frozen/).
Theorem A and Theorem B(a) are proved by Leonardo Bonanno's code under `BouRabeeGwynne/` (see
[Copied code](#copied-code)); the others are proved in this repository.

| Paper | Lean declaration |
| --- | --- |
| Theorem A | `SpherePackings.theorem_A` |
| Theorem B(a) | `SpherePackings.theorem_B_a` |
| Theorem B(b) | `SpherePackings.theorem_B_b` |
| Proposition 1.1, the cell bounds | `SpherePackings.prop_1_1` |
| Proposition 1.1, Theorems A and B for Poisson–Voronoi tilings | `SpherePackings.prop_1_1_theorems_A_B` |
| Theorem 4.1 | `SpherePackings.theorem_4_1` |
| Theorem 6.1 | `SpherePackings.theorem_6_1` |

How to read the statements:

- `Euc d` is `EuclideanSpace ℝ (Fin d)`. The tilings are a `BouRabeeGwynne.TilingSequence`, and the
  nearest vertices a `BouRabeeGwynne.NearestVertexData` with its `ApproximationCondition`, the
  hypothesis `ε_n + sup ‖zⁿ − z‖ → 0`.
- The collar `closure U ⊆ interior D` is `BouRabeeGwynne.HasAmbientCollar`, and the disjunction of
  (I), (II) and (III) is `BouRabeeGwynne.PaperRegularity`.
- Theorem A constructs a standard Brownian law (`BouRabeeGwynne.IsStandardBrownianLaw`). It shows
  that Brownian motion started in `U` leaves `U` almost surely, and that the Lévy–Prokhorov
  distance between the two stopped laws is eventually below every `η > 0`, for all `z ∈ U`.
- The conclusion `BouRabeeGwynne.DirichletApproximationTarget` of Theorem B also asserts that, for
  all large `n`, the discrete Dirichlet problem has a unique solution. In part (b) the nearest
  points are any choice (`BouRabeeGwynne.NearestClosureBoundaryChoices`). The statement shows that
  choices exist, that they lie on the boundary of `U`, and that, for all large `n`, they lie within
  twice the mesh of their vertices.
- In Proposition 1.1 the mass bounds are `SpherePackings.HolderMassBounds μ W β⁺ β⁻`. Only the
  points in `W` are assumed to form a Poisson point process (`SpherePackings.IsPoissonPointProcess`),
  of intensity `m μ` restricted to `W`. The second part also assumes that every `Λ_m` is locally
  finite.
- Theorem 4.1 holds for any nearest-neighbour walks on graphs in `ℝᵈ`
  (`SpherePackings.NearestNeighbourWalk`) under Assumption D as printed (`SpherePackings.AssumptionD`).
  It adds that, for all large `n`, the walk leaves the vertices in `U` almost surely.
- Theorem 6.1 produces a `SpherePackings.SpherePacking` with a sphere centred at the origin. The
  walk from there, rescaled by `1/n` and stopped on leaving the unit ball, does not converge to
  Brownian motion stopped on leaving the unit ball. In dimension three every sphere is also covered
  (`SpherePackings.SpherePacking.Covered`).

## All numbered results

Each row gives the Lean declaration in [`SpherePackings/Frozen/`](SpherePackings/Frozen/) that
proves the result, whether it is the printed statement or the corrected one, and who proved it.
[`CORRESPONDENCE.md`](CORRESPONDENCE.md#node-table) gives a note on the formulation of each.

<!-- STATUS-BEGIN (generated by tools/sync_docs.py) -->

The paper has 20 labelled theorems, lemmas and propositions.  Theorem B, Proposition 1.1, Theorem
3.3 and Lemma 5.1 are stated in two parts, so the table has 24 rows.  All 24 statements are proved,
6 as printed and 18 as in the corrected paper.  Every proof uses only Lean's three standard axioms
`propext`, `Classical.choice` and `Quot.sound`.  This paragraph and the table are generated from
`ledger/manifest.yaml` by `python3 tools/sync_docs.py`.

<!-- STATUS-END -->

<!-- PAPER-MAP-BEGIN (generated by tools/sync_docs.py) -->

| Paper | Lean declaration | Content | Form | Proved by |
|---|---|---|---|---|
| [Theorem A](paper/rw-spheres.tex#L259) | [SpherePackings.Frozen.theoremA](SpherePackings/Frozen/TheoremA.lean#L25) | Convergence of random walk | corrected | leobon12 |
| [Theorem B(a)](paper/rw-spheres.tex#L297) | [SpherePackings.Frozen.theoremB_a](SpherePackings/Frozen/TheoremBa.lean#L18) | Convergence of the Dirichlet problem, data harmonic near `closure U` | corrected | leobon12 |
| [Theorem B(b)](paper/rw-spheres.tex#L297) | [SpherePackings.Frozen.theoremB_b](SpherePackings/Frozen/TheoremBb.lean#L21) | Convergence of the Dirichlet problem, data continuous on `closure U` | corrected | this repository |
| [Proposition 1.1](paper/rw-spheres.tex#L371) | [SpherePackings.Frozen.prop11_cells](SpherePackings/Frozen/Prop11Cells.lean#L24) | Voronoi cells of Poisson processes lie between two balls | corrected | this repository |
| [Proposition 1.1](paper/rw-spheres.tex#L378) | [SpherePackings.Frozen.prop11_theoremAB](SpherePackings/Frozen/Prop11TheoremAB.lean#L20) | Theorems A and B for Poisson–Voronoi tilings | corrected | this repository |
| [Lemma 2.1](paper/rw-spheres.tex#L633) | [SpherePackings.Frozen.lemma21FiniteDegrees](SpherePackings/Frozen/Lemma21FiniteDegrees.lean#L20) | Discrete divergence theorem | corrected | this repository |
| [Lemma 2.2](paper/rw-spheres.tex#L657) | [SpherePackings.Frozen.lemma22_affine_kernel](SpherePackings/Frozen/Lemma22AffineKernel.lean#L18) | Affine functions are discrete harmonic | corrected | this repository |
| [Lemma 2.3](paper/rw-spheres.tex#L684) | [SpherePackings.Frozen.lemma23_dual_variational](SpherePackings/Frozen/Lemma23DualVariational.lean#L20) | Dual variational principle | as printed | leobon12 (paper form here) |
| [Lemma 2.4](paper/rw-spheres.tex#L739) | [SpherePackings.Frozen.lemma24_dual_volume](SpherePackings/Frozen/Lemma24DualVolume.lean#L16) | Volume of the dual polytope | as printed | leobon12 |
| [Lemma 2.5](paper/rw-spheres.tex#L769) | [SpherePackings.Frozen.lemma25_dual_coverage](SpherePackings/Frozen/Lemma25DualCoverage.lean#L19) | Dual polytopes cover the cells | corrected | this repository (from leobon12) |
| [Proposition 2.6](paper/rw-spheres.tex#L822) | [SpherePackings.Frozen.prop26_energy](SpherePackings/Frozen/Prop26Energy.lean#L27) | Energy bound | corrected | this repository (from leobon12) |
| [Lemma 3.1](paper/rw-spheres.tex#L937) | [SpherePackings.Frozen.lemma31_poincare](SpherePackings/Frozen/Lemma31Poincare.lean#L23) | Poincaré-type inequality | corrected | leobon12 |
| [Proposition 3.2](paper/rw-spheres.tex#L980) | [SpherePackings.Frozen.prop32_columns](SpherePackings/Frozen/Prop32Columns.lean#L26) | Closeness on columns | corrected | this repository (from leobon12) |
| [Theorem 3.3](paper/rw-spheres.tex#L1030) | [SpherePackings.Frozen.theorem33_planar](SpherePackings/Frozen/Theorem33Planar.lean#L31) | Planar bound | corrected | this repository (from leobon12) |
| [Theorem 3.3](paper/rw-spheres.tex#L1050) | [SpherePackings.Frozen.theorem33_rate](SpherePackings/Frozen/Theorem33Rate.lean#L29) | Planar rate `C ε^{2/3}` | corrected | this repository (from leobon12) |
| [Lemma 3.5](paper/rw-spheres.tex#L1128) | [SpherePackings.Frozen.lemma35_weighted_energy](SpherePackings/Frozen/Lemma35WeightedEnergy.lean#L16) | Weighted gradient-energy estimate | as printed | leobon12 |
| [Theorem 3.6](paper/rw-spheres.tex#L1147) | [SpherePackings.Frozen.theorem36_rate](SpherePackings/Frozen/Theorem36Rate.lean#L33) | General dimension, small cells | corrected | this repository (from leobon12) |
| [Theorem 3.7](paper/rw-spheres.tex#L1314) | [SpherePackings.Frozen.theorem37_rate](SpherePackings/Frozen/Theorem37Rate.lean#L33) | General dimension, decay hypothesis | corrected | this repository (from leobon12) |
| [Theorem 4.1](paper/rw-spheres.tex#L1481) | [SpherePackings.Frozen.theorem41](SpherePackings/Frozen/Theorem41.lean#L24) | Central limit theorem under Assumption D | as printed | this repository (from leobon12's proof of Theorem A) |
| [Proposition 4.2](paper/rw-spheres.tex#L1511) | [SpherePackings.Frozen.prop42_general](SpherePackings/Frozen/Prop42General.lean#L23) | Convergence of harmonic measure | corrected | this repository |
| [Lemma 5.1(a)](paper/rw-spheres.tex#L1627) | [SpherePackings.Frozen.lemma51a_inner](SpherePackings/Frozen/Lemma51Inner.lean#L18) | Inner balls of Voronoi cells | corrected | this repository |
| [Lemma 5.1(b)](paper/rw-spheres.tex#L1635) | [SpherePackings.Frozen.lemma51b_outer](SpherePackings/Frozen/Lemma51Outer.lean#L22) | Outer balls of Voronoi cells | corrected | this repository |
| [Lemma 5.2](paper/rw-spheres.tex#L1650) | [SpherePackings.Frozen.lemma52_dual_polytope](SpherePackings/Frozen/Lemma52DualPolytope.lean#L14) | Polar of a perturbed cross-polytope | as printed | this repository |
| [Theorem 6.1](paper/rw-spheres.tex#L1791) | [SpherePackings.Frozen.theorem61_counterexample](SpherePackings/Frozen/Theorem61Counterexample.lean#L26) | Simple random walk counterexample | as printed | this repository |

<!-- PAPER-MAP-END -->

The hypotheses of the main theorems can be met: lattice Voronoi tilings of a ball satisfy those of
Theorems A and B (`SpherePackings.exists_lattice_tilingSequence`) and of Theorem 4.1
(`SpherePackings.theorem41_hypotheses_satisfiable`).

## Corrections

The Lean statements follow a corrected version of the arXiv v2 source,
[`paper/rw-spheres-corrected.tex`](paper/rw-spheres-corrected.tex). Each change is marked in the
source by a comment `% CORRECTION n` or `% CLOSE n`, and the section *Corrections to the
published version* of the corrected paper summarizes them in nine items. For each changed
statement, [`CORRESPONDENCE.md`](CORRESPONDENCE.md) says whether the published version is false, with a
counterexample, or open. The counterexamples are informal arguments, not formalized in Lean.
[`GAP-CHECKS.md`](GAP-CHECKS.md) records independent checks of four claims about the printed paper.

- **Theorems A and B, Sections 2 to 4.** The theorems assume `closure U ⊆ interior D`, and the
  estimates of Sections 2 and 3 assume *complete* cells: finitely many neighbours, and every
  boundary point of the cell in the cell of a neighbour. Without these the published statements
  are false, for example on a square grid of a rectangle.
- **Theorem B(b).** The boundary value at a vertex is taken at a nearest point of `closure U`. The
  published prescription, the nearest point of the cell `P_v` at which `h_C` is defined, need not
  exist.
- **Proposition 1.1.** The mass bounds are assumed on a neighbourhood `W` of `closure U`. With the
  bounds on `U` only, the statement is false.
- **Lemmas 2.1 and 2.5.** Lemma 2.1 needs finite degrees. The first inclusion of Lemma 2.5 is false
  as printed and is replaced by a covering of the cells of `V[U]`.
- **Propositions 2.6 and 3.2.** Their constant `M` also bounds the Taylor remainders along the
  edges. Both published versions are false, even for complete cells.
- **Theorem 3.3.** The displayed bound is changed, and the rate holds for `ε ≤ 1/2`. With a
  constant uniform over all meshes the published rate is false.
- **Theorems 3.6 and 3.7.** Their constant bounds the cell Hessian and the Taylor remainders on
  the internal edges. The published proofs have gaps; the proofs here use Bonanno's corrected
  iteration.
- **Proposition 4.2.** It holds for balls whose closure lies in `B_δ(D)`, and is false otherwise.
- **Lemma 5.1.** Part (a) tests the grid points whose cube meets `U`; as printed it is false. Part
  (b) is stated with constants depending on `d`. The printed radius `2k` is also proved for every
  `d ≤ 12` (`SpherePackings.Voronoi.geometric_constraint_outer_two`); it fails for every `d ≥ 13`.
- **Theorem 6.1.** The statement is unchanged. For `d ≥ 4` some small spheres of the printed
  packing touch no big sphere, so the small spheres are placed at even coordinates beyond the
  third; only the proof changes.

Two questions about the printed statements are open: whether Theorems 3.3, 3.6 and 3.7 hold with
the published cell Hessian constant alone, and whether the published linear bound of Theorem 3.3
holds. Neither is needed for the Lean statements.

## Scope

- **Edges.** Every contact of dimension `d − 1` of two cells is an edge, as the paper reads it, and
  orthogonality is required on all of them.
- **The formal objects.** Tilings, conductances, the discrete Dirichlet problem, curves modulo time
  parametrization, the stopped walk and the Brownian laws are Bonanno's definitions. The
  conventions are listed in [`CORRESPONDENCE.md`](CORRESPONDENCE.md#conventions).
- **Nearest vertices.** `zⁿ` is any nearest vertex; the paper's lexicographic tie-breaking is one
  choice.
- **Assumption D** is a hypothesis, formalized as printed. Test functions are given on `ℝᵈ`, the
  existence of the discrete Dirichlet solutions is not assumed, and (4.2) is required of every
  solution.
- **Total definitions.** Lean's real-valued definitions are total, so the statements carry the
  positivity, finiteness and nonemptiness hypotheses they need. [`AUDIT.md`](AUDIT.md) records a
  review of every definition for such junk values.
- **Not formalized.** Remarks 1.2 and 3.4, the examples of Section 1.2 other than Voronoi
  tessellations, and the open problems. No Lean example constructs a Poisson point process.

## Checking the proofs

- **No `sorry`.** The library has none. `tools/check_manifest.py` fails on any `sorry`, `admit`,
  `sorryAx`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `opaque` and similar
  tokens under `SpherePackings/` and `BouRabeeGwynne/`. Each of the six comparator challenges
  contains one intentional `sorry` at the statement, which the matching solution proves.
- **Standard axioms only.** [`SpherePackings/Meta/AxiomsAudit.lean`](SpherePackings/Meta/AxiomsAudit.lean)
  prints the axioms of the main theorems. `tools/check_axioms.py` checks those of every statement in
  the table above and of seven supporting facts about the model, and fails on anything beyond
  `propext`, `Classical.choice` and `Quot.sound`. [`CERTIFICATE.md`](CERTIFICATE.md) records the
  result.
- **Pinned statements.** Each statement in the table lies between `-- FROZEN-STATEMENT-BEGIN` and
  `-- FROZEN-STATEMENT-END`. The SHA-256 of that text, and of both paper sources, is pinned in
  `ledger/manifest.yaml` and checked by `tools/check_manifest.py`.
- **Independent check of the statements.** The main theorems are restated in six comparator
  challenges under [`SpherePackingsAudit/`](SpherePackingsAudit/README.md): Theorem A, Theorem B
  (both parts), the two parts of Proposition 1.1, Theorem 4.1 and Theorem 6.1. The challenges import
  only Mathlib and vocabulary modules that copy the needed declarations verbatim;
  `tools/check_vocabulary.py` re-derives the copies. [leanprover/comparator](https://github.com/leanprover/comparator)
  checks that each solution proves the challenge statement with only the permitted axioms, with
  the Lean kernel and the independent nanoda kernel.
- **The copied code.** [`AUDIT.md`](AUDIT.md) records a review of the modules copied or adapted
  from Bonanno's formalization, for definitions that do not mean what they say, vacuous hypotheses
  and statements weaker than claimed. The nonvacuity examples in `SpherePackings/Audit/Nonvacuity/`
  build with the library.
- **Continuous integration.** The **CI** workflow builds the library, rejects any warning in this
  repository's modules and any `sorry`, checks the axiom reports and runs `tools/verify.py`. The
  **Comparator audit** workflow checks the six pairs, one job per pair; see
  [`CI_ARTIFACTS.md`](CI_ARTIFACTS.md).

`SpherePackings/` and `SpherePackings.lean` contain 182 Lean files with 24,271 lines. Bonanno's
`BouRabeeGwynne/` adds 319 files with 37,349 lines, including 21 files vendored from Rémy Degenne's
Brownian-motion and Kolmogorov-extension projects. The comparator sources are 37 files with 2,642
lines.

## Building

Install [elan](https://github.com/leanprover/elan). The toolchain, Lean `v4.34.0-rc2`, is pinned in
[`lean-toolchain`](lean-toolchain), and Lake fetches Mathlib at the commit
`a4c8ef0a69f52ec80525d5086bb3542f4660faaf`, the pins of Bonanno's release, recorded in
[`lakefile.lean`](lakefile.lean) and [`lake-manifest.json`](lake-manifest.json).

```bash
lake exe cache get   # prebuilt Mathlib
lake build           # the library
lake env lean SpherePackings/Meta/AxiomsAudit.lean 2>&1 | tee .lake/axioms-audit.log
python3 scripts/check_axioms.py .lake/axioms-audit.log   # the axiom reports of the main theorems
lake build SpherePackingsAudit                           # the comparator pairs
```

`import SpherePackings` loads the main theorems and what they use.

The checkers need Python 3.10 or newer and PyYAML (`python3 -m pip install -r tools/requirements.txt`).
`python3 tools/verify.py` runs them all and stops at the first failure:

| Command | What it checks |
|---|---|
| `python3 tools/check_manifest.py` | the pinned SHA-256 of every statement and of the paper; no forbidden token in the library; every file of `BouRabeeGwynne/` names its source |
| `python3 tools/check_coverage.py` | every labelled result of `paper/rw-spheres.tex` is in the manifest or listed as not formalized (a review aid, not a proof of equivalence) |
| `python3 tools/sync_docs.py` | the manifest and the generated parts of this file and of `CORRESPONDENCE.md` are current (`--write` regenerates them) |
| `python3 tools/check_warnings.py` | `lake build SpherePackings` emits no warning in this repository's modules |
| `python3 tools/check_axioms.py` | every statement of the manifest uses only the three standard axioms |
| `python3 tools/check_vocabulary.py` | the comparator vocabulary modules are verbatim copies of the repository declarations |
| `python3 tools/certificate.py` | regenerates `CERTIFICATE.md` after a successful axiom audit (`--check` compares) |

To build the paper, run `pdflatex` twice on `rw-spheres.tex` or `rw-spheres-corrected.tex` in
[`paper/`](paper/).

## Running the comparators

Each pair has a configuration `SpherePackingsAudit/<Pair>/comparator.json`, which permits exactly
`propext`, `Classical.choice` and `Quot.sound` and enables the nanoda kernel. The pinned toolchain
does not bundle an exporter or external kernels. Build `leanprover/comparator`,
`leanprover/lean4export` (at the project's toolchain), `ammkrn/nanoda_lib` and `Zouuup/landrun` at
the revisions pinned in [`comparator.yml`](.github/workflows/comparator.yml), then run

```bash
COMPARATOR_BIN=<comparator> COMPARATOR_LANDRUN=<landrun> \
COMPARATOR_LEAN4EXPORT=<lean4export> COMPARATOR_NANODA=<nanoda_bin> \
  ./scripts/run_comparators.sh            # or: --pair TheoremA
```

Logs are kept under `.lake/comparator-logs/`. Recorded local runs are in
[`SpherePackingsAudit/COMPARATOR_RUNS.md`](SpherePackingsAudit/COMPARATOR_RUNS.md).

CI runs on pushes to `main` that change anything but the paper PDFs, `CITATION.cff`,
`CONTRIBUTING.md` and `CI_ARTIFACTS.md`. The comparator audit runs on pushes that change Lean
sources, `SpherePackingsAudit/`, `scripts/run_comparators.sh` or the build configuration. Both can
be started manually from the [Actions page](https://github.com/nitromannitol/Random-Walk-On-Sphere-Packings/actions).
See [`CONTRIBUTING.md`](CONTRIBUTING.md) for build conventions.

## Repository layout

```text
SpherePackings.lean    the root module
SpherePackings/
  MainTheorems.lean    the main theorems, stated in full
  Frozen/              the statements of the labelled results, one per file
  General/             Markov chains on subsets of ℝ^d and the walk/Brownian coupling behind Theorem 4.1
  Support/             the proofs
  Audit/Nonvacuity/    nonvacuity examples
  Meta/                AxiomsAudit.lean
BouRabeeGwynne/        Bonanno's formalization of Theorems A and B(a), copied (see Copied code)
SpherePackingsAudit/   the Mathlib-only comparator challenges, solutions and vocabulary
paper/                 the arXiv v2 source, the corrected paper, figures, bibliography and PDFs
ledger/                manifest.yaml (the hash of each statement) and the audit reports
CORRESPONDENCE.md      paper ↔ Lean: conventions, corrections, statement table
GAP-CHECKS.md          the checks of four claims about the printed paper
AUDIT.md               the review of the copied and adapted code
CERTIFICATE.md         the toolchain, and the axioms and hash of each statement
tools/, scripts/       the checkers and generators, the axiom check and the comparator runner
```

## How this was built

The Lean code was written with AI assistance, using models from Anthropic (Claude), under the
direction of Ahmed Bou-Rabee. Every proof is checked by the Lean kernel. Models from OpenAI (GPT)
checked claims about the paper and drafted its corrections. The models, tooling, hardware and
review status are recorded in [`formalization.yaml`](formalization.yaml), following the
[mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml) standard. Theorem A
and Theorem B(a) were formalized by leobon12.

## Copied code

The directory `BouRabeeGwynne/` contains code copied from Leonardo Bonanno's
[`lean-formalizations`](https://github.com/leobon12/lean-formalizations), at commit `cf73d6e`.
This code is copied source, not a dependency: the library builds without that repository.  Every
copied file names its source file and commit in its header; 13 files also add
`omit [Fintype V] in` before declarations that do not use finiteness, and one file drops a
`set_option maxHeartbeats 800000 in` that its proof does not need, as their headers state.
The files under `BouRabeeGwynne/Upstream/` and `BouRabeeGwynne/DyadicExitApprox.lean` were
vendored by Leonardo Bonanno from Rémy Degenne's `brownian-motion` and `kolmogorov_extension4`
projects, under the Apache License 2.0.  [`NOTICE`](NOTICE) gives the details, and
[Acknowledgments](#acknowledgments) lists what the copied code proves.

## Authors and citation

The Lean development is by **Ahmed Bou-Rabee**.  The paper is by Ahmed Bou-Rabee and Ewain
Gwynne.  To cite the formalization, use [`CITATION.cff`](CITATION.cff).

### Acknowledgments

Much of this formalization is based on the formalization of the paper by **Leonardo Bonanno**
(leobon12),
<https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne> (repository
`leobon12/lean-formalizations`, commit `cf73d6e115827859895cbbd3a3556bf602db32d6`).

- **Copied:** all 319 Lean files of `BouRabeeGwynne/`, unchanged apart from a header in each naming its
  source, and, in 13 walk files, `omit [Fintype V] in` before declarations whose proofs do not use
  the finiteness of the state space (so that they apply to infinite graphs), and, in `BrownianNextExit.lean`, one
  removed `set_option maxHeartbeats 800000 in`.  They contain leobon12's statements and proofs of **Theorem A**
  (`BouRabeeGwynne.theoremA_proved`) and **Theorem B(a)** (`BouRabeeGwynne.theoremB_part_a`), the
  statement of **Theorem B(b)** (`BouRabeeGwynne.TheoremBPartBStatement`), and the internal results
  registered here as **Lemma 2.4, Lemma 3.1 and Lemma 3.5**, the qualitative forms of
  **Theorems 3.6 and 3.7** used for Theorem B(a), and **Proposition 4.2** for tilings.  leobon12's
  statement correction (the ambient collar) and reading of the edge rule are adopted throughout.
  The 20 files under `BouRabeeGwynne/Upstream/`, and the excerpt `BouRabeeGwynne/DyadicExitApprox.lean`,
  were vendored by leobon12 from Rémy Degenne's `brownian-motion` and (with Peter Pfaffelhuber)
  `kolmogorov_extension4` projects, with their Apache-2.0 copyright and author lines, which are
  kept (`PROVENANCE.md` in each `Upstream/` directory); `BouRabeeGwynne/BrownianProjectiveLaw.lean`
  adapts the Kolmogorov extension proof.
- **Adapted:** the paper forms of **Lemma 2.3, Lemma 2.5, Propositions 2.6 and 3.2, Theorems 3.3,
  3.6 and 3.7** (Theorem 3.7 through leobon12's corrected iteration), the **Theorem B(b)** proof,
  and **Theorem 4.1** and **Proposition 4.2** for general walks (leobon12's coupling from the proof
  of Theorem A, for an arbitrary kernel) are new files built on leobon12's lemmas; **Lemma 2.2** uses
  leobon12's polytope Gauss–Green identity.  The comparator vocabulary under
  `SpherePackingsAudit/Vocabulary/BouRabeeGwynne/` copies leobon12's declarations verbatim.
- **New here:** Theorem B(b), Proposition 1.1, Lemmas 5.1 and 5.2, Theorem 6.1, Lemma 2.1 and the
  guards.

The verification of leobon12's release (its pinned toolchain and Mathlib, the BouRabeeGwynne part of
its `Certificate.lean`, and its whole-declaration axiom audit, 3,458 declarations with 72,575
reachable) was re-run before the import: it builds with its pinned toolchain
`leanprover/lean4:v4.34.0-rc2` and Mathlib `a4c8ef0`, and Theorems A and B(a) use only `propext`,
`Classical.choice` and `Quot.sound`.

This formalization is built on [Lean 4](https://lean-lang.org) and
[Mathlib](https://github.com/leanprover-community/mathlib4); the comparator audit uses
[`leanprover/comparator`](https://github.com/leanprover/comparator).

## License

The Lean development is licensed under the Apache License 2.0; see [`LICENSE`](LICENSE).  The
paper in [`paper/`](paper/) is posted on arXiv under the Creative Commons Attribution 4.0
International license ([CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)); the corrected
version is a modified version of it, with the changes marked, distributed under the same license.
These licences are not set by the software licence.  The files under `BouRabeeGwynne/Upstream/`
and `BouRabeeGwynne/DyadicExitApprox.lean` come from Rémy Degenne's Brownian-motion and
Kolmogorov-extension projects (see [Acknowledgments](#acknowledgments)) and keep their own
Apache License 2.0 notices; see the `LICENSE` and `PROVENANCE.md` files in
`BouRabeeGwynne/Upstream/BrownianMotion/` and `BouRabeeGwynne/Upstream/KolmogorovExtension/`.
[`NOTICE`](NOTICE) lists the copied code and its sources.
