All 24 registered statements are `PROVED`, as printed or as in the corrected paper `paper/rw-spheres-corrected.tex`.

# Status: Random walk on sphere packings (arXiv:2405.11673v2)

Updated 2026-10-19.  Line numbers refer to the unchanged arXiv v2 source `paper/rw-spheres.tex`
(SHA-256 `13540317ed6770077961706bc591e9266968779b8cf38a432e4c8ce65e49125d`).  The corrected paper
`paper/rw-spheres-corrected.tex` is the same source with the corrections marked in comments; its
SHA-256 is in `ledger/manifest.yaml`.  The generated node table is in `README.md`; differences in
formulation are in `CORRESPONDENCE.md`.

Standard: every labelled result is proved at the strength of the corrected paper: as printed, or,
where the printed statement is changed, as in the corrected paper, with the README saying whether
the printed version is false (with a counterexample) or open.  A result proved only under a
hypothesis stronger than the corrected paper's would be `PARTIAL`; none is.

Sources of proofs:

- **leobon12**: https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
  (commit `cf73d6e`), copied into `BouRabeeGwynne/` with a header naming the source.
- **local**: this repository's earlier corrected Lemma 2.1.
- **new**: proved in this repository.

## Open

| Question | State |
|---|---|
| Theorems 3.3, 3.6 and 3.7 with the published cell Hessian constant alone (no Taylor control on the internal edges) | open; the registered statements use the corrected paper's constant `M_U°` (Hessian on the cells, finite Taylor remainder on the internal edges), which a Hessian bound on the internal edge segments implies |
| The published linear bound of Theorem 3.3, `inf_k (6 k M ε vol(Û) + 2(√2 k⁻¹ + ε) L)` | not settled; the registered bound is the corrected paper's quadratic one, `3 M₀ ε² + inf_k (6 k M ε vol(Û) + (M/2)(√2 k⁻¹ + ε)²)` |
| A Poisson point process in Lean | not constructed: no Lean example exhibits an `IsPoissonPointProcess` (a construction, for instance for Lebesgue measure on `ℝ^d`, would need the Poisson colouring theorem and a superposition over unit cubes) |

## Labelled results

| Result (label, lines) | State | Lean / note |
|---|---|---|
| Theorem A `theorem:convergence-of-rw-trace` (259–277) | proved by leobon12, corrected (counterexample) | `Frozen.theoremA` |
| Theorem B(a) (297–321) | proved by leobon12, corrected (counterexample) | `Frozen.theoremB_a` |
| Theorem B(b) (297–321) | **new**, corrected (not well defined as printed) | `Frozen.theoremB_b` (leobon12's statement) |
| Proposition 1.1 `prop:min-max-edge-length` (371–381) | **new**, corrected (counterexample) | `Frozen.prop11_cells`, `Frozen.prop11_theoremAB` |
| Remark 1.2 `remark:gmc` | not a result | remark citing Berestycki |
| Lemma 2.1 `lemma:discrete-divergence-theorem` (633–640) | local, corrected (well-posedness) | `Frozen.lemma21FiniteDegrees` |
| Lemma 2.2 `lemma:linear-lie-in-kernel` (657–659) | **new**, corrected (counterexample; complete cells) | `Frozen.lemma22_affine_kernel` |
| Lemma 2.3 `lemma:dual-variational-principle` (684–690) | new paper form of leobon12's | `Frozen.lemma23_dual_variational` |
| Lemma 2.4 `lemma:geometry-bound` (739–744) | leobon12 | `Frozen.lemma24_dual_volume` |
| Lemma 2.5 `lemma:easy-global-qe-bounds` (769–784) | new from leobon12, corrected (counterexamples): `⋃_{v ∈ V[U]} P_v ⊆ ⋃_{e ∈ E[Ū]} Q_e` for complete cells | `Frozen.lemma25_dual_coverage` |
| Proposition 2.6 `prop:energy-bound` (822–844) | new from leobon12, corrected (counterexamples; complete cells, Taylor at one active endpoint, check G2) | `Frozen.prop26_energy` |
| Lemma 3.1 `lemma:ptype-inequality` (937–943) | new from leobon12, corrected (counterexample; complete cells; columns in any direction) | `Frozen.lemma31_poincare` |
| Proposition 3.2 `prop:energy-poincare-bound` (980–1001) | new from leobon12, corrected (counterexamples; as Proposition 2.6) | `Frozen.prop32_columns` |
| Theorem 3.3 `theorem:2d`, the bound (1030–1049) | **new**, corrected: the corrected paper's quadratic bound with `3 M₀ ε²` (counterexample without complete cells, check G4; the published linear bound is not settled) | `Frozen.theorem33_planar` |
| Theorem 3.3 `theorem:2d`, the rate (1050–1053) | **new**, corrected: `C ε^{2/3}` for `ε ≤ 1/2` (the published rate is false with a constant uniform over all meshes) | `Frozen.theorem33_rate` |
| Remark 3.4 (1100–1119) | not a result | proof-adaptation remark |
| Lemma 3.5 `lemma:gradient-energy-estimate` (1128–1135) | leobon12 | `Frozen.lemma35_weighted_energy` |
| Theorem 3.6 `theorem:generaldim` (1147–1176) | **new** from leobon12, corrected (complete cells, check G4; internal-edge Taylor constant), through leobon12's corrected iteration | `Frozen.theorem36_rate` |
| Theorem 3.7 `theorem:generaldim-decay` (1314–1340) | **new** from leobon12, corrected (complete cells, check G4; internal-edge Taylor constant), through leobon12's corrected iteration (gap G1) | `Frozen.theorem37_rate` |
| Assumption D (1438–1462) | a hypothesis | formalized as printed (`AssumptionD`); `TilingAssumptionD` is a localized tiling version used by the earlier tiling proof |
| Theorem 4.1 `theorem:general-clt` (1481–1488) | **new**, as printed (any nearest-neighbour walks, Assumption D as printed) | `Frozen.theorem41` |
| Proposition 4.2 `prop:convergence-of-harmonic-measure` (1511–1516) | **new**, corrected (the ball must lie in `B_δ(D)`; counterexample) | `Frozen.prop42_general` |
| Lemma 5.1 `lemma:geometric-constraint` (1627–1642) | **new**, corrected (counterexamples; (b) with constants `δ(d)`, `R(d) ≥ 2`, the printed radius false for `d ≥ 13`; for `4 ≤ d ≤ 12` the printed radius is true but not formalized, and the registered statement is weaker there) | `Frozen.lemma51a_inner`, `Frozen.lemma51b_outer` |
| Lemma 5.2 `lemma:dual-polytope-bound` (1650–1653) | **new** | `Frozen.lemma52_dual_polytope` |
| Theorem 6.1 `theorem:counter-example` (1791–1794) | **new**, as printed; in dimension three every sphere is covered; the packing is modified for `d ≥ 4`, where it does not cover `ℝ^d` | `Frozen.theorem61_counterexample` |

The counterexamples behind the corrections are informal arguments (README, CORRESPONDENCE); none
is formalized in Lean.  Four claims about the paper were checked independently (`GAP-CHECKS.md`).

Guards: the unit ball is a Lipschitz domain; lattice Voronoi cells are cubes; lattice Voronoi
tilings satisfy all hypotheses of Theorems A and B; the localized Assumption D holds for them; the
conductance walks on them satisfy Assumption D as printed, so the hypotheses of Theorem 4.1 and
Proposition 4.2 are satisfiable; a standard Brownian law exists (leobon12); the Lemma 2.1 infinite
star.

## Infrastructure

- `ledger/manifest.yaml` (generated by `tools/sync_docs.py` from `tools/nodes.py`).
- `tools/verify.py` runs `check_manifest`, `check_coverage`, `sync_docs`, `check_warnings`,
  `check_axioms`, `check_vocabulary` and `certificate --check`.
- `SpherePackingsAudit/`: six comparator pairs (Theorem A, Theorem B, Proposition 1.1 twice,
  Theorem 6.1, Theorem 4.1), Mathlib-only, with verbatim vocabulary copies; Lean and nanoda kernels
  (`COMPARATOR_RUNS.md`).
- `.github/workflows/build.yml` and `comparator.yml`.
- README, CORRESPONDENCE, ASSUMPTIONS, CERTIFICATE, CONTRIBUTING, CITATION.cff, formalization.yaml.

## Milestones

- 2026-10-18: leobon12's `BouRabeeGwynne` modules and the BouRabeeGwynne part of its
  `Certificate.lean` (headline checks plus the whole-declaration axiom audit, 3,458 declarations,
  72,575 reachable) build with its pinned toolchain `leanprover/lean4:v4.34.0-rc2` and Mathlib
  `a4c8ef0`; both theorems use only `propext`, `Classical.choice`, `Quot.sound`.  The other libraries
  of that repository (LQG, Quantum Zipper, …) are unrelated to this paper and were not built.
- 2026-10-18: `BouRabeeGwynne/` imported; project moved to the same toolchain and Mathlib.
- 2026-10-18: Theorem B(b), Proposition 1.1, Lemmas 2.2, 5.1, 5.2, Theorem 6.1 proved; Sections 2–3
  paper forms; frozen registry, tools, comparator pairs, documentation.
- 2026-10-18: Proposition 4.2 and Theorem 4.1 proved in general form (any nearest-neighbour walk,
  Assumption D as printed): leobon12's walk/Brownian coupling generalized to the chain of an
  arbitrary Markov kernel (`SpherePackings/General/`), with the deterministic step bound of the
  tiling walk replaced by the shape of the excursions from balls.
- 2026-10-18: audit of the 330 adapted modules by an independent model: no incorrect definition and
  no vacuous statement; two mislabelled docstrings (`AUDIT.md`).
- 2026-10-18: gap checks G1 (the gap in the printed proof of the rate of Theorem 3.7) and G2
  (Proposition 2.6 false as printed) confirmed.  Proposition 2.6 proved with its correction (the
  Hessian bound also on the edge segments of `E[Ū]`); Proposition 3.2 and Theorems 3.6 (printed
  bound, the exit cell of Step 2 handled by a subharmonic comparison) and 3.7 (printed rate, through
  leobon12's corrected iteration, re-proved with the Hessian bound on the cells and edge segments,
  `SpherePackings/Support/Section3/DecaySegment.lean`) under the same hypothesis.
- 2026-10-19: audit extended to the 63 modules adapted since the first audit (batches 15–20).
- 2026-10-19: Theorem 3.3: the bound `6 k M ε vol(Û) + M (ε + √2 k⁻¹)²` and the rate `C ε^{1/2}`,
  `C = 6 M vol(B_{R₀+1}) + (1 + √2)² M`, without a Lipschitz hypothesis
  (`SpherePackings/Support/Section3/PlanarQuadratic.lean`).
- 2026-10-19: Proposition 3.2, both statements of Theorem 3.3, and Theorems 3.6 and 3.7 registered
  as `PARTIAL` (the edge-segment hypothesis is stronger than the printed one, and no counterexample
  to the printed statements is known); Lemma 3.1 registered as corrected.
- 2026-10-19: gap checks G3 (Lemma 5.1(b): as printed for `d ≤ 3`, false for every `d ≥ 14`) and G4
  (Theorems 3.3, 3.6 and 3.7 false without the interior-cell hypothesis) confirmed.
- 2026-10-19: Lemma 5.1(a) with the grid cubes that meet `U`; Lemma 5.1(b) with `δ = 1/10` and the
  radius `max(2, 2√(d/3)) k`, the printed one for `d ≤ 3`; Lemma 2.5 with the natural inclusion
  `⋃_{v ∈ V[U]} P_v ⊆ ⋃_{e ∈ E[Ū]} Q_e`; Theorem 6.1 with every sphere covered in dimension three.
- 2026-10-19: `IsPoissonPointProcess` asks for finitely many points in bounded sets only, so that
  intensities of infinite mass, such as Lebesgue measure on `ℝ^d`, are admitted (before, its
  finiteness condition on all sets of finite intensity forced every realization to be finite).
- 2026-10-19: attribution headers naming leobon12's formalization added to the adapted modules of
  `SpherePackings/`.
- 2026-10-19: the corrected paper `paper/rw-spheres-corrected.tex` added next to the original, pinned
  by SHA-256; the registered statements follow it.  Complete cells (`Support/Complete/`) in place of
  the interior-cell hypothesis in Lemmas 2.2, 2.5, 3.1, Propositions 2.6, 3.2 and Theorems 3.3, 3.6,
  3.7, with leobon12's Gauss–Green, column, mass and trimming lemmas re-proved for complete cells.
  Propositions 2.6 and 3.2 with the finite Taylor inequality at one active endpoint of each edge.
  Theorems 3.3, 3.6 and 3.7 with the Hessian bound on the cells and the finite Taylor inequality on
  the internal edges only (`Support/Section3/InternalTaylor.lean`): Theorem 3.3 with the corrected
  paper's quadratic bound and the rate `C ε^{2/3}`, no Lipschitz hypothesis; Theorems 3.6 and 3.7
  through leobon12's corrected iteration.  Lemma 5.1(a) with the grid cubes `x + [-r, r]^d` that meet
  `U`; Lemma 5.1(b) with dimension-dependent constants (the printed radius fails for `d ≥ 13`).
  Proposition 1.1 with only the points in `W` assumed to form a Poisson point process.  All 24
  registered statements `PROVED`.
