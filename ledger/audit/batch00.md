# Audit batch 0
| Module | Verdict | Summary |
|---|---|---|
| BouRabeeGwynne.AbsorbingExcursionKernel | OK | Generic selector/absorbing kernels; all maps total, no junk values. |
| BouRabeeGwynne.DiscretePDEAlgebra | NOTE | `energy` is half the paper's Dirichlet energy 𝒟(f,A): it sums each edge once, the paper sums directed edges. Constant factor 2 only. |
| BouRabeeGwynne.StoppedWalk | NOTE | Transition rows are the paper's p(w,v) and absorption. A zero-conductance interior row is junk (zero), unreachable because all uses assume `hpos`. |
| BouRabeeGwynne.FiniteDirichlet | OK | Accessibility, Dirichlet problem, maximum principle, uniqueness and stability match; accessibility criterion's hypothesis satisfiable (compiled). |
| BouRabeeGwynne.FiniteExit | OK | Survival probability is P(τ > n) by absorption; finite exit a.s. under accessibility. |
| BouRabeeGwynne.CurveSpace | OK | Fréchet distance is the infimum over increasing homeomorphisms of the supremal error (paper eq. cmp-topology); quotient is the metric curve space. |
| BouRabeeGwynne.LocalGeometry | OK | Mesh-distance lemmas; every `toReal` use is guarded by `mesh ≠ ∞`. |
| BouRabeeGwynne.LocalRegion | OK | V[U], ∂V[U], \bar V[U] match the paper; finiteness lemmas; guards as above. |
| BouRabeeGwynne.FacetMeasure | OK | Facet area positive and finite for adjacent cells (lemmas only). |
| BouRabeeGwynne.DiscretePDE | OK | `conductanceReal` = (1.1), `discreteLaplacian` = (1.4), `SolvesDirichlet` and `DirichletError` = discrete Dirichlet problem and (1.5). |
| BouRabeeGwynne.TilingNetwork | OK | Restriction to the closed region is faithful: interior neighbours lie in `closedVertices`. Uniqueness is only on the closed region, as documented. |
| BouRabeeGwynne.PaperObjects | NOTE | `RegularityII` uses `mesh.toReal` (⊤ ↦ 0), so the standalone predicate admits infinite mesh. Neutralised in Theorems A/B by `ApproximationCondition`. Other definitions match (1.1), (1.3), (I)–(III). |
| BouRabeeGwynne.StoppedCurveLaws | NOTE | `IsStandardBrownianLaw` = Mathlib Brownian motion per coordinate plus independence (satisfiable, compiled). Exit-time totalisations and `Measure.map` junk are guarded by the a.s./AEMeasurable conjuncts. |
| BouRabeeGwynne.StoppedCurveMeasurable | NOTE | `untopD 0` totalisation of never-exiting paths. The measurability statements are true for the totalised maps and irrelevant under a.s. finite exit. |
| BouRabeeGwynne.DiscreteHarmonicMeasure | NOTE | `exitVertex` totalises never-exit to the start vertex; `discreteHarmonicMeasure` is a probability measure even without accessibility. Every theorem assumes `haccess`. |
| BouRabeeGwynne.TrajectoryCoupling | OK | Generic intertwining lemma; hypotheses jointly satisfiable and conclusion correct. |

Counts: OK 10, NOTE 6, ISSUE 0. No `Upstream/` modules in this batch.

## BouRabeeGwynne.AbsorbingExcursionKernel
- `selectedExcursionKernel` (line 21): none-branch is `dirac (true, constantState x)`, some-branch maps `κ j x` to active flag `false`. Matches docstring (terminated excursion when selector returns `none`).
- `absorbingExcursionKernel` (line 62): terminated histories stay terminated; active ones select the next excursion by `selector (endPoint s)`. Matches docstring. Total maps, no junk.
- `absorbingExcursionKernel_ae_start` (line 124): a.s. start-point identity from the `hstart`/`hconst` hypotheses. Generic; its hypotheses are ordinary conditions on the kernels and selector, not definitions, so no nonvacuity question beyond ordinary satisfiability (not checked here).

## BouRabeeGwynne.DiscretePDEAlgebra
- `discreteGrad` (line 28): f w − f v, matches paper ∇^G (first numbered display of §2.1, paper ll. 612–614).
- `discreteDiv` (line 31): ∑_w θ(w,v), matches (div θ)(v) = ∑_{(w,v)∈E} θ(e) (eq:discrete-divergence, paper l. 622). Docstring says "Equation (2.2)"; counting numbered displays in §2.1 gives (2.3). Docstring-only issue.
- `IsDiscreteVectorField` (line 34): antisymmetry, matches.
- `FiniteConductanceNetwork` (line 98): symmetric, nonnegative, zero diagonal; no connectivity or positivity assumed. Matches the paper's conductance networks.
- `laplacian` (line 109): ∑_w a(v,w)(f w − f v) = Δ^G of eq:geometric-laplacian (paper l. 289, labelled (1.4)). Docstring cites "(2.4)", which by count is the divergence-theorem display (paper l. 636), not the Laplacian. Docstring-only.
- `energy` (line 113) — NOTE: energy = ½ ∑_v ∑_w a(v,w)(f w − f v)² = sum over each undirected edge once. The paper's 𝒟(f,A) (eq:dir.energy, paper l. 812) sums over E[Ā], which contains both orientations (proof of Lemma 2.1, paper l. 633–660: "each neighboring pair appears twice"). So 𝒟 = ∑_v∑_w a(f w − f v)² = 2·energy on the same set. Checked by compiled `example` in Nonvacuity: `twoPointNetwork.energy (1_{1}) = 1`, where 𝒟 would be 2. `Section3EnergyNormalization.lean` (`incidentEnergy_eq_networkEnergy`) states the once-per-edge convention explicitly, so downstream statements are self-consistent; they differ from the paper's constants by 2.
- `green_laplacian` (line 135): ∑ Δf·g = −½ ∑∑ a(f w − f v)(g w − g v). Sign and factor check out.
- `discrete_integration_by_parts` (line 57): matches Lemma 2.1 (lemma:discrete-divergence-theorem, paper l. 633). The Lean version is over all of `V` (Fintype) with no zero-boundary hypothesis, so it is a generalisation. This makes the degree-finiteness correction (README item 3) automatic.
- `discrete_integration_by_parts_zero` (line 76): vanishing-divergence version, matches the paper's zero-boundary form.
- `weighted_quadratic_minimizer` (line 168): ∑x²/a ≤ ∑y²/a under ∑(y−x)x/a = 0 and a > 0, a Pythagorean inequality. Its name says "minimizer" and the statement is the minimum property. It is the quadratic core of Lemma 2.3 (dual variational principle, paper l. 684). Satisfiable (x = 0).

## BouRabeeGwynne.StoppedWalk
- `totalConductance` (line 27): sum over `V`, matches cond(w).
- `transitionProbability` (line 37) — NOTE: for v ∈ A, a(v,w)/cond(v) matches p(w,v) = cond(w,v)/cond(w) (eq:conductance, paper l. 233). Outside A it is δ_v (absorption). If cond(v) = 0 for v ∈ A, the row is zero, which is not a probability vector. Unreachable: every constructor (`stepPMF`, `trajectoryLaw`, ...) takes `hpos : ∀ v ∈ A, 0 < totalConductance v`.
- `IsAbsorbedPath` (line 103): correct absorption predicate.
- `exitTime` (line 117): `hittingAfter … Aᶜ 0`. Unfolds (Mathlib `HittingTime.lean` l. 65–66) to `if ∃ j ≥ 0, ω j ∈ Aᶜ then sInf … else ⊤`. This is the first exit, ⊤ if never. `exitTime_le_iff` (line 124) confirms the semantics.
- `stoppedGenerator` (line 79) and `stoppedGenerator_eq_laplacian_div` (line 83): normalised generator Δf/cond(v) on A, 0 off A. Correct.
- `trajectoryLaw` (line 208): Ionescu–Tulcea law of the chain (instance `isProbabilityMeasure`, line 212). Correct.

## BouRabeeGwynne.FiniteDirichlet
- `BoundaryAccessible` (line 18): every vertex of A reaches the complement by a path of positive-conductance edges. Matches the docstring.
- `SolvesDirichlet` (line 23): Δf = 0 on A and f = g off A. Correct.
- `maximum_principle` (line 69) and `homogeneous_solution_eq_zero` (line 102): correct under accessibility.
- `dirichletOperator` (line 116): linear, Laplacian rows on A, identity rows off A. Correct.
- `existsUnique_dirichlet` (line 165) and `dirichletSolution` (line 182): `Classical.choose` picks the unique solution, so no junk.
- `dirichlet_stability` (line 192), `dirichletSolution_stability` (line 222): uniform perturbation bound, correct.
- `boundaryAccessible_of_strict_subharmonic` (line 232): hypothesis `∀ v ∈ A, 0 < Δf v` is satisfiable. Compiled on the two-point network with f = 1_{1}, Δf(0) = 1 > 0. The hypothesis excludes exactly the closed positive-conductance components inside A, since Green's identity forces their Laplacian sum to 0.

## BouRabeeGwynne.FiniteExit
- `totalConductance_pos_of_boundaryAccessible` (line 23): correct.
- `nStepPMF` (line 32): n-fold bind of the actual transition PMFs. Correct.
- `survivalProbability` (line 123): P(X_n ∈ A), which equals P(τ > n) because the walk is absorbed (`trajectoryLaw_marginal`, line 112). Correct, no junk.
- `survivalLimit` (line 191): infimum of an antitone family bounded in [0,1]. Correct.
- `trajectoryLaw_ae_finiteExit` (line 260) and `..._of_boundaryAccessible` (line 286): a.s. finite exit under accessibility. Compiled as a nonvacuity example.

## BouRabeeGwynne.CurveSpace
- `TimeChange` (line 32): `unitInterval ≃o unitInterval`. Order automorphisms are exactly the increasing homeomorphisms, as the docstring says.
- `timeChangeCost` (line 44): supremal spatial error, sup over `unitInterval`.
- `frechetEDist` (line 49): infimum over time changes of the supremal error. This is paper eq:cmp-topology (paper l. 251) after normalising time to [0,1]. No junk: `TimeChange` is nonempty and the infimum is over ENNReal.
- `CurveSpace` (line 158): `SeparationQuotient` of the Fréchet pseudo-metric, i.e. curves identified at Fréchet distance 0. Matches "curves modulo time parametrisation".
- `project` (line 181) and `endPoint` (line 201): well defined on the quotient (`endPoint` via `SeparationQuotient.lift`).

## BouRabeeGwynne.LocalGeometry
- `dist_le_mesh` (line 13): requires `mesh ≠ ∞`, which guards `toReal`. Correct.
- `edge_dist_le_two_mesh` (line 29): adjacent marked points within 2 meshes, including exterior neighbours. Correct.
- `cell_subset_cthickening` (line 40) and `cell_subset_domain_of_collar` (line 49): correct.

## BouRabeeGwynne.LocalRegion
- `interiorVertices` (line 13): V[U] = {v | pos v ∈ U}. Matches.
- `neighbors` (line 17): {w | adj v w}. Matches.
- `vertexBoundary` (line 21): {w ∉ A | ∃ v ∈ A, adj v w}, the exterior boundary. This is the ∂ needed for the Dirichlet problem.
- `boundaryVertices` (line 25), `closedVertexSet` (line 29), `closedVertices` (line 33): ∂V[U], A ∪ ∂A and \bar V[U]. Match the paper's definitions.
- `neighbors_finite` (line 37), `interiorVertices_finite` (line 61), `boundaryVertices_finite` (line 84), `closedVertices_finite` (line 92): correct.
- `closedVertices_finite_of_collar` (line 120): guarded by `mesh ≠ ⊤`. Correct.

## BouRabeeGwynne.FacetMeasure
- `euclideanHausdorffMeasure_affineSpan_pos_lt_top` (line 13): for nonempty compact convex s, 0 < μH in the affine dimension < ∞. Correct.
- `facetVolume_pos_lt_top` (line 72): adjacency gives affine dimension d−1, hence 0 < facetVolume < ∞.
- `edgeLength_pos` (line 97), `conductance_pos` (line 104), `conductance_ne_top` (line 108): correct. Uses `pos_injective`.

## BouRabeeGwynne.DiscretePDE
- `conductanceReal` (line 17): facetVolume.toReal / ‖pos w − pos v‖ on edges, 0 off edges (documented). `toReal` is finite on edges (`facetVolume_ne_top`), so no junk. Matches (1.1).
- `discreteLaplacian` (line 76): ∑ over the finite neighbour set of a(v,w)(f w − f v). Matches (1.4).
- `weightedDiscreteGradient` (line 81): cond(w,v)(f w − f v), orientation (w,v). Matches eq:anabla, paper's (2.2), as the docstring says.
- `DiscreteHarmonicOn` (line 99): requires finite degree at interior vertices, automatic under local finiteness.
- `SolvesDirichlet` (line 105): Δh = 0 on V[U], h = boundary data on ∂V[U]. Matches the discrete Dirichlet problem.
- `DirichletError` (line 110): uniform error over interior vertices, matches (1.5).
- `DirichletConverges` (line 115): ∀η>0 eventually uniform error ≤ η. Matches the limit form of (1.5).

## BouRabeeGwynne.TilingNetwork
- `finiteNetwork` (line 15): restriction of `conductanceReal` to R, symmetric, nonnegative, zero diagonal. Correct.
- `finiteNetwork_laplacian` (line 24): equals the discrete Laplacian when neighbours lie in R. Hypothesis satisfiable.
- `finiteInterior` (line 39), `solvesDirichlet_restrict` (line 60), `solvesDirichlet_iff_restrict` (line 74): correct, and the hypothesis `hneighbors` is the local-finiteness premise.
- `dirichlet_unique_on_closed` (line 93): conclusion restricted to `closedVertices`, as documented. The hypothesis `haccess` on the finite network is the graph-level accessibility of V[U], which is satisfiable.

## BouRabeeGwynne.PaperObjects
- `IsDomain` (line 17): open, nonempty, connected. Matches "domain".
- `HasAmbientCollar` (line 21): `closure U ⊆ interior D`, the correction (README item 1).
- `ConvexPolytope` (line 43): compact, convex, nonempty interior, finite H-representation. Matches the paper's "closed convex polytope", with boundedness from compactness.
- `IsCodimOneFacet` (line 61): (P ∩ Q) nonempty with affine dimension d−1. Matches the paper's edge rule. NOTE: `d - 1` is truncated subtraction, harmless for d ≥ 1 and all theorems assume `1 ≤ d`.
- `LocallyFiniteCells` (line 75): each compact K ⊆ D meets finitely many cells. Matches paper l. 225.
- `TilingData` (line 87): cover, disjoint interiors, vertex in interior, local finiteness. Matches the paper's tiling graph. `domain` is not required open or connected, which is fine because the theorems impose it.
- `TilingData.adj` (line 109), `facet` (line 120), `facetVolume` (line 124): μH^{d−1}(cell v ∩ cell w). Match vol_{d−1}(P_w ∩ P_v).
- `conductance` (line 132): facetVolume / edgeLength = (1.1). NOTE: on the diagonal (v = w) it is ⊤ (facet = cell has infinite (d−1)-measure, edge length 0). Unused there: only the adjacent-pair positivity lemmas (`FacetMeasure.lean` l. 104–110) use it.
- `IsOrthogonal` (line 151): for each edge, facet differences are orthogonal to pos w − pos v. Equivalent to the paper's orthogonality, since differences of facet points span its direction.
- `mesh` (line 157): sup of cell diameters = ε_n (eq:smallness, paper l. 263, and (1.3)). NOTE: ⊤ when diameters are unbounded (see `RegularityII`).
- `minTileVolume` (line 161): infimum of tile volumes, the "smallest tile" of paper item (II). For V = ∅ it is ⊤.
- `incidentScale` (line 165): sup over adjacent w of (edgeLength·facetVolume)^α, the max over incident edges of paper item (III). For an isolated vertex it is 0, so (III) fails there, which is conservative. The paper's max over an empty set is undefined in that case.
- `RegularityI` (line 200): d = 2, matches paper item (I) (l. 269).
- `RegularityII` (line 207) — NOTE: intended as paper item (II) (l. 270), "minTileVolume ≥ exp(−o(ε⁻¹))", i.e. ∃ q with ε_n q_n → 0 and minVol ≥ exp(−q_n) eventually. Junk: when mesh = ⊤, `mesh.toReal = 0`, so the Tendsto holds for any q. Then q = 0 with minVol ≥ 1 satisfies the predicate even though the mesh is infinite, which the paper's (II) excludes. Neutralised in Theorems A/B: `ApproximationCondition` (Approximation.lean l. 40–43, `mesh + uniformError → 0` in ℝ≥0∞) forces mesh → 0 (`mesh_tendsto_zero`, l. 45). A grep shows every statement use of `PaperRegularity` appears next to `ApproximationCondition`. The empty tiling fails (II) because `minTileVolume.toReal = 0`, harmlessly.
- `RegularityIII` (line 216): ∃ α > 0, C ≠ ∞, eventually in n, diam(cell v) ≤ C · incidentScale α v. Matches paper item (III) with a uniform constant. No junk (ENNReal).
- `PaperRegularity` (line 223): disjunction (I) ∨ (II) ∨ (III). Matches "at least one of the three conditions".

## BouRabeeGwynne.StoppedCurveLaws
- `curveSpaceMeasurableSpace` (line 23), `curveSpaceBorelSpace` (line 26): Borel σ-algebra on the metric curve space.
- `BrownianPath` (line 29): C(ℝ≥0, ℝ^d), the Borel σ-algebra on it (line 31).
- `IsStandardBrownianLaw` (line 38): a probability measure with each coordinate a Mathlib `IsBrownianReal` (zero-start Gaussian projective family plus continuity) and the coordinates mutually independent. This is standard d-dimensional Brownian motion. Satisfiable: `isStandardBrownianLaw_euclideanWienerLaw` (EuclideanWienerLaw.lean l. 83) is compiled in Nonvacuity.
- `polygonalCurve` (line 45): uniform-time polygonal interpolation of the first m steps. Checked: t = 0 gives pos(ω 0), t = 1 gives pos(ω m) by telescoping, and the clamp gives the segments. Correct.
- `stoppedPolygonalCurve` (line 60) — NOTE: for never-exiting paths the duration is `untopD 0`, so the curve is constant (documented, lines 57–59). Guarded by the a.s. clause in `IsStoppedTilingWalkLaw` (line 112).
- `continuousExitTime` (line 67): ⨅ over {t | z + ω t ∉ U} = first exit of z + B from U. ⊤ on the empty set (documented). Correct.
- `stoppedBrownianRepresentative` (line 74) — NOTE: `toNNReal ⊤ = 0` totalisation (duration zero), documented. Guarded by Theorem A's a.s. clause (TheoremAStatement.lean l. 44).
- `stoppedBrownianCurve` (line 83): no docstring (style only).
- `stoppedBrownianLaw` (line 88): `μ.map`. Measure.map is 0 for non-AEMeasurable maps; Theorem A asserts AEMeasurable and IsProbabilityMeasure (TheoremAStatement.lean l. 43–45), so guarded.
- `IsStoppedTilingWalkLaw` (line 100): R = closedVertices ∪ {v₀} (finite), A = interior of R, hpos, start = v₀, AEMeasurable curve, a.s. finite exit, μ = law.map curve. Matches the paper's walk. `letI : MeasurableSpace R := ⊤` is the discrete σ-algebra on a finite type. Interior neighbours lie in closedVertices ⊆ R, so the transition rows are the true rows (`neighbor_mem_closedVertices`, LocalRegion.lean l. 112). Nonvacuity not attempted; see the Nonvacuity section.

## BouRabeeGwynne.StoppedCurveMeasurable
- `polygonalCurve_congr_prefix` (line 21): the interpolation through step m depends only on ω ≤ m. Correct.
- `measurable_curveProjection_polygonalCurve` (line 38): factorisation through the finite prefix. Correct.
- `measurable_discreteExitTime` (line 58): correct.
- `measurable_stoppedPolygonalDuration` (line 63) — NOTE: the `untopD 0` totalisation (see StoppedCurveLaws). The measurability statement is true for the totalised map and cannot affect statements under a.s. finite exit.
- `measurable_stoppedPolygonalCurve` (line 71): measurable for all paths, with no finite-exit hypothesis. Correct.

## BouRabeeGwynne.DiscreteHarmonicMeasure
- `exitVertex` (line 24) — NOTE: `ω ((exitTime A ω).untopD 0)` is ω 0 on never-exiting paths. Documented as the same convention as the curve law. Relevant only on a null set under `haccess`.
- `exitVertex_not_mem` (line 32), `IsAbsorbedPath.eventually_eq_exitVertex` (line 40): correct.
- `integral_stepPMF_of_harmonic` (line 76), `trajectoryLaw_integral_eval_of_harmonic` (line 100): mean-value property, correct.
- `discreteHarmonicMeasure` (line 114) — NOTE: pushforward of the trajectory law by `exitVertex`, and a probability measure for every A (instance, line 118). Without `haccess`, never-exit mass sits on the start vertex, which lies in A. The paper's harmonic measure needs a.s. exit. Every theorem in this module assumes `haccess` (lines 128, 156).
- `integral_discreteHarmonicMeasure_of_solvesDirichlet` (line 127): ∫ g dμ_v = f v under SolvesDirichlet, haccess and hpos. Correct. Satisfiable: the two-point network has a unique solver (Nonvacuity).
- `dirichletSolution_eq_integral_discreteHarmonicMeasure` (line 155): the genuine solver is the harmonic-measure integral. Correct.

## BouRabeeGwynne.TrajectoryCoupling
- `prefixMap` (line 42), `append` (line 50), `prefix_zero` (line 80), `prefix_succ` (line 86): generic history combinatorics, correct.
- `map_prefix_law` (line 104): hypotheses `hinit : μ.map f = ν` and `hstep : (κ n h).map f = η n (prefixMap f n h)` are jointly satisfiable (e.g. f = id, κ = η). Correct.
- `measure_eq_of_prefix_eq` (line 121): equal finite prefix laws determine the measure (cylinders). Correct.
- `map_trajectory_law` (line 147): the image of the trajectory law is the trajectory law of the image kernels. Correct.

## Nonvacuity examples
Scratch file: `Nonvacuity.lean`.
Compiled from the repository root with `lake env lean …/Nonvacuity.lean`. Exit 0, no warnings, no `sorry`.

```lean
import BouRabeeGwynne.FiniteExit
import BouRabeeGwynne.FiniteDirichlet
import BouRabeeGwynne.EuclideanWienerLaw

open MeasureTheory ProbabilityTheory
open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork

/-- Two vertices joined by a unit-conductance edge. -/
def twoPointNetwork : FiniteConductanceNetwork (Fin 2) where
  a v w := if v = w then 0 else 1
  symm v w := by
    by_cases h : v = w
    · subst h; rfl
    · simp [h, Ne.symm h]
  nonneg v w := by
    by_cases h : v = w <;> simp [h]
  loop_zero v := by simp

/-- The interior `{0}` is boundary accessible: `0` reaches `1 ∉ {0}` in one edge. -/
lemma twoPoint_boundaryAccessible : twoPointNetwork.BoundaryAccessible {0} := by
  intro v hv
  have hv0 : v = 0 := hv
  subst hv0
  refine ⟨1, by simp, Relation.ReflTransGen.single ?_⟩
  simp [twoPointNetwork]

/-- The actual walk from `0` exits `{0}` almost surely. -/
example : ∀ᵐ ω ∂twoPointNetwork.trajectoryLaw ({0} : Set (Fin 2))
    (twoPointNetwork.totalConductance_pos_of_boundaryAccessible {0} twoPoint_boundaryAccessible) 0,
    exitTime ({0} : Set (Fin 2)) ω ≠ ⊤ :=
  twoPointNetwork.trajectoryLaw_ae_finiteExit_of_boundaryAccessible {0}
    twoPoint_boundaryAccessible 0

/-- The finite Dirichlet problem is uniquely solvable on this network. -/
example (g : Fin 2 → ℝ) : ∃! f : Fin 2 → ℝ, twoPointNetwork.SolvesDirichlet {0} g f :=
  twoPointNetwork.existsUnique_dirichlet {0} twoPoint_boundaryAccessible g

/-- The hypothesis of the strict-subharmonic criterion is satisfiable: `Δf(0) = 1 > 0`. -/
example : twoPointNetwork.BoundaryAccessible {0} :=
  twoPointNetwork.boundaryAccessible_of_strict_subharmonic {0}
    (fun v => if v = 1 then 1 else 0) (by
      intro v hv
      have hv0 : v = 0 := hv
      subst hv0
      simp [FiniteConductanceNetwork.laplacian, twoPointNetwork])

/-- Value of the library `energy` on `f = 1_{1}`: `½ (1 + 1) = 1`. The paper's
`𝒟(f,A)` sums over both orientations, which gives `2` here. -/
example : twoPointNetwork.energy (fun v => if v = 1 then 1 else 0) = 1 := by
  simp [FiniteConductanceNetwork.energy, Fin.sum_univ_two, twoPointNetwork]
  norm_num

/-- The standard Brownian law required in Theorem A's conclusion is satisfiable in every dimension. -/
example (d : ℕ) : ∃ μ : Measure (BrownianPath d), IsStandardBrownianLaw μ :=
  ⟨_, isStandardBrownianLaw_euclideanWienerLaw d⟩
```

What this shows:
- The network-level bundle is jointly satisfiable and the definitions compute as intended: `BoundaryAccessible {0}` holds; the walk from 0 exits a.s. (`trajectoryLaw_ae_finiteExit_of_boundaryAccessible`); the finite Dirichlet problem has a unique solution (`existsUnique_dirichlet`). Together these exercise the `hpos`, accessibility and finite-exit hypotheses used by `DiscreteHarmonicMeasure` and `FiniteExit`.
- The strict-subharmonic hypothesis of `boundaryAccessible_of_strict_subharmonic` is satisfiable (Δf(0) = 1 > 0).
- `energy` on the two-point network evaluates to 1. The paper's 𝒟 would give 2, which confirms the factor-2 NOTE on `energy`.
- `IsStandardBrownianLaw` is satisfiable in every dimension (`isStandardBrownianLaw_euclideanWienerLaw`).

Not compiled:
- An explicit `OrthogonalTiling` (e.g. two intervals in ℝ¹) was not built, because it needs `ConvexPolytope` compactness, interior and halfspace data. Cited instead: `SpherePackings.exists_lattice_tilingSequence` (`SpherePackings/Support/Guards/LatticeTilings.lean` l. 45–48) gives, for 1 ≤ d, a `TilingSequence` G with `HasAmbientCollar (ball 0 1) G.domain`, `Nonempty (NearestVertexData G)`, `∀ N, N.ApproximationCondition` and `RegularityII G`. Together with `isLipschitzDomain_ball`, this supplies a nonvacuous instance of Theorem A's hypothesis bundle for U = ball. Not recompiled here.
- `IsStoppedTilingWalkLaw` was not instantiated. It needs an `OrthogonalTiling` and graph-level accessibility of its finite region. Its ingredients (a.s. finite exit on the finite network, measurability of the stopped curve) are covered generically by the network example and `measurable_stoppedPolygonalCurve`.
