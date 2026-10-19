# Audit batch 6
| Module | Verdict | Summary |
|---|---|---|
| BouRabeeGwynne.WalkBrownianFailure | NOTE | Bound `(k+1)b` matches docstring; `herror`/`hinit` use `discreteHarmonicMeasure`, whose exit vertex is junk for never-exiting walks, and no `BoundaryAccessible` hypothesis is assumed |
| BouRabeeGwynne.WalkBrownianActiveTransfer | OK | Truncation inequality; flag convention (`false` = active) is consistent with the rest of the batch |
| BouRabeeGwynne.FiniteStoppedLawComparison | NOTE | `ρ` need not be a probability measure; `innerDomain` (out of batch) is ∅ when `Uᶜ = ∅`, so `hosc` is a different event for `U = univ`; harmless for bounded `U` |
| BouRabeeGwynne.BrownianStoppedEndpoint | NOTE | Non-a.e. lemma uses `toNNReal ∞ = 0` on never-exiting paths; consistent because the selector sees the same position; a.e. lemma is clean |
| BouRabeeGwynne.ExcursionOscillation | OK | Oscillation bounds (`2r`, `R + a + S`) match their statements |
| BouRabeeGwynne.TilingWalkRegionEmbedding | OK | Region enlargement preserves absorbed walk law under `neighbors v ⊆ R` for active `v` |
| BouRabeeGwynne.TilingClockedExcursion | OK | Clocked excursion law is region-independent; statements match docstrings |
| BouRabeeGwynne.Section3LocalMaximum | OK | `externalBoundary` is the graph boundary; clamping argument is correct |
| BouRabeeGwynne.Section3Iteration | OK | Trimming rule and `|replacement − h| ≤ κ + δ` are as documented |
| BouRabeeGwynne.Section3Boxes | OK | Box/cell-cut lemmas; `mesh ≠ ∞` is assumed where `toReal` is used |
| BouRabeeGwynne.HalfspaceBoundary | OK | Interior and frontier characterizations are correct without irredundancy |
| BouRabeeGwynne.HalfspaceFibers | NOTE | `planeParameter` divides by zero for constraints parallel to `e`; the junk is never used (filtered) |
| BouRabeeGwynne.FiberEndpoints | OK | Active-constraint and frontier statements are correct |
| BouRabeeGwynne.ProjectedBase | NOTE | `hyperplaneProjection e` is `id` when `e = 0` (not a hyperplane projection); all uses that matter have `e ≠ 0` |
| BouRabeeGwynne.Section3Projection | OK | Orthogonal projection is 1-Lipschitz; facet measure does not increase |
| BouRabeeGwynne.Section3GoodLines | OK | Strict-margin good-parameter lemma is correct |
| BouRabeeGwynne.PolytopeBoundary | OK | Closure of interior and facet-in-frontier lemmas are correct |
| BouRabeeGwynne.LocalFacetCoverage | OK | Frontier equals union of contacts; lower-dimensional contacts are included as documented |
| BouRabeeGwynne.Section3ColumnTraversal | OK | Strict increase of fiber endpoints across touching cells |
| BouRabeeGwynne.Section3GraphPaths | OK | Telescoping and boundary-path lemmas are correct |
| BouRabeeGwynne.FacetNormals | OK | Separation signs (outward from `v`, inward to `w`) are correct |
| BouRabeeGwynne.FacetNull | OK | Non-adjacent contacts have zero `facetVolume` |
| BouRabeeGwynne.Section3ColumnPaths | OK | Almost every column has boundary-reaching paths in the column graph |
| BouRabeeGwynne.Section3WeightedEnergy | NOTE | Lemma 3.5 is stated in facet form (`facetVolume · length`), equal to `d·vol(Q_e)` only via Lemma 2.4; `1/2` normalizes unordered edges |
| BouRabeeGwynne.Section3ColumnEnergy | OK | Integral and Cauchy–Schwarz bounds are correct |
| BouRabeeGwynne.Section3ColumnEdgeIndex | OK | Oriented edges are counted once; column graph edges match the filter |
| BouRabeeGwynne.Section3ColumnEstimate | NOTE | Lemma 3.1 bound matches the printed threshold with undirected sums; the printed directed sums give a threshold twice as large, so the Lean statement is stronger |

Totals: OK 20, NOTE 7, ISSUE 0.

## BouRabeeGwynne.WalkBrownianFailure
- `walkBrownianJointLaw_firstFailure_le` (line 22): matches its docstring. The failure event over `i ≤ k` has mass at most `(k+1)·b`, chained through `SkeletonCoupling.jointPathLaw_bad_le` with `ε n = b` for `n < k` and `1` otherwise. The hypotheses `herror` (37–41) and `hinit` (43–44) are the Section 3 cell approximations and are not discharged here. For `b < 1/(k+1)` they are a genuine approximation requirement, not a trivial one.
- `herror`/`hinit` (lines 37, 43): these compare `N.discreteHarmonicMeasure (B j)` with the Brownian stopped law. `discreteHarmonicMeasure` is `map exitVertex` (DiscreteHarmonicMeasure.lean:24–25), and `exitVertex A ω = ω ((exitTime A ω).untopD 0)`. For a walk that never leaves `A`, the exit vertex is the start vertex, which lies in `A`, not on the boundary. The theorem assumes no `N.BoundaryAccessible (B j)`; `WalkBrownianActiveTransfer` (line 59) does. The conclusion is still a true statement about the actual coupling, so this is a NOTE: the hypotheses have junk meaning only for non-accessible `B`.
- `hB` (line 24): positivity is required only on `B j`, which is what the coupling uses.

## BouRabeeGwynne.WalkBrownianActiveTransfer
- `sequenceActive` (line 18): `{ω | (ω K).1 = false}`. `false` means active, consistent with `activeEndpointCell` and the stopping flag in `actualWalkStage`/`selectedClockedExcursion` (none ⇒ `true`). OK.
- `coupling_walkActive_le_brownianActive_add_firstFailure` (line 25): OK.
- `trajectoryLaw_walkActive_le_brownianActive_add_failure` (line 48): walk-active mass at `K` is at most Brownian-active mass plus the first-failure event. Hypotheses `hBA`, `hA`, `haccess` are consistent. OK.

## BouRabeeGwynne.FiniteStoppedLawComparison
- `levyProkhorov_reconstructed_stopped_laws_le` (line 18): the conclusion `LP ≤ r` under `b + c + o ≤ r` and `ε + η < r` is a valid building block and matches the docstring (failure, Brownian tail, oscillation).
- `ρ` (line 21): no `IsProbabilityMeasure ρ` is assumed. The coupling argument only uses bad-set masses, so the statement is valid for finite `ρ`, but it is stated for arbitrary measures; instantiate with probability measures.
- `hosc` (lines 35–36), via `innerDomain` (BrownianInnerExit.lean:15–16, outside this batch): `innerDomain U ε = {x | ε < infDist x Uᶜ}`. For `Uᶜ = ∅` (for example `U = univ`), `infDist_empty` gives `infDist x ∅ = 0`, so `innerDomain` is `∅` rather than `univ`. The event then becomes "whole-curve oscillation `> η`" instead of the intended empty event. The lemma is still true, but its hypothesis is stronger than intended for that `U`. Harmless for bounded `U`, which is the only case used in the paper (Theorem A assumes bounded `U`). Recommend requiring `Uᶜ.Nonempty` in `innerDomain`'s users, or defining it with the convention made explicit.
- `hsmall` (line 24, strict) and `hbudget` (line 37): consistent with the `≤ r` conclusion.

## BouRabeeGwynne.BrownianStoppedEndpoint
- `brownianSkeletonClock_position_not_mem_of_stopped` (line 17): stated for all `ω`. `(brownianSkeletonClock …).2.toNNReal` sends `∞` to `0`, so on never-exiting paths the position is `z`. The claim stays true because `brownianClockChoice` (BrownianSkeletonClock.lean:21–23) reads the same totalized position. NOTE, harmless.
- `brownianSkeleton_concatenate_endPoint` (line 49): requires `≠ ∞` (line 52). OK.
- `standardBrownianLaw_skeleton_ae_stopped_endPoint_outside` (line 63): the a.e. form, using `standardBrownianLaw_ae_finiteSkeletonClock`. The junk does not enter. OK.

## BouRabeeGwynne.ExcursionOscillation
- `curveOscillationLe` (line 18): `{c | ∀ t, dist (c t) (c 0) ≤ R}`. Empty for `R < 0`, and only used with `R ≥ 0`. OK.
- `isClosed_curveOscillationLe` (21), `measurableSet_curveOscillationLe` (26), `mem_curveOscillationLe_of_closedBall` (30): OK.
- `absorbingExcursionKernel_ae_oscillation` (37), `trajMeasure_ae_curveOscillation` (66): a.e. propagation over the Markov chain. OK.
- `brownianExcursionKernel_ae_oscillation` (93): start in `ball x r` gives oscillation `≤ 2r`. Matches the statement. OK.
- `concatenate_pointwise_dist_le` (112), `goodExcursionPair_pasted_pointwise_dist_le` (133): bound `R + a + S`. OK.

## BouRabeeGwynne.TilingWalkRegionEmbedding
- `regionInclusion` (32), `regionInclusion_injective` (34): OK.
- `finiteNetwork_totalConductance_inclusion` (38): needs `neighbors v ⊆ R`, which is the stated hypothesis. OK.
- `finiteNetwork_stepPMF_inclusion` (53), `finiteNetwork_trajectoryLaw_inclusion` (109): the absorbed walk law pushes forward to the larger region's law. Positivity is required only on `B`. OK.
- `closedVertices_mono` (128): OK.

## BouRabeeGwynne.TilingClockedExcursion
- `exitTime_comp` (15), `ofWalk_comp` (22): reindexing identities. OK.
- `finiteNetwork_clockedExcursion_inclusion` (40), `ambient_trajectoryLaw_map_clockedExcursion` (66): the clocked excursion kernel is independent of the enclosing region. Matches docstring. OK.

## BouRabeeGwynne.Section3LocalMaximum
- `externalBoundary` (21): `{w | w ∉ A ∧ ∃ v ∈ A, 0 < a v w}`, the graph boundary `∂A`. Matches the paper's convention. OK.
- `local_maximum_principle` (26): clamping outside `A` to `min(h, M)` is correct; only boundary values matter. OK.
- `harmonic_error_le_boundary_error_add_oscillation` (51): `|h v − g v| ≤ η + ω`. OK.

## BouRabeeGwynne.Section3Iteration
- `boundaryAccessible_mono` (23): OK.
- `errorBadSet` (30): strict `κ < |f v|`. OK.
- `trimmedErrorSet` (35): keeps a bad `v` iff every good positive-conductance neighbour has `δ < |f v − f w|`. Matches the docstring ("remove a bad vertex if an edge … has small gradient"). OK.
- `abs_le_outside_trimmedErrorSet` (51): `|f v| ≤ κ + δ` outside the trimmed set. OK.
- `trimmedHarmonicReplacement` (69), `trimmedHarmonicReplacement_step_bound` (82): the replacement is the actual Dirichlet solver on the trimmed set, and the bound `|replacement − h| ≤ κ + δ` holds everywhere. Consistent with the docstring. OK.

## BouRabeeGwynne.Section3Boxes
- `slabIntersection` (19): open box `{x | ∀ i, lower i < L i x < upper i}`. OK.
- `exists_cut_of_not_subset` (25): intermediate value on a convex polytope. OK.
- `cellsContainedInterior` (51), `cellsContainedInterior_subset` (54): OK.
- `boundary_cell_meets_cut` (57): a boundary cell of the box meets a cut line. OK.
- `boundary_cell_dist_le_box_diameter` (69): requires `hmesh : T.mesh ≠ ∞`, which is needed for `mesh.toReal` to be meaningful. OK.
- `error_le_of_good_box` (87): `hmod` quantifies over all `w : R` within `mesh + D`, but only boundary `w` are used, so it is no stronger than needed. OK.

## BouRabeeGwynne.HalfspaceBoundary
- `mem_carrier_iff` (10), `zero_normal_bound` (17): uses `interior_nonempty`. OK.
- `inner_lt_of_mem_interior` (24), `mem_interior_iff` (42): correct characterization without irredundancy. OK.
- `mem_frontier_iff` (72): frontier points are exactly those with an active nonzero constraint. OK.

## BouRabeeGwynne.HalfspaceFibers
- `exists_halfspace_inner_pos` (13), `exists_halfspace_inner_neg` (32): from compactness. OK.
- `upperConstraints` (42), `lowerConstraints` (46): filtered by the sign of `⟪p.1, e⟫`. OK.
- `planeParameter` (60): `(p.2 − ⟪p.1, y⟫)/⟪p.1, e⟫`. Division by zero gives junk `0` for `⟪p.1, e⟫ = 0`. NOTE: this junk is never used, because `upperFiber` and `lowerFiber` take `inf'`/`sup'` only over the filtered constraints (lines 63–67, with nonemptiness at 49 and 54).
- `parallelConstraintsHold` (70): OK.
- `mem_line_iff` (87): exact fiber description, including the empty-fiber case. OK.

## BouRabeeGwynne.FiberEndpoints
- `exists_upperFiber_active` (29), `exists_lowerFiber_active` (42), `upperFiber_mem_frontier` (55), `lowerFiber_mem_frontier` (65): OK.
- `upperEndpoint` (76), `lowerEndpoint` (79): `y + fiber • e`. OK.

## BouRabeeGwynne.ProjectedBase
- `hyperplaneProjection` (line 10): orthogonal projection onto `e^⊥` for `e ≠ 0`. For `e = 0` it is `id` (because `(inner e e)⁻¹ = 0`), not a hyperplane projection. NOTE: the docstring says the main uses have `e ≠ 0`, and the only `e`-generic use (`projected_facet_measure_le`, Section3Projection:58) still holds for `id`.
- `projectedBase` (45): feasible base of the fibres. OK.
- `projectedBase_eq_image` (51): the feasibility base equals the orthogonal image of the cell, proved without any polytope projection theorem. Matches its docstring. OK.
- `upperEndpoint_mem_frontier` (77), `lowerEndpoint_mem_frontier` (81), `project_upperEndpoint` (85), `project_lowerEndpoint` (90): OK.

## BouRabeeGwynne.Section3Projection
- `hyperplaneProjection_norm_le` (20), `hyperplaneProjection_lipschitz` (39): 1-Lipschitz. OK.
- `lipschitzOne_euclideanHausdorffMeasure_image_le` (46): `μH(P '' s) ≤ μH(s)`. OK.
- `projected_facet_measure_le` (58), `projected_facet_compact` (62), `projected_facet_measure_ne_top` (66): OK.

## BouRabeeGwynne.Section3GoodLines
- `unitLine_isometry` (15), `unitLine_interval_measure` (21): length of a unit-speed segment. OK.
- `exists_unitLine_parameter_outside` (30): strict margin `μ Y < ofReal (b − a)` gives a good parameter `t ∈ Ioo a b`. OK.
- `exists_unitLine_parameter_outside_of_bound` (42): OK.

## BouRabeeGwynne.PolytopeBoundary
- `ConvexPolytope.closure_interior` (10): OK.
- `cell_disjoint_interior` (20), `facet_subset_frontier_left` (26), `facet_subset_frontiers` (34): OK.

## BouRabeeGwynne.LocalFacetCoverage
- `frontier_point_mem_other_cell` (15): a frontier point of a cell inside `interior domain` lies in another cell (local finiteness). OK.
- `touchingCells` (45): `w ≠ v ∧ (facet v w).Nonempty`, including lower-dimensional contacts as documented. OK.
- `touchingCells_finite` (49), `frontier_eq_iUnion_contacts` (58): OK.

## BouRabeeGwynne.Section3ColumnTraversal
- `exists_touching_upperFiber_gt` (25), `exists_touching_lowerFiber_lt` (77): a touching cell with strictly larger upper (smaller lower) fiber endpoint. OK.

## BouRabeeGwynne.Section3GraphPaths
- `unorderedEdgeVariation` (26): `|f v − f w|` on an unordered edge. OK.
- `abs_sub_le_walk_variation` (38), `abs_sub_le_graph_variation` (50), `abs_le_graph_variation_of_boundary_path` (66): telescoping. OK.
- `boundary_path_of_increasing_neighbor` (76): finite-graph argument for a path to the boundary. OK.

## BouRabeeGwynne.FacetNormals
- `exists_cell_separator` (19), `facet_direction_eq_ker` (40), `inner_edge_eq_zero_of_mem_facet_direction` (63): OK. (`_hd` in line 40 is unused; harmless.)
- `facet_normal_separation` (76): edge vector points out of `v`'s cell and into `w`'s cell. OK.

## BouRabeeGwynne.FacetNull
- `euclideanHausdorffMeasure_eq_zero_of_affineSpan_rank_lt` (13): OK.
- `facet_finrank_le` (25), `facetVolume_eq_zero_of_not_adj` (50): non-adjacent contacts have zero `(d−1)`-area. The `d−1` truncation is excluded by `1 ≤ d`. OK.

## BouRabeeGwynne.Section3ColumnPaths
- `ae_projected_contact_adj` (18): a.e. `y`, a projected facet of a non-adjacent pair is null. OK.
- `columnGraph` (41): edges are adjacencies with an endpoint in `A` whose projected facet contains `y`. OK.
- `ae_column_boundary_path` (46), `ae_abs_le_column_graph_variation` (94): every interior column vertex reaches the boundary; telescoping bound. OK.

## BouRabeeGwynne.Section3WeightedEnergy
- `conductanceReal_mul_edge_norm_sq` (23), `facet_weight_le_gradient_energy` (30): OK.
- `weighted_gradient_energy_estimate_on_edges` (44): OK.
- `weighted_gradient_energy_estimate_finiteNetwork` (58): NOTE. This is Lemma 3.5 (paper line 1128) in facet form: `facetVolume · ‖e‖` replaces `d·vol_d(Q_e)`, and the equality is Lemma 2.4 (paper line 739, `lemma:geometry-bound`; CORRESPONDENCE.md:187). The `1/2` normalizes unordered edges on both sides. The paper's `E` is directed (its `−1/2` at line 638), so its printed `D` is twice ours on both sides and the inequality is unchanged.

## BouRabeeGwynne.Section3ColumnEnergy
- `columnVariation` (26), `integral_columnVariation` (39), `integral_columnVariation_le_facetSum` (55): OK.
- `facetSum_le_sqrt_energy_mul_sqrt_mass` (67), `integral_columnVariation_le_energy` (106): Cauchy–Schwarz, correct. OK.

## BouRabeeGwynne.Section3ColumnEdgeIndex
- `contactGraph` (16), `orientedContactPair` (32), `orientedInteriorEdges` (43): each undirected interior edge counted once. OK.
- `columnGraph_edgeFinset` (62), `column_graph_variation_eq` (88): OK.

## BouRabeeGwynne.Section3ColumnEstimate
- `incidentEnergy` (line 15): sum over unordered interior edges, no `1/2`. `incidentMass` (line 20): sum of `facetVolume.toReal · ‖e‖` over the same edges. Neither has a `toReal ⊤` junk, since the edges are adjacent (`facetVolume_ne_top`).
- `columnBadSet` (line 24): `∃ v ∈ A, y ∈ projBase(cell v) ∧ τ < |f v|`. A.e. this equals the printed `max_{v ∈ L_y} |f v| > τ`, because of `ae_column_boundary_path`. OK.
- `column_bad_measure_le` (51): Chebyshev. OK.
- `column_poincare_measure_bound` (84): matches Lemma 3.1 (paper line 937) with threshold `k·(D·Σ d vol(Q_e))^{1/2} = k·√incidentEnergy·√incidentMass`, including zero energy. NOTE: sums are over unordered edges. The printed sums are directed (CORRESPONDENCE.md:115), so the printed threshold is twice ours and the Lean bound is stronger. Not a defect.
- `column_poincare_of_energy_bound` (144): conditional on `henergy`. The docstring says so, and the energy input is the explicit Proposition 2.6 hypothesis. Honest. OK.

## Nonvacuity examples
Scratch file: `Nonvacuity.lean`
Compiled with `lake env lean …/Nonvacuity.lean` from the repository root. Exit 0, no errors, no warnings. `#print axioms` reports `[propext, Classical.choice, Quot.sound]`.

```lean
import BouRabeeGwynne.WalkBrownianFailure
import BouRabeeGwynne.EuclideanWienerLaw
import BouRabeeGwynne.BrownianExcursionKernel
import BouRabeeGwynne.ContinuousExitProperties

/-! Nonvacuity witness for the hypothesis bundle of
`walkBrownianJointLaw_firstFailure_le` in the one-stage case `k = 0`:
one walk vertex with no edges, one Brownian domain `ball 0 1`, one cell
`closedBall 0 1` that contains the whole closure of the domain, and the
standard Brownian law `euclideanWienerLaw 1`. The stage-`0` approximation
hypothesis holds with both masses equal to `1`. The `herror` bundle (`k ≥ 1`)
is not witnessed here. -/

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace BouRabeeGwynne.Nonvacuity

open FiniteConductanceNetwork

def N1 : FiniteConductanceNetwork (Fin 1) where
  a := fun _ _ => 0
  symm := fun _ _ => rfl
  nonneg := fun _ _ => le_rfl
  loop_zero := fun _ => rfl

def posOne : Fin 1 → Euc 1 := fun _ => 0
def BOne : Unit → Set (Fin 1) := fun _ => ∅
abbrev UOne : Unit → Set (Euc 1) := fun _ => Metric.ball 0 1
instance : MeasurableSpace (Option Unit) := ⊤

instance : MeasurableSingletonClass (Option Unit) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

def selOne : ℕ → Euc 1 → Option Unit := fun _ _ => none
abbrev mOne : ℕ → ℕ := fun _ => 1
def EOne : ∀ n, Fin (mOne n) → Set (Euc 1) := fun _ _ => Metric.closedBall 0 1
def choiceOne : ∀ n, Fin (mOne n) → Option Unit := fun _ _ => none

theorem hinj_one : Function.Injective posOne := fun a b _ => Subsingleton.elim a b

theorem hB_one : ∀ j v, v ∈ BOne j → 0 < N1.totalConductance v := by
  intro j v hv
  simp [BOne] at hv

theorem hU_one : ∀ j, IsOpen (UOne j) := fun _ => Metric.isOpen_ball

theorem hUb_one : ∀ j, Bornology.IsBounded (UOne j) := fun _ => Metric.isBounded_ball

theorem hs_one : ∀ n, Measurable (selOne n) := fun _ => measurable_const

theorem hE_one : ∀ n i, MeasurableSet (EOne n i) := fun _ _ => measurableSet_closedBall

theorem hdE_one : ∀ n, Pairwise (fun i j => Disjoint (EOne n i) (EOne n j)) := by
  intro n i j hij
  exact absurd (Subsingleton.elim i j) hij

theorem hselect_one : ∀ n, selOne n = cellSelector (EOne n) (choiceOne n) := by
  intro n
  funext x
  unfold cellSelector
  cases cellLabel (EOne n) x <;> rfl

theorem hdiam_one : ∀ n ≤ 0, ∀ i, ∀ x ∈ EOne n i, ∀ y ∈ EOne n i, dist x y ≤ 2 := by
  intro n _ i x hx y hy
  have hx' : dist x 0 ≤ 1 := mem_closedBall.mp hx
  have hy' : dist y 0 ≤ 1 := mem_closedBall.mp hy
  linarith [dist_triangle_right x y 0]

theorem hcover_one : ∀ n ≤ 0, ∀ j, closure (UOne j) ⊆ ⋃ i, EOne n i := by
  intro n _ j
  rw [show UOne j = Metric.ball 0 1 from rfl, closure_ball (0 : Euc 1) one_ne_zero]
  intro x hx
  exact Set.mem_iUnion.mpr ⟨0, hx⟩

theorem hinit_one :
    ∀ i : Fin (mOne 0),
      |((Measure.map posOne (N1.discreteHarmonicMeasure (BOne ()) (hB_one ()) 0)) (EOne 0 i)).toReal
        - ((Measure.map CurveSpace.endPoint
            (stoppedBrownianLaw (UOne ()) 0 (euclideanWienerLaw 1))) (EOne 0 i)).toReal|
        ≤ (1 / 2 : ℝ) / ((mOne 0 : ℝ) + 1) := by
  have : IsProbabilityMeasure (euclideanWienerLaw 1) :=
    (isStandardBrownianLaw_euclideanWienerLaw 1).1
  intro i
  have hwalk : (Measure.map posOne (N1.discreteHarmonicMeasure (BOne ()) (hB_one ()) 0))
      (EOne 0 i) = 1 := by
    rw [Measure.map_apply (measurable_of_finite posOne) (hE_one 0 i)]
    have hpre : posOne ⁻¹' (EOne 0 i) = univ := by
      apply eq_univ_of_forall
      intro v
      simp [posOne, EOne]
    rw [hpre, measure_univ]
  have hae : ∀ᵐ ω ∂(euclideanWienerLaw 1),
      CurveSpace.endPoint (stoppedBrownianCurve (UOne ()) 0 ω) ∈ EOne 0 i := by
    have key : ∀ᵐ ω ∂(euclideanWienerLaw 1),
        ∀ t, stoppedBrownianRepresentative (UOne ()) 0 ω t ∈ closure (UOne ()) :=
      ae_of_ae_map (measurable_stoppedBrownianRepresentative (Metric.isOpen_ball : IsOpen (Metric.ball (0 : Euc 1) 1)) 0).aemeasurable
        (brownianExcursionKernel_ae_mem_closure le_rfl Metric.isOpen_ball Metric.isBounded_ball
          (euclideanWienerLaw 1) (isStandardBrownianLaw_euclideanWienerLaw 1)
          (mem_ball_self one_pos))
    filter_upwards [key] with ω hω
    have h1 : stoppedBrownianRepresentative (UOne ()) 0 ω 1 ∈ Metric.closedBall (0 : Euc 1) 1 := by
      have h2 := hω 1
      rwa [show UOne () = Metric.ball 0 1 from rfl, closure_ball (0 : Euc 1) one_ne_zero] at h2
    exact h1
  have hbrown : (Measure.map CurveSpace.endPoint
      (stoppedBrownianLaw (UOne ()) 0 (euclideanWienerLaw 1))) (EOne 0 i) = 1 := by
    rw [stoppedBrownianLaw, Measure.map_map CurveSpace.continuous_endPoint.measurable
      (measurable_stoppedBrownianCurve (Metric.isOpen_ball : IsOpen (Metric.ball (0 : Euc 1) 1)) 0),
      Measure.map_apply (CurveSpace.continuous_endPoint.measurable.comp
        (measurable_stoppedBrownianCurve (Metric.isOpen_ball : IsOpen (Metric.ball (0 : Euc 1) 1)) 0)) (hE_one 0 i)]
    have hset : (CurveSpace.endPoint ∘ stoppedBrownianCurve (UOne ()) 0) ⁻¹' EOne 0 i
        =ᵐ[euclideanWienerLaw 1] (univ : Set (BrownianPath 1)) := by
      refine Filter.eventuallyEqSet_iff.2 ?_
      filter_upwards [hae] with ω hω
      simp only [Function.comp_apply, Set.mem_preimage, Set.mem_univ, iff_true]
      exact hω
    rw [measure_congr hset, measure_univ]
  rw [hwalk, hbrown]
  norm_num

theorem firstFailure_bundle_witness : True := by
  have : IsProbabilityMeasure (euclideanWienerLaw 1) :=
    (isStandardBrownianLaw_euclideanWienerLaw 1).1
  have h := FiniteConductanceNetwork.walkBrownianJointLaw_firstFailure_le N1 (le_refl (1 : ℕ))
    posOne hinj_one BOne hB_one UOne hU_one hUb_one (euclideanWienerLaw 1)
    (isStandardBrownianLaw_euclideanWienerLaw 1) selOne hs_one mOne EOne hE_one hdE_one
    choiceOne hselect_one 0 (b := 1 / 2) (by norm_num) hdiam_one
    (fun n hn => absurd hn (Nat.not_lt_zero n)) hcover_one
    (fun n hn => absurd hn (Nat.not_lt_zero n)) () 0 0 (mem_ball_self one_pos) hinit_one
  trivial

end BouRabeeGwynne.Nonvacuity

#print axioms BouRabeeGwynne.Nonvacuity.firstFailure_bundle_witness
```

What it shows:
- The full hypothesis bundle of `walkBrownianJointLaw_firstFailure_le` at `k = 0`, `b = 1/2` is jointly satisfiable with a real standard Brownian law `μ = euclideanWienerLaw 1` (cited existing result `isStandardBrownianLaw_euclideanWienerLaw`). That covers the injectivity, `hB` (vacuous since `B = ∅`), boundedness and openness of `U`, the selector identity `hselect`, the diameter, cover, and inside hypotheses, and the stage-0 approximation `hinit`.
- `hinit` holds exactly here: both masses of the cell equal `1` (the walk side because the single vertex lies in the cell; the Brownian side because the stopped exit point lies in `closure (ball 0 1) = closedBall 0 1` almost surely). So `1/2 ≥ 0` is the only real inequality.
- The result is a consistency witness only. It does not witness `herror` (stages `n < k`, so `k ≥ 1`), it uses a trivial walk (`B = ∅`, no edges), and it does not instantiate the Section 3 tiling bundles. `SpherePackings.exists_lattice_tilingSequence` was not needed for this and was not used.

## Not checked
- `CurveSpace.endPoint`, `levyProkhorovEDist` and `innerDomain` are referenced but defined outside this batch; I read their definitions only where needed (`innerDomain`: BrownianInnerExit.lean:15–16; `CurveSpace`: CurveSpace.lean:25–217, skimmed).
- Paper-correspondence claims for Theorems 3.3, 3.6, 3.7 and Proposition 2.6 are not in this batch and were taken from CORRESPONDENCE.md where cited.
