# Audit batch 7
| Module | Verdict | Summary |
|---|---|---|
| BouRabeeGwynne.GraphMeasure | OK | Graph area factor sqrt(1+‖b‖²) and affine-graph measure/integral transport are the standard ones. |
| BouRabeeGwynne.HyperplaneGraph | NOTE | Slope/intercept divide by `a none` (x/0 = 0 at `a none = 0`); every parametrization statement carries `a none ≠ 0`. |
| BouRabeeGwynne.CoordinateHyperplane | OK | Coordinate deletion/reparametrization of `a·x=c` and its area/flux formulas match the hyperplane formulas. |
| BouRabeeGwynne.Section3PlanarEstimate | OK | Planar good-box and column-measure estimates; `mesh ≠ ⊤` is an explicit hypothesis wherever `mesh.toReal` is used. |
| BouRabeeGwynne.Approximation | NOTE | (1.3) encoded faithfully; `NearestVertexData` presupposes minimizers exist for all z ∈ D, which the paper also presupposes but does not prove (see below). |
| BouRabeeGwynne.ApproximationGeometry | OK | Consequences of (1.3): eventual finite mesh, uniform nearest-vertex error, eventual cell inclusion. |
| BouRabeeGwynne.NearestVertexExistence | OK | Nearest vertex exists when `closedBall z r ⊆ D` with `mesh.toReal ≤ r`; hypotheses as stated. |
| BouRabeeGwynne.EventualLocalRegion | NOTE | Docstring says "external" vertices, but the statement covers all of `closedVertices U` (stronger, true). |
| BouRabeeGwynne.Section3CompactCollar | OK | Compact collar Q, Hessian bound M, continuity modulus; each conjunct matches the docstring. |
| BouRabeeGwynne.Section3EdgeSums | OK | Handshaking identity for ordered vs. unordered edge sums. |
| BouRabeeGwynne.Section3EnergyNormalization | OK | Oriented-edge sums, `incidentEnergy` = network energy when exterior values vanish, mass = Σ facetVolume·edgeLength. |
| BouRabeeGwynne.DualDirichlet | NOTE | `dualEnergy` divides by `a w v`, so off-edge θ contributes 0; all uses force θ = 0 where a = 0. Lemma 2.3 statement matches. |
| BouRabeeGwynne.FiniteFluxEnergy | OK | Energy = ½ dual energy of gradient; Dirichlet argument order checked against the definition. |
| BouRabeeGwynne.FluxResidual | OK | Pointwise Taylor residual on balls, uniform over short pairs near U; constants depend only on h, U, W. |
| BouRabeeGwynne.FacetFlux | OK | Surface flux v→w is the outward normal flux of cell v; residual bound and integrability as stated. |
| BouRabeeGwynne.SupportedSurfaceField | OK | Index convention `(w,v)` gives discrete divergence at v = outward flux from v; residual-to-energy bound correct. |
| BouRabeeGwynne.SupportFaceProjection | OK | Actual face slices and upper/lower active regions; projection identities as stated. |
| BouRabeeGwynne.FacetProjection | OK | Projection of contact facets to upper/lower endpoints; overlap projection statements correct. |
| BouRabeeGwynne.ContactCoordinateFlux | OK | Coordinate-normal contact flux equals ± integral over upper/lower endpoint projection. |
| BouRabeeGwynne.TripleContact | OK | Triple contacts have rank < d−1; pairwise contact overlaps are surface-null. |
| BouRabeeGwynne.FacetPartition | OK | Boundary of a cell is the surface-disjoint union of its (possibly partial) contacts. |
| BouRabeeGwynne.Section3ParallelFacetProjection | OK | Contacts parallel to the column direction project to a surface-null set. |
| BouRabeeGwynne.ProjectedContactPartition | OK | a.e. decomposition of projected bases into upper/lower contact projections. |

Totals: OK 19, NOTE 4, ISSUE 0. No `Upstream/` module is in this batch, so check 3 does not apply.

## BouRabeeGwynne.GraphMeasure
- `graphLinear_normDet` (line 63): normDet = sqrt(1+‖b‖²); matches the standard graph area factor of a linear functional.
- `graphLinear_measure_image` (81), `affineGraph_measure_image` (100): μHE[card ι] of graph images = sqrt(1+‖b‖²)·volume; the Hausdorff index is the graph dimension card ι, which is correct.
- `graphLinear_normDet_of_isEmpty` (75): area factor 1 for empty ι; consistent with the general formula.
- `affineGraph_integral_image` (140): area-formula transport; matches.

## BouRabeeGwynne.HyperplaneGraph
- `hyperplaneSlope` (26–27), `hyperplaneIntercept` (33–35): NOTE. `-a (some i) / a none` and `c / a none` are x/0 = 0 when `a none = 0`, so these are not a graph description there. All parametrization statements take `ha : a none ≠ 0`: `range_hyperplaneGraph` (101), `hyperplaneGraph_image` (112), `hyperplaneGraph_areaFactor` (146), `hyperplaneGraph_measure_image` (154), `hyperplaneGraph_signed_integral` (184). `hyperplaneGraph_apply_none` (65) is a formula without `ha`, true as an identity; junk only at `a none = 0`, and it does not claim parametrization.
- `hyperplaneGraph` (46): affine graph of {a·x = c} over the ι-coordinates; the none-coordinate (c − Σ a_i q_i)/a_none (line 67) is correct.
- `hyperplaneGraph_areaFactor` (146): sqrt(1+‖slope‖²) = ‖a‖/|a none|; matches the hyperplane area factor, no nonemptiness hypothesis needed.
- `hyperplaneGraph_signed_integral` (184): ∫ (a_none/‖a‖) f dH over the patch = sign(a_none)∫ f(graph) dq; correct.

## BouRabeeGwynne.CoordinateHyperplane
- `coordinateChart` (21), `coordinateProjection` (32), `coordinatePlaneGraph` (39): delete coordinate i, parametrize {a·x=c} by the other coordinates; the chart is a linear isometry so norms and measures are preserved. The projection is the paper's proj_j (tex line 923).
- `coordinate_hyperplane_measure_projection` (98): μHE[n] s = (‖a‖/|a_i|)·volume(proj s); matches the area formula.
- `coordinate_hyperplane_integral_projection` (64): signed flux with weight a_i/‖a‖ = sign(a_i)·∫ over the projection; matches.
- `coordinate_perpendicular_measure_projection` (177): the special case a = e_i, c = 0; correct.

## BouRabeeGwynne.Section3PlanarEstimate
- `planar_hyperplaneProjection` (17): projection onto e_{i.rev}^⊥ is x_i e_i; correct for Fin 2.
- `exists_planar_good_box` (42): cuts lie in (x0−2r, x0−r) and (x0+r, x0+2r) and avoid the bad base via μHE[1] ≤ ℓ < r; consistent with the docstring.
- `planar_good_box_diameter` (69): proves dist ≤ 8r; the true bound is 4√2·r, so the claim is valid and nonsharp, as documented.
- `planar_error_le_of_column_measure` (103), `planar_error_le_of_energy_bound` (138): `mesh ≠ ⊤` is an explicit hypothesis (lines 112, 148), so `mesh.toReal ⊤ = 0` cannot be exploited.

## BouRabeeGwynne.Approximation
- `NearestVertexData` (16–20): a total vertex map with `isNearest` only for z ∈ domain. This matches the paper's sup over z ∈ D (tex 264) and "z^n the nearest vertex" (tex 261, 1422). Lexicographic tie-breaking is not formalized; the statement allows any minimizer, which is the stronger reading.
- NOTE, the existence presupposition. `isNearest` is a hypothesis of the structure, so a `NearestVertexData G` exists only if a global minimizer of dist(z, pos v) over all v exists for each z ∈ D. Existence is not automatic. `exists_nearest_vertex` (NearestVertexExistence:22) needs `closedBall z r ⊆ D`, so it does not cover z within a mesh of ∂D. Hand-sketched counterexample (not compiled): in d = 1 with D = [0,1], take the cells [0,0.1],…,[0.9,1] (so z = 1 has nearest interior vertex at 0.95, distance 0.05), plus infinitely many interval cells outside D accumulating at 1.01 from above with positions 1.01 + c·2^{−k}. Local finiteness on D holds, cells have disjoint interiors, and the infimum of dist(1, pos v) is 0.01, approached but not attained. Then no `NearestVertexData G` exists, so Theorems A and B are vacuous for that G. The paper's "let z^n be the nearest vertex" carries the same presupposition, so this is inherited rather than a Lean error. Recorded as NOTE.
- `uniformError` (31): ⨆ over z ∈ D of dist(pos(vertex), z); matches the sup over D in (1.3).
- `ApproximationCondition` (40–43): Tendsto (mesh + uniformError) → 0 in ℝ≥0∞, matching tex 264–265 (ε_n = sup diam). The ENNReal limit forces `mesh ≠ ⊤` eventually (ApproximationGeometry:14), so no ⊤ junk survives.

## BouRabeeGwynne.ApproximationGeometry
- `eventually_mesh_finite_le` (14), `eventually_vertex_dist_le` (23), `eventually_interior_cells_subset_domain` (34): consequences of ApproximationCondition alone; correct.

## BouRabeeGwynne.NearestVertexExistence
- `vertices_in_compact_finite` (14): from local finiteness; correct.
- `exists_nearest_vertex` (22): hypotheses `0 < r`, `closedBall z r ⊆ D`, `mesh ≠ ⊤`, `mesh.toReal ≤ r`; conclusion is a global minimizer. Matches the docstring.

## BouRabeeGwynne.EventualLocalRegion
- `eventually_closedVertices_in_neighborhood` (36–45): NOTE. The docstring says "every external graph vertex", but the statement quantifies over all of `closedVertices U` (= V[U] ∪ ∂V[U], which includes interior vertices). The statement is stronger and true as proved; only the docstring wording understates it.
- `eventually_closedVertices_finite` (16), `eventually_interior_neighbors_finite` (26), `eventually_exists_nearest_vertex` (49): correct and match their docstrings.

## BouRabeeGwynne.Section3CompactCollar
- `HarmonicNearClosure.exists_compact_collar` (17–25): conjuncts `closure U ⊆ interior Q`, `Q ⊆ W`, `Q ⊆ interior D`, `cthickening ρ (closure U) ⊆ Q`, uniform continuity on Q, and the Hessian bound M on Q all hold as stated. Satisfiable (constant case in Nonvacuity).
- `closedVertex_ball_subset_cthickening` (53), `eventually_closedRegion_in_compact_collar` (72): correct.

## BouRabeeGwynne.Section3EdgeSums
- `sum_adjacent_pairs_eq_twice_edge_sum` (21), `edge_sum_eq_half_sum_adjacent_pairs` (55): handshaking identities; correct.

## BouRabeeGwynne.Section3EnergyNormalization
- `sum_orientedInteriorEdges_eq_half_ordered` (16): once-per-edge sum equals ½ of the ordered sum; correct.
- `incidentEnergy_eq_networkEnergy` (48): holds when f = 0 off A (hzero), which is what removes exterior–exterior edges; correct.
- `incidentMass_eq_half_ordered` (75): mass = Σ facetVolume·|w−v| = Σ conductance·|w−v|²; consistent.

## BouRabeeGwynne.DualDirichlet
- `FiniteConductanceNetwork.dualEnergy` (14–15): NOTE. `(θ w v)^2 / N.a w v` is x/0 = 0 on zero-conductance pairs, so a nonzero θ off the edge set contributes 0 silently. Every use (`dual_variational_principle` at line 21 and its callers in FiniteFluxEnergy) assumes `θ = 0` where `a = 0`, so the junk cannot change any conclusion.
- `dual_variational_principle` (19–24): Thomson-type minimality of the gradient flux among fields with matching divergence on A and support on edges. Matches Lemma 2.3 (CORRESPONDENCE.md).

## BouRabeeGwynne.FiniteFluxEnergy
- `energy_eq_half_dualEnergy_weightedGradient` (15): energy = ½Σa(Δf)² = ½·dualEnergy(a∇f); matches `energy` (DiscretePDEAlgebra:113–114).
- `energy_error_le_flux_residual` (32), `energy_error_le_incident_flux_residual` (68): `SolvesDirichlet A g f` has the solution in the second slot, as in the definition (FiniteDirichlet:23–24); the conclusions are the Proposition 2.6-type bound with the genuine residual.

## BouRabeeGwynne.FluxResidual
- `fluxResidual_bound_on_closedBall` (19–27): |h w − h v − Dh(y)(w−v)| ≤ 3Mε‖w−v‖ for dist(v,w) ≤ 2ε and dist(v,y) ≤ ε; correct (‖x−y‖ ≤ 3ε on the ball).
- `exists_collar_derivative_bounds` (69), `exists_uniform_fluxResidual_bound` (99): constants depend only on h, U, W; no convexity of U needed; correct.

## BouRabeeGwynne.FacetFlux
- `unitEdgeDirection` (33): zero only when the marked points coincide, which never happens for adjacent v, w (pos injective).
- `surfaceFlux` (48–49): ∫ over facet v w of ∂ in direction (w−v)/‖w−v‖ with μHE[d−1]; the outward normal flux of cell v, matching tex 673 (ν = (w−v)/‖w−v‖).
- `surfaceFlux_residual_bound_on_closedBall` (80–88): |c(v,w)(h w − h v) − surfaceFlux| ≤ 3M·mesh·|F|; correct single-contact Taylor estimate.
- `exists_uniform_surfaceFlux_residual_bound` (139–148): integrability is part of the conclusion, so the Bochner junk value 0 is excluded.

## BouRabeeGwynne.SupportedSurfaceField
- `supportedSurfaceField` (15–16): `supportedSurfaceField h w v = surfaceFlux h v w` when adj (line 19), so `discreteDiv` at v is the outward flux from v (line 44). Matches the paper's divergence convention.
- `residual_dual_energy_bound` (64–68): r²/c ≤ C²·|F|·|w−v| given |r| ≤ C|F|; correct, with c > 0 from adjacency.

## BouRabeeGwynne.SupportFaceProjection
- `supportFace` (24–25), `upperActiveRegion` (28), `lowerActiveRegion` (33): definitional; `supportFace` is the actual slice P ∩ {plane} and may be lower-dimensional, as intended. `planeParameter` (HalfspaceFibers:60–61) divides by ⟨n,e⟩, which is nonzero by the `hn` hypotheses.
- `project_supportFace_eq_upperActiveRegion` (113), `supportFace_eq_upperEndpoint_image` (149), `projectedBase_eq_iUnion_upperActiveRegion` (166): correct.

## BouRabeeGwynne.FacetProjection
- `project_facet_subset_projectedBase` (20), `upperFiber_eq_lineParameter_of_mem_facet` (25), `upperEndpoint_projection_of_mem_facet` (78): hypotheses (1 ≤ d, adjacency, positive transverse component) are the ones needed; correct.
- `project_facet_inter_of_pos` (98), `project_facet_inter_of_neg` (113): projection commutes with intersection on same-sign contacts; correct.

## BouRabeeGwynne.ContactCoordinateFlux
- `coordinate_hyperplane_integral_perpendicular_projection` (18–24): ∫_s (a_i/‖a‖) f dH^{n+1} = sign(a_i)·∫ over the n-dimensional perpendicular projection with μHE[n]; dimensions consistent.
- `integral_upper_contact_eq_projection` (57–62), `integral_lower_contact_eq_projection` (79–84): ±integral over the upper/lower endpoint projection, with the sign of (w−v)_i selecting the branch; correct.

## BouRabeeGwynne.TripleContact
- `triple_contact_rank_lt` (55–58): distinct v, w, u with a nonempty triple intersection give affine rank < d−1; correct, using the disjoint-interior separators.
- `facet_inter_facet_measure_zero` (122–124): pairwise contact overlaps are surface-null; correct.

## BouRabeeGwynne.FacetPartition
- `contactFinset` (16–17): the finite set of touching cells (w ≠ v, nonempty facet), including lower-dimensional contacts as the docstring says; correct.
- `frontier_restrict_eq_sum_contacts` (32), `frontier_measure_eq_sum_contacts` (61), `frontier_measure_ne_top` (72), `integral_frontier_eq_sum_contacts` (87): correct.

## BouRabeeGwynne.Section3ParallelFacetProjection
- `projected_parallel_facet_measure_zero` (23–27): e ⊥ (w−v) gives a projection of affine rank < d−1, hence surface-null; the d = 1 case is vacuous because w−v ≠ 0 contradicts parallelism. Correct.

## BouRabeeGwynne.ProjectedContactPartition
- `upperContactFinset` (17–21), `lowerContactFinset` (23–27): adjacency plus sign filters of `contactFinset`; correct.
- `projectedBase_ae_eq_iUnion_upperContacts` (54), `projectedBase_ae_eq_iUnion_lowerContacts` (135): a.e. equalities of the projected base with the union of upper/lower contact projections; correct.
- `integral_projectedBase_eq_sum_upperContacts` (217–222): correct.

## Context outside this batch (not counted in the table)
- `RegularityII` (`BouRabeeGwynne/PaperObjects.lean` 207–213): NOTE. `mesh.toReal` is 0 when mesh = ⊤, so the clause `mesh.toReal · q n → 0` holds trivially for infinite-mesh sequences, and the standalone predicate is not self-contained as the paper's (II), which presupposes finite ε_n. All consumers also assume `N.ApproximationCondition`, which forces `mesh ≠ ⊤` eventually (TheoremAStatement:39; TheoremBStatement:102, 114; Frozen `theorem36_qualitative` and `theorem37_qualitative`; Section3CaseIITarget:31; Section3CaseIIITarget). The junk is therefore unobservable in every theorem.
- `TilingData.conductance` (PaperObjects 132–133, ENNReal): self-loop gives facetVolume v v / 0 = ⊤ (the d-dimensional cell has μHE[d−1] = ⊤), so the ENNReal `conductance` is junk on the diagonal. It is used only under `adj` guards (FacetMeasure 105, 109); `conductanceReal` (DiscretePDE:17) is the one used in statements.
- `RegularityI` (200), `RegularityIII` (216–220), `incidentScale` (165–168): match tex 269–271 (planarity; O(max over incident edges) with α > 0). `PaperRegularity` (223–224) matches "at least one of the three conditions".
- `conductance` (PaperObjects 132–133) and `(1.1)`: matches tex 233–236 (cond(w,v) = vol_{d−1}(P_w∩P_v)/‖w−v‖).

## Nonvacuity examples
File: `Nonvacuity.lean`, compiled from the repository root with `lake env lean …/Nonvacuity.lean`. Exit status 0, no errors, no warnings. `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound` for both theorems, so neither hides a `sorry`.

```lean
import SpherePackings.Support.Guards.LatticeTilings
import SpherePackings.Support.Guards.LipschitzBall
import BouRabeeGwynne.TheoremAStatement
import BouRabeeGwynne.Harmonic

open MeasureTheory Metric
open scoped Topology

namespace A07Audit

open BouRabeeGwynne

/-- The hypotheses shared by Theorems A and B (domain, bounded, ambient collar, (1.3) for every
choice of nearest vertices, and the regularity disjunction) are jointly satisfiable in every
dimension `d ≥ 1`, by the lattice Voronoi tilings on the unit ball. -/
theorem lattice_premises_satisfiable {d : ℕ} (hd : 1 ≤ d) :
    ∃ (G : TilingSequence d) (N : NearestVertexData G) (U : Set (Euc d)),
      IsLipschitzDomain U ∧ Bornology.IsBounded U ∧ HasAmbientCollar U G.domain ∧
      N.ApproximationCondition ∧ PaperRegularity G := by
  obtain ⟨G, hcollar, ⟨N⟩, hall, hII⟩ := SpherePackings.exists_lattice_tilingSequence hd
  exact ⟨G, N, ball (0 : Euc d) 1, SpherePackings.isLipschitzDomain_ball hd, isBounded_ball,
    hcollar, hall N, Or.inr (Or.inl hII)⟩

/-- The zero function is harmonic on a neighbourhood of the closure of the unit ball, so the
`HarmonicNearClosure` hypothesis of the Section 3 collar lemmas is satisfiable. -/
theorem zero_harmonicNearClosure {d : ℕ} : HarmonicNearClosure (fun _ : Euc d => (0 : ℝ)) (ball (0 : Euc d) 1) :=
  ⟨ball (0 : Euc d) 2, isOpen_ball,
    closure_ball_subset_closedBall.trans (closedBall_subset_ball (by norm_num)),
    ⟨contDiffOn_const, fun x _ => by simp⟩⟩

end A07Audit

#print axioms A07Audit.lattice_premises_satisfiable
#print axioms A07Audit.zero_harmonicNearClosure
```

Output of the compile: `'A07Audit.lattice_premises_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound]` and `'A07Audit.zero_harmonicNearClosure' depends on axioms: [propext, Classical.choice, Quot.sound]`.

What they show:
- `lattice_premises_satisfiable`: for every d ≥ 1 there is a `TilingSequence` with a `NearestVertexData`, a bounded Lipschitz U (the unit ball), the ambient collar, `ApproximationCondition` for every choice of nearest vertices, and `PaperRegularity` via hypothesis (II). So the joint premise of Theorems A and B is satisfiable and not vacuous. This relies on `exists_lattice_tilingSequence`, whose proof I did not review; the example only assembles it. Hypotheses (I) and (III) are not separately witnessed.
- `zero_harmonicNearClosure`: `HarmonicNearClosure` holds for the zero function. This is only the trivial case; a non-constant harmonic witness was not attempted within the time budget. The constant case shows the bundle is satisfiable, not that it is non-degenerate.
- Not attempted: a witness for `RegularityIII` (no lattice cell computation was attempted) and a hand-checked counterexample to `NearestVertexData` existence beyond the sketch above.

RESULT: DONE — verdicts: OK 19, NOTE 4, ISSUE 0.
