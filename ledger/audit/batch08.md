# Audit batch 8
| Module | Verdict | Summary |
|---|---|---|
| BouRabeeGwynne.CoordinateVolume | OK | Coordinate splitting is measure-preserving with Euclidean normalization; Fubini statement is the standard one. |
| BouRabeeGwynne.FiberCalculus | OK | FTC along a fiber; fiber endpoints are inf'/sup' over nonempty constraint sets, so no junk value enters. |
| BouRabeeGwynne.CoordinateFiberFubini | OK | Coordinate divergence identity over a cell, with upper endpoint signed +, lower endpoint −, as printed. |
| BouRabeeGwynne.CoordinateLaplacian | OK | Σᵢ ∂²ᵢᵢ h equals Mathlib's Δ (trace of Hessian, standard sign). |
| BouRabeeGwynne.PolytopeGaussGreen | OK | Sum over contacts of outward flux equals ∫Δh; (pos w − pos v) is outward for P_v by orthogonality. |
| BouRabeeGwynne.SurfaceEnergyEstimate | NOTE | Hessian estimate has the PARTIAL Prop 2.6 hypotheses (2·mesh balls, global mesh), not flagged in the docstring; `mesh ≠ ⊤` guards the `toReal`. |
| BouRabeeGwynne.Section3HarmonicInput | ISSUE | Docstring calls `harmonic_error_energy_le_incidentMass` "Proposition 2.6", but the statement is the weaker PARTIAL variant (Hessian bound on 2·mesh balls around all of R, global mesh). |
| BouRabeeGwynne.Section3MassTrimming | NOTE | Unscaled trimming lemma uses one δ both as edge-length cap and trimming threshold; correct but narrower; the scaled lemma (used downstream) has independent L, ℓ. |
| BouRabeeGwynne.DualCells | OK | `cellPyramid`, `dualPolytope`, `dualVolume` match the paper's Q_e = conv(w, P_w∩P_v) ∪ conv(v, P_w∩P_v) (rw-spheres.tex:725–728). |
| BouRabeeGwynne.PyramidSlices | OK | Perpendicular slices and homothety are correct; the `t ≠ 0` hypothesis of the slice-measure formula is genuinely needed. |
| BouRabeeGwynne.Section3CylinderVolume | NOTE | `orthogonalCylinder` is junk for e = 0 (x/0 = 0); harmless since every lemma takes `e ≠ 0`. Volume formula is correct. |
| BouRabeeGwynne.ConeIntegrals | OK | ∫₀ʳ (t/r)ᵏ dt = r/(k+1) and its lintegral/nnnorm variants; all need and have r > 0. |
| BouRabeeGwynne.PyramidVolume | OK | Cone volume ‖e‖·(r/d)·area(base), i.e. base × height / d, with height r‖e‖. |
| BouRabeeGwynne.FacetPyramidHeights | OK | Each contact lies in the slice at a height r ∈ (0,1) from its apex, from orthogonality. |
| BouRabeeGwynne.DualAdditivity | OK | The two halves of a dual cell meet exactly in the facet; dual volume is the sum of the two pyramid volumes. |
| BouRabeeGwynne.DualVolume | OK | dualVolume = ‖e‖·vol_{d−1}(F)/d, matching the paper's ‖w−v‖·vol_{d−1}(H_e) = d·vol_d(Q_e) (rw-spheres.tex:741–743). |
| BouRabeeGwynne.DualNull | OK | Non-adjacent contacts have affine rank < d−1, so their dual cells are null; `IsCodimOneFacet` used correctly. |
| BouRabeeGwynne.PyramidOverlap | OK | Two pyramids from one apex overlap only over the cone on the common base; the overlap is null. |
| BouRabeeGwynne.DualVolumeSums | OK | Dual cells of distinct oriented edges have null overlap; the sum of dual volumes equals the volume of the union. |
| BouRabeeGwynne.Section3InternalMass | OK | Bad-column cylinder bounds, dual-volume identity and once-oriented mass convention are consistent. |
| BouRabeeGwynne.Section3Accessibility | OK | Positive projected-base measure gives positive-conductance exit paths; `BoundaryAccessible` matches its definition. |
| BouRabeeGwynne.TilingDirichlet | OK | The selected Dirichlet solution is unique on the closed region; values elsewhere are documented as unconstrained. |
| BouRabeeGwynne.BoundarySampling | OK | `Classical.choose` is used only through spec lemmas; the nearest closure point exists for nonempty U in a proper space. |
| BouRabeeGwynne.BoundaryGeometry | OK | Minimizing boundary samples lie on the frontier and within 2·mesh of the external vertex. |
| BouRabeeGwynne.TheoremBStatement | NOTE | Branch statements match the paper's (a)/(b); the ∀S clause is non-vacuous (checked); `toReal ⊤ = 0` in PaperRegularity clause (II) is harmless given `ApproximationCondition`. |
| BouRabeeGwynne.Section3WellPosed | OK | An accessible vertex forces a positive mesh; eventual unique Dirichlet extension as stated. |
| BouRabeeGwynne.Section3PlanarTarget | NOTE | Proves only the d = 2 instance of Theorem B(a), as its docstring says; premises are weaker than `TheoremBPartAStatement` at d = 2, so it is a stronger planar instance, not the general target. |

## BouRabeeGwynne.CoordinateVolume
- `coordinateVolumeEquiv` (line 21): Euc(n+1) ≃ᵐ Euc n × ℝ with horizontal coordinates first; matches the docstring.
- `coordinateInsert` (line 31): inverse of the equivalence at (y, t); coordinate i equals t (`coordinateInsert_apply` in CoordinateFiberFubini.lean:38).
- `measurePreserving_coordinateVolumeEquiv` (line 36): both sides carry Euclidean/product normalization; no Jacobian constant. Matches the docstring.
- `integral_eq_integral_coordinate_slices` (line 46): Fubini along a coordinate line, hypothesis `Integrable f`; standard.

## BouRabeeGwynne.FiberCalculus
- `integral_fderiv_fiber_eq_sub` (line 19): FTC of the directional derivative along the fiber [lowerFiber, upperFiber]. `upperFiber`/`lowerFiber` (HalfspaceFibers.lean:63, 66) are inf'/sup' over nonempty filtered constraint sets (lemmas `upperConstraints_nonempty`, `lowerConstraints_nonempty`), so there is no junk. `hbounds` (line 22) excludes empty fibers.

## BouRabeeGwynne.CoordinateFiberFubini
- `coordinateProjection_coordinatePlaneGraph` (line 19), `inner_coordinatePlaneGraph` (line 25), `coordinateInsert_eq_line` (line 43), `axisGraph_mem_projectedBase` (line 60), `coordinateInsert_not_mem_of_not_mem_projectedBase` (line 70): correct bookkeeping; `inner` hypothesis `a i ≠ 0` (line 26) is the needed one.
- `integral_coordinate_fderiv_eq_endpoint_integral` (line 82): ∫_P ∂_{e_i} h = ∫_{projectedBase} (h∘upper − h∘lower) dμHE[n]. This is the coordinate divergence theorem with the right signs. Hypotheses (open W ⊇ carrier, C¹ on W) are satisfiable.

## BouRabeeGwynne.CoordinateLaplacian
- `contDiffOn_directional_fderiv` (line 23), `fderiv_directional_fderiv` (line 29): correct regularity and Hessian-symmetry bookkeeping.
- `laplacian_eq_sum_coordinate_second` (line 41): Δh(x) = Σᵢ D²h(x)(eᵢ, eᵢ) with Mathlib's `Δ`, the trace of the Hessian. This is the standard Laplacian, matching the docstring.
- `continuousLinearMap_apply_eq_sum_coordinates` (line 53): correct.

## BouRabeeGwynne.PolytopeGaussGreen
- `upperContactFinset_eq_filter_neighborFinset` (line 19), `lowerContactFinset_eq_filter_neighborFinset` (line 32): correct.
- `integrableOn_upperEndpoint` (line 45), `integrableOn_lowerEndpoint` (line 62): correct.
- `sum_coordinate_contact_integral_eq_integral_fderiv` (line 81): correct.
- `surfaceFlux_eq_sum_coordinate_contact_integral` (line 132): `surfaceFlux` (FacetFlux.lean:48) integrates ∇h · unitEdgeDirection v w over the facet. The direction (pos w − pos v)/‖·‖ is outward from P_v: the facet separates pos v ∈ P_v from pos w ∈ P_w, and orthogonality makes the facet normal exact.
- `sum_surfaceFlux_eq_integral_laplacian_succ` (line 166), `sum_surfaceFlux_eq_integral_laplacian` (line 211): Σ_w flux = ∫_{P_v} Δh. The hypothesis `hvD` (P_v ⊆ interior domain) is what makes the neighbour facets exhaust ∂P_v. Correct Gauss–Green with Mathlib Δ.
- `sum_surfaceFlux_eq_zero_of_harmonic` (line 223): correct (`IsHarmonicOn` is Δ = 0 on an open set, Harmonic.lean:17).

## BouRabeeGwynne.SurfaceEnergyEstimate
- `energy_error_le_surfaceFlux_mass` (line 17): conditional lemma. `hdiv` (line 20) and `hres` (line 22) are explicit obligations, as the docstring (lines 14–16) says; they are discharged downstream. Energy is ½ Σ over ordered pairs (DiscretePDEAlgebra.lean:113), matching the normalization.
- `energy_error_le_hessian_mesh_mass` (line 75): the Hessian bound `hH` (lines 84–85) is on `closedBall (pos v) (2·mesh)` for every v ∈ R, and ε is the global `T.mesh` (`hmesh`, line 77). Printed Prop 2.6 (rw-spheres.tex:823–842) takes M over G_U = ⋃_{v∈V̄[U]} P_v and ε = sup over V̄[U] of diam P_v. So this is the PARTIAL form recorded in CORRESPONDENCE.md, a weaker statement. The docstring (lines 72–74) does not claim Prop 2.6. The constant 9 = 3² is right. `hmesh` correctly guards `toReal`.
- `ordered_energy_error_le_hessian_mesh_mass` (line 117): `dualEnergy (weightedGradient ·)` is the paper's D(f,A) (rw-spheres.tex:813) with E taken directed (rw-spheres.tex:557–558). The normalization is correct. The docstring says "the same estimate", which inherits the hypothesis departure above without saying so.

## BouRabeeGwynne.Section3HarmonicInput
- `harmonic_error_energy_le_incidentMass` (line 17): ISSUE. The docstring (lines 15–16) says "Proposition 2.6 in the exact once-oriented energy/mass normalization". The statement is not the printed Prop 2.6:
  - `hH` (lines 26–27) requires ‖D²h‖ ≤ M on `closedBall (pos v) (2·mesh)` for every v ∈ R. That region contains the printed G_U = ⋃_{v∈V̄[U]} P_v, so the lemma applies to fewer h.
  - `hmesh` (line 19) and the bound use the global `T.mesh` rather than sup_{V̄[U]} diam P_v, so ε can be larger.
  - Both departures make the statement weaker than printed Prop 2.6. CORRESPONDENCE.md and README "Open" already register Prop 2.6 as PARTIAL, so only the docstring overclaims. The constant 9 = 3² and the once-oriented `incidentMass` normalization are correct.
  - I did not construct a concrete h separating the two hypothesis sets.
  - Fix: reword the docstring as the partial form of Proposition 2.6.
- `harmonic_error_energy_le_for_subsets` (line 49): correct; the subset S ⊆ A inherits all hypotheses.

## BouRabeeGwynne.Section3MassTrimming
- `facet_weight_le_scaled_gradient_energy` (line 18): facetVol·len = cond·len² ≤ cond·L² ≤ (L²/ℓ²)·cond·(f w − f v)² using ℓ < |f w − f v|. Correct.
- `internalMass` (line 42): ½ Σ over ordered pairs with adj ∧ both endpoints in B, so each unordered edge is counted once. This matches the once-oriented `incidentMass` (Section3ColumnEstimate.lean:20).
- `incidentMass_trimmed_le_internalMass_add_energy` (line 49): NOTE. `hlength` (line 51) caps every edge by the same δ that is the trimming threshold (`trimmedErrorSet` with δ). The statement is correct but applies only when all edges have length ≤ δ. The general version is `incidentMass_trimmed_le_internalMass_add_scaled_energy` (line 100) with independent L and ℓ, which the contraction lemma uses (Section3InternalMass.lean:260).
- `incidentMass_trimmed_le_internalMass_add_scaled_energy` (line 100): correct; the coefficient records the global length bound, as its docstring says.

## BouRabeeGwynne.DualCells
- `convexHull_insert_eq_segment_image` (line 15), `isCompact_convexHull_insert_of_convex` (line 35): correct, including the empty-base case, which gives the singleton {a}.
- `cellPyramid` (line 48): conv({pos v} ∪ facet v w). Correct.
- `dualPolytope` (line 52): cellPyramid v w ∪ cellPyramid w v. This matches the paper's Q_e = conv(w, P_w∩P_v) ∪ conv(v, P_w∩P_v) (rw-spheres.tex:725–728).
- `dualVolume` (line 56): μHE[d] of the dual polytope = vol_d(Q_e). Correct.
- `dist_pos_le_mesh_of_mem_cellPyramid` (line 106): `hmesh` (line 107) guards the `toReal`. Correct.

## BouRabeeGwynne.PyramidSlices
- `perpendicularSlice` (line 15), `mem_perpendicularSlice` (line 18): the slice {z : ⟪e, z−a⟫ = t·⟪e,e⟫} is the hyperplane at parameter t in units of e. Apex a lies in slice 0. Correct.
- `pyramid_slice_eq_homothety` (line 70), `pyramid_slice_eq_empty` (line 92): correct.
- `pyramid_slice_measure` (line 103): the hypothesis `ht0 : t ≠ 0` (line 106) is needed. At t = 0 the slice is {a}, and for k = 0 the formula would give 1 instead of #s. It is a real hypothesis, not junk.

## BouRabeeGwynne.Section3CylinderVolume
- `orthogonalCylinder` (line 21): NOTE. The parameter ⟪e,x⟫/⟪e,e⟫ has no `e ≠ 0` guard, so for e = 0 it is junk (x/0 = 0). Harmless: `orthogonalCylinder_slice` (line 31) and `orthogonalCylinder_volume` (line 67) take `he : e ≠ 0`, and no caller uses e = 0.
- `measurableSet_orthogonalCylinder` (line 24): correct.
- `orthogonalCylinder_volume` (line 67): μHE[d](cyl) = ‖e‖ₑ·ofReal(b−a)·μHE[d−1](Y). This is the correct length (b−a)‖e‖ times base area. ofReal(b−a) = 0 when b < a, consistent with the empty cylinder.

## BouRabeeGwynne.ConeIntegrals
- `integral_scaled_pow_Icc` (line 13), `lintegral_scaled_pow_Icc` (line 25), `lintegral_nnnorm_scaled_pow_Icc` (line 37): ∫₀ʳ (t/r)ᵏ dt = r/(k+1), in real, extended and nnnorm forms. Correct for r > 0.

## BouRabeeGwynne.PyramidVolume
- `pyramid_volume` (line 13): μHE[d](conv(a, s)) = ‖e‖ₑ·ofReal(r/d)·μHE[d−1](s). This is base × height / d with height r‖e‖. Correct; `hbase` and `hr` are satisfiable.

## BouRabeeGwynne.FacetPyramidHeights
- `perpendicularSlice_reverse` (line 9): correct reparametrization from the other apex.
- `exists_facet_height` (line 22): the contact lies in the slice perpendicular to pos w − pos v at a height r ∈ (0,1). This uses orthogonality. Correct.

## BouRabeeGwynne.DualAdditivity
- `facet_full_measure_zero` (line 15): μHE[d](facet) = 0 for v ≠ w, using d ≥ 1. Correct.
- `cellPyramid_inter_reverse` (line 26): the two halves meet exactly in the facet. Correct.
- `dualVolume_eq_pyramid_add` (line 38): dualVolume = sum of the two pyramid volumes. Correct.

## BouRabeeGwynne.DualVolume
- `dualVolume_eq` (line 17): dualVolume = ‖pos w − pos v‖ₑ·ofReal(1/d)·facetVolume. The heights r and 1−r sum to 1. This matches the paper's ‖w−v‖·vol_{d−1}(H_e) = d·vol_d(Q_e) (rw-spheres.tex:741–743).
- `edgeLength_mul_facetVolume_eq_dim_mul_dualVolume` (line 56): the real-valued form. Correct.

## BouRabeeGwynne.DualNull
- `cellPyramid_finrank_le` (line 17), `cellPyramid_measure_zero_of_nonadjacent_contact` (line 26), `dualVolume_eq_zero_of_nonadjacent_contact` (line 41): ¬adj with a nonempty facet forces rank < d−1 (adjacency is `IsCodimOneFacet`, PaperObjects.lean:61–63), so the dual cell is null. Correct.

## BouRabeeGwynne.PyramidOverlap
- `cellPyramid_inter_subset_cone_contact_inter` (line 17): two pyramids from one apex intersect inside the cone over F_vw ∩ F_vu. Correct.
- `cellPyramid_inter_measure_zero` (line 68): null overlap, using `hwu : w ≠ u` (line 69). Correct.

## BouRabeeGwynne.DualVolumeSums
- `cellPyramid_aedisjoint_of_apex_ne` (line 15), `cellPyramid_aedisjoint` (line 23), `dualPolytope_aedisjoint` (line 33): null overlaps for distinct primal cells and distinct oriented edges. Correct.
- `sum_dualVolume_eq_measure_union` (line 51), `sum_dualVolume_le_measure` (line 65): `hrev` excludes both orientations of one edge. Correct.

## BouRabeeGwynne.Section3InternalMass
- `orientedInteriorEdges_no_reverse` (line 18), `isCompact_columnBadSet` (line 41), `columnBadSet_perpendicular` (line 53), `cell_subset_badCylinder` (line 59), `dualPolytope_subset_badCylinder` (line 71): correct.
- `internalEdges` (line 83), `internalMass_eq_sum_internalEdges` (line 95): correct.
- `sum_facet_weight_le_dim_mul_volume` (line 120): facetVol·len = d·dualVol (line 136). Correct.
- `incidentMass_le_dim_mul_volume` (line 144), `internalMass_bad_le_cylinder_volume` (line 161), `internalMass_bad_le_of_column_bound` (line 189): correct.
- `incidentMass_trimmed_le_contraction_factor` (line 224): `hzero` (line 228) gives zero exterior data; `hτ`, `hℓ`, `hC` are the needed positivity hypotheses. Correct.

## BouRabeeGwynne.Section3Accessibility
- `hyperplaneProjection_range` (line 15), `projectedBase_affine_rank` (line 29): rank d−1. Correct.
- `projectedBase_measure_pos` (line 52): positive (d−1)-measure of every cell's projected base, including d = 1 (counting measure). Correct.
- `finiteNetwork_boundaryAccessible_of_cell_interior` (line 69): `BoundaryAccessible` (FiniteDirichlet.lean:18) requires for every v ∈ A a positive-conductance path to some w ∉ A. The statement matches.

## BouRabeeGwynne.TilingDirichlet
- `neighbors_finite_of_finite_closed` (line 15), `dirichletSolution` (line 22), `dirichletSolution_apply_closed` (line 30), `dirichletSolution_apply_outside` (line 39), `dirichletSolution_spec` (line 47), `exists_dirichlet` (line 56), `eq_dirichletSolution_on_closed` (line 63), `dirichlet_stability_on_closed` (line 72), `dirichletSolution_stability_on_closed` (line 86): correct. `dirichletSolution` returns g off the closed region (documented, harmless). The solution is unique on the closed region (line 63), so the classical choice does not matter.

## BouRabeeGwynne.BoundarySampling
- `nearestClosurePoint` (line 19): `Classical.choose` of a nearest point (`Metric.exists_mem_closure_infDist_eq_dist`). Only the spec lemmas (lines 22, 26) are used, and every statement holds for any nearest point. Nonempty U in a proper space suffices, so there is no junk.
- `projectedBoundaryValue` (line 48), `closure_samples_uniform_control` (line 75), `projectedBoundaryValue_uniform_control` (line 95): correct; the uniform control is the expected continuity estimate on the compact closure.
- `nearestClosurePoint_mem_frontier` (line 116): a nearest closure point of x ∉ interior U lies on the frontier. Correct.

## BouRabeeGwynne.BoundaryGeometry
- `boundary_minimizer_dist_le` (line 15): a minimizer q over U is within 2·mesh of the external vertex w, by comparison with an adjacent interior vertex. Correct.
- `boundary_projection_mem_frontier` (line 23), `boundary_projection_dist_le` (line 29): correct; `hmesh` (line 30) guards `toReal`.

## BouRabeeGwynne.TheoremBStatement
- `HasUniqueDirichletExtension` (line 35): ∃ solution, unique on `closedVertices`. The existence clause prevents the solution quantifier in `DirichletApproximationTarget` from being vacuous. Correct.
- `DirichletApproximationTarget` (line 48): eventually finite closed region and unique extension, and for every η > 0 eventually the error bound for every solution. `DirichletError` (DiscretePDE.lean:110) is over interior vertices. Correct.
- `NearestClosureBoundaryChoices` (line 61): `point ∈ closure U` (line 64) and nearest over `closure U` (lines 65–66). Correct, and the structure is inhabited for nonempty U (`ofNonempty`, line 71; see Nonvacuity below).
- `boundaryData` (line 79): default 0 off the boundary. Harmless: `SolvesDirichlet` reads only boundary vertices (DiscretePDE.lean:107).
- `TheoremBPartAStatement` (line 98): matches Theorem B(a) with the ambient collar; the harmonic-near-closure premise is satisfiable (Nonvacuity example 3).
- `TheoremBPartBStatement` (line 110): matches B(b). The ∀S clause is guarded by the Nonempty clause (line 116) and is non-vacuous (Nonvacuity example 2). The frontier claim (line 118) and the 2·mesh claim (lines 119–120) are correct for every nearest choice.
- `TheoremBStatement` (line 124): correct conjunction.
- NOTE: `PaperRegularity` (PaperObjects.lean:223) includes `RegularityII` (PaperObjects.lean:207–213), which applies `ENNReal.toReal` to `mesh` and `minTileVolume`. If `mesh = ⊤` the decay clause is vacuous at that index (`toReal ⊤ = 0`). This is harmless in these statements because `ApproximationCondition` (Approximation.lean:40) forces `mesh` finite eventually. `RegularityII` on its own would admit tilings with unbounded cells.

## BouRabeeGwynne.Section3WellPosed
- `mesh_toReal_pos_of_accessible_vertex` (line 17): an accessible vertex gives a positive-conductance edge, so the mesh is positive. `hmesh` (line 19) guards the `toReal`. Correct.
- `NearestVertexData.eventually_uniqueDirichletExtension` (line 35): eventually the closed region is finite and the Dirichlet extension is unique for any boundary data, as stated.

## BouRabeeGwynne.Section3PlanarTarget
- `theoremB_part_a_planar` (line 20): NOTE. It proves only the planar (d = 2) instance, as its docstring (lines 17–19) says. It omits `IsDomain` (only boundedness and `HasAmbientCollar` are assumed) and `PaperRegularity`, which holds automatically for d = 2 through `RegularityI 2` (PaperObjects.lean:200). So it is a stronger d = 2 statement than `TheoremBPartAStatement`, but it does not cover the general-d target.

## Nonvacuity examples
Scratch file `Nonvacuity.lean`, compiled from the repository root with `lake env lean`, wrapped in `timeout 900`. Exit code 0, no errors or warnings. `#print axioms` output:

```
'nonvac_shared_premises' depends on axioms: [propext, Classical.choice, Quot.sound]
'nonvac_theoremB_part_b_premises' depends on axioms: [propext, Classical.choice, Quot.sound]
'nonvac_theoremB_part_a_premises' depends on axioms: [propext, Classical.choice, Quot.sound]
```

File contents (verbatim):

```lean
import BouRabeeGwynne.TheoremAStatement
import BouRabeeGwynne.TheoremBStatement
import BouRabeeGwynne.Harmonic
import SpherePackings.Support.Guards.LatticeTilings
import SpherePackings.Support.Guards.LipschitzBall

open BouRabeeGwynne Metric
open scoped Topology

/-- Shared premises of `TheoremAStatement` and `TheoremBStatement`, in every dimension `d ≥ 1`:
lattice tilings with the unit ball as domain, the nearest-vertex data, the approximation
condition, and `PaperRegularity` through alternative (II). -/
theorem nonvac_shared_premises (d : ℕ) (hd : 1 ≤ d) :
    ∃ (G : TilingSequence d) (N : NearestVertexData G) (U : Set (Euc d)),
      IsLipschitzDomain U ∧ Bornology.IsBounded U ∧ HasAmbientCollar U G.domain ∧
      N.ApproximationCondition ∧ PaperRegularity G := by
  obtain ⟨G, hcollar, ⟨N⟩, happrox, hreg⟩ := SpherePackings.exists_lattice_tilingSequence hd
  exact ⟨G, N, ball (0 : Euc d) 1, SpherePackings.isLipschitzDomain_ball hd, isBounded_ball,
    hcollar, happrox N, Or.inr (Or.inl hreg)⟩

/-- Premises of `TheoremBPartBStatement` for the boundary data `hC = 0`, including
`Nonempty (NearestClosureBoundaryChoices G U)`, so the universal quantifier over the sampling
choices `S` in branch (b) is not vacuous. -/
theorem nonvac_theoremB_part_b_premises (d : ℕ) (hd : 1 ≤ d) :
    ∃ (G : TilingSequence d) (N : NearestVertexData G) (U : Set (Euc d)) (hC : Euc d → ℝ),
      IsLipschitzDomain U ∧ Bornology.IsBounded U ∧ HasAmbientCollar U G.domain ∧
      N.ApproximationCondition ∧ PaperRegularity G ∧ IsHarmonicOn hC U ∧
      ContinuousOnClosure hC U ∧ Nonempty (NearestClosureBoundaryChoices G U) := by
  obtain ⟨G, hcollar, ⟨N⟩, happrox, hreg⟩ := SpherePackings.exists_lattice_tilingSequence hd
  refine ⟨G, N, ball (0 : Euc d) 1, fun _ => 0, SpherePackings.isLipschitzDomain_ball hd,
    isBounded_ball, hcollar, happrox N, Or.inr (Or.inl hreg), ⟨contDiffOn_const, fun x _ => by simp⟩,
    continuousOn_const,
    ⟨NearestClosureBoundaryChoices.ofNonempty G (ball (0 : Euc d) 1) ⟨0, mem_ball_self one_pos⟩⟩⟩

/-- Premises of `TheoremBPartAStatement`: `HarmonicNearClosure` holds for the zero function
with the open neighbourhood `univ` of `closure U`. -/
theorem nonvac_theoremB_part_a_premises (d : ℕ) (hd : 1 ≤ d) :
    ∃ (G : TilingSequence d) (N : NearestVertexData G) (U : Set (Euc d)) (hC : Euc d → ℝ),
      IsDomain U ∧ Bornology.IsBounded U ∧ HasAmbientCollar U G.domain ∧
      N.ApproximationCondition ∧ PaperRegularity G ∧ HarmonicNearClosure hC U := by
  obtain ⟨G, hcollar, ⟨N⟩, happrox, hreg⟩ := SpherePackings.exists_lattice_tilingSequence hd
  exact ⟨G, N, ball (0 : Euc d) 1, fun _ => 0,
    (SpherePackings.isLipschitzDomain_ball hd).isDomain, isBounded_ball, hcollar, happrox N,
    Or.inr (Or.inl hreg), Set.univ, isOpen_univ, Set.subset_univ _,
    ⟨contDiffOn_const, fun x _ => by simp⟩⟩

#print axioms nonvac_shared_premises
#print axioms nonvac_theoremB_part_b_premises
#print axioms nonvac_theoremB_part_a_premises
```

What the examples show:
- `nonvac_shared_premises`: for every d ≥ 1 the shared premises of Theorem A (TheoremAStatement.lean:38–39) and Theorem B (lines 113–114) are jointly satisfiable. The witness is the lattice tiling sequence from `SpherePackings.exists_lattice_tilingSequence`, the unit ball as U (Lipschitz by `isLipschitzDomain_ball`), and `PaperRegularity` through alternative (II).
- `nonvac_theoremB_part_b_premises`: the B(b) bundle with hC = 0 is satisfiable, with `IsHarmonicOn` and `ContinuousOnClosure`. It also shows `NearestClosureBoundaryChoices G U` is inhabited, so the ∀S clause of `TheoremBPartBStatement` quantifies over a nonempty class.
- `nonvac_theoremB_part_a_premises`: the B(a) bundle with `HarmonicNearClosure` for hC = 0 (open neighbourhood `univ`) is satisfiable.

Limits: these show the premises can hold together, not that the conclusions are true. The witnesses use alternative (II) only, and hC is constant, so alternative (III) and non-constant harmonic data are not exercised. `PaperRegularity` holds for every G when d = 2 through `RegularityI`, which is not exhibited here.

No `Upstream/` modules are in this batch.
