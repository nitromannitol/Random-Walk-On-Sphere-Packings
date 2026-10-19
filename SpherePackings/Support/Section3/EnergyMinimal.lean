-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (files `BouRabeeGwynne/FluxResidual.lean` and `BouRabeeGwynne/FacetFlux.lean` at commit cf73d6e):
-- the flux-residual bounds, with the Hessian bound on the edge segment and the cell in place of the
-- closed ball of radius twice the mesh.
import BouRabeeGwynne.Section3PlanarTarget
import Mathlib.Analysis.Normed.Affine.Convex

/-!
# Proposition 2.6 under the edge-segment hypothesis (intermediate result)

**Intermediate result**, under the earlier, stronger hypotheses (the cells of `V[U]` in the interior
of the ambient set, and the Hessian bound also on the edge segments of `E[Ū]`); it is not
registered. The registered Propositions 2.6 and 3.2 are the corrected paper's,
`harmonic_energy_bound_complete` and `harmonic_column_bound_complete` (`EnergyComplete.lean`:
complete cells and the finite Taylor inequality at one active endpoint of each edge).

Proposition 2.6 (`rw-spheres.tex:822-896`, label `prop:energy-bound`) is false as printed: its proof
applies Taylor's theorem on the segment `[v, w]` of an edge, which can leave `Û`, where `h_C` is not
controlled (check G2 in `GAP-CHECKS.md`: a planar Voronoi tiling with a thin cell outside `Û`
crossed by an edge segment, and `h_C` with a cut through that cell).  The correction here asks
`h_C` to be `C²` near the edge segments of `E[Ū]` with the Hessian bound `M` there as well; `M` is
otherwise taken on `Û`, and `ε` is the largest diameter of a cell of `V̄[U]`, as printed.  The
second correction, that the cells of `V[U]` lie in the interior of the ambient set (not the weakest
such hypothesis), is the one of Lemma 2.2 (README, with its counterexample).

The proof is the printed one: Taylor's theorem along `[v, w]`, and the comparison of gradients
inside the convex cell `P_w`, from `w` to a point of the facet.
-/

namespace SpherePackings

open BouRabeeGwynne BouRabeeGwynne.OrthogonalTiling

open scoped MeasureTheory BigOperators Classical

/-- The flux residual of an edge from the Hessian on the edge segment `[v, w]` and on the segment
from `w` to the facet point `y`. -/
theorem fluxResidual_bound_segment {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : E → ℝ) {v w y : E} {ε M : ℝ} (hM : 0 ≤ M)
    (hw : dist v w ≤ 2 * ε) (hy : dist w y ≤ ε)
    (hseg : ∀ x ∈ segment ℝ v w, DifferentiableAt ℝ h x ∧ DifferentiableAt ℝ (fderiv ℝ h) x ∧
      ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M)
    (hcell : ∀ x ∈ segment ℝ w y, DifferentiableAt ℝ (fderiv ℝ h) x ∧
      ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M) :
    |h w - h v - (fderiv ℝ h y) (w - v)| ≤ 3 * M * ε * ‖w - v‖ := by
  have hwseg : w ∈ segment ℝ v w := right_mem_segment ℝ v w
  have hvseg : v ∈ segment ℝ v w := left_mem_segment ℝ v w
  have hwy : ‖fderiv ℝ h w - fderiv ℝ h y‖ ≤ M * ε := by
    have h1 := Convex.norm_image_sub_le_of_norm_fderiv_le (fun x hx => (hcell x hx).1)
      (fun x hx => (hcell x hx).2) (convex_segment w y) (right_mem_segment ℝ w y)
      (left_mem_segment ℝ w y)
    calc ‖fderiv ℝ h w - fderiv ℝ h y‖ ≤ M * ‖w - y‖ := h1
      _ ≤ M * ε := mul_le_mul_of_nonneg_left (by rw [← dist_eq_norm]; exact hy) hM
  have hbound : ∀ x ∈ segment ℝ v w, ‖fderiv ℝ h x - fderiv ℝ h y‖ ≤ 3 * M * ε := by
    intro x hx
    have hxw : ‖fderiv ℝ h x - fderiv ℝ h w‖ ≤ M * ‖x - w‖ :=
      Convex.norm_image_sub_le_of_norm_fderiv_le (fun z hz => (hseg z hz).2.1)
        (fun z hz => (hseg z hz).2.2) (convex_segment v w) hwseg hx
    have hdist : ‖x - w‖ ≤ 2 * ε := by
      have h1 := dist_add_dist_of_mem_segment hx
      rw [← dist_eq_norm]
      linarith [dist_nonneg (x := v) (y := x)]
    calc ‖fderiv ℝ h x - fderiv ℝ h y‖
        ≤ ‖fderiv ℝ h x - fderiv ℝ h w‖ + ‖fderiv ℝ h w - fderiv ℝ h y‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ M * (2 * ε) + M * ε :=
          add_le_add (hxw.trans (mul_le_mul_of_nonneg_left hdist hM)) hwy
      _ = 3 * M * ε := by ring
  have hg : ∀ x ∈ segment ℝ v w, HasFDerivWithinAt (fun z => h z - (fderiv ℝ h y) z)
      (fderiv ℝ h x - fderiv ℝ h y) (segment ℝ v w) x := fun x hx =>
    ((hseg x hx).1.hasFDerivAt.sub (fderiv ℝ h y).hasFDerivAt).hasFDerivWithinAt
  have hres := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hg hbound (convex_segment v w)
    hvseg hwseg
  have hid : (h w - (fderiv ℝ h y) w) - (h v - (fderiv ℝ h y) v) =
      h w - h v - (fderiv ℝ h y) (w - v) := by
    rw [map_sub]
    ring
  rw [hid, Real.norm_eq_abs] at hres
  exact hres

variable {d : ℕ}

/-- Two points of a cell are at most its diameter apart. -/
private lemma dist_le_of_mem_cell (T : OrthogonalTiling d) {v : T.V} {ε : ℝ}
    (hv : Metric.diam (T.cell v).carrier ≤ ε) {x y : Euc d} (hx : x ∈ (T.cell v).carrier)
    (hy : y ∈ (T.cell v).carrier) : dist x y ≤ ε :=
  (Metric.dist_le_diam_of_mem (T.cell v).compact.isBounded hx hy).trans hv

/-- The single-contact residual, with the Hessian bound on the edge segment and on the cell of
the endpoint `w` only. -/
theorem surfaceFlux_residual_bound_segment (T : OrthogonalTiling d) (h : Euc d → ℝ) {v w : T.V}
    (hvw : T.adj v w) {ε : ℝ}
    (hdv : Metric.diam (T.cell v).carrier ≤ ε) (hdw : Metric.diam (T.cell w).carrier ≤ ε)
    {W : Set (Euc d)} (hW : IsOpen W) (hh : ContDiffOn ℝ 2 h W) (hcell : (T.cell w).carrier ⊆ W)
    {W' : Set (Euc d)} (hW' : IsOpen W') (hh' : ContDiffOn ℝ 2 h W')
    (hseg : segment ℝ (T.pos v) (T.pos w) ⊆ W')
    {M : ℝ} (hM : 0 ≤ M)
    (hHseg : ∀ x ∈ segment ℝ (T.pos v) (T.pos w), ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M)
    (hHcell : ∀ x ∈ (T.cell w).carrier, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M) :
    |T.conductanceReal v w * (h (T.pos w) - h (T.pos v)) - T.surfaceFlux h v w| ≤
      3 * M * ε * (T.facetVolume v w).toReal := by
  have hposv : T.pos v ∈ (T.cell v).carrier := interior_subset (T.pos_mem_interior v)
  have hposw : T.pos w ∈ (T.cell w).carrier := interior_subset (T.pos_mem_interior w)
  have hvw2 : dist (T.pos v) (T.pos w) ≤ 2 * ε := by
    obtain ⟨x, hxv, hxw⟩ := hvw.2.1
    calc dist (T.pos v) (T.pos w) ≤ dist (T.pos v) x + dist x (T.pos w) := dist_triangle _ _ _
      _ ≤ ε + ε := add_le_add (dist_le_of_mem_cell T hdv hposv hxv)
          (dist_le_of_mem_cell T hdw hxw hposw)
      _ = 2 * ε := (two_mul _).symm
  have hCF : ContDiffOn ℝ 1 (fderiv ℝ h) W := hh.fderiv_of_isOpen hW (by norm_num)
  have hCF' : ContDiffOn ℝ 1 (fderiv ℝ h) W' := hh'.fderiv_of_isOpen hW' (by norm_num)
  have hlength : 0 < ‖T.pos w - T.pos v‖ := T.edge_norm_pos hvw
  have hpoint : ∀ y ∈ T.facet v w,
      |(h (T.pos w) - h (T.pos v)) / ‖T.pos w - T.pos v‖ -
        (fderiv ℝ h y) (T.unitEdgeDirection v w)| ≤ 3 * M * ε := by
    intro y hy
    have hsegwy : segment ℝ (T.pos w) y ⊆ (T.cell w).carrier :=
      (T.cell w).convex.segment_subset hposw hy.2
    have hraw := fluxResidual_bound_segment h hM hvw2
      (dist_le_of_mem_cell T hdw hposw hy.2)
      (fun x hx => ⟨(hh'.differentiableOn (by norm_num)).differentiableAt
          (hW'.mem_nhds (hseg hx)),
        (hCF'.differentiableOn (by norm_num)).differentiableAt (hW'.mem_nhds (hseg hx)),
        hHseg x hx⟩)
      (fun x hx => ⟨(hCF.differentiableOn (by norm_num)).differentiableAt
          (hW.mem_nhds (hcell (hsegwy hx))), hHcell x (hsegwy hx)⟩)
    have hid : (h (T.pos w) - h (T.pos v)) / ‖T.pos w - T.pos v‖ -
        (fderiv ℝ h y) (T.unitEdgeDirection v w) =
        (h (T.pos w) - h (T.pos v) - (fderiv ℝ h y) (T.pos w - T.pos v)) /
          ‖T.pos w - T.pos v‖ := by
      simp only [unitEdgeDirection, map_smul, smul_eq_mul, div_eq_mul_inv]
      ring
    rw [hid, abs_div, abs_of_pos hlength]
    exact (div_le_iff₀ hlength).mpr hraw
  have hres := abs_const_mul_sub_setIntegral_le
    (μ := μHE[d - 1]) (s := T.facet v w)
    (c := (h (T.pos w) - h (T.pos v)) / ‖T.pos w - T.pos v‖)
    (C := 3 * M * ε)
    (T.toTilingData.facetVolume_pos_lt_top hvw).2
    (T.surfaceFlux_integrable h hvw hW hh (fun y hy => hcell hy.2)) hpoint
  change |(T.facetVolume v w).toReal *
      ((h (T.pos w) - h (T.pos v)) / ‖T.pos w - T.pos v‖) - T.surfaceFlux h v w| ≤
    3 * M * ε * (T.facetVolume v w).toReal at hres
  have hconstant : (T.facetVolume v w).toReal *
      ((h (T.pos w) - h (T.pos v)) / ‖T.pos w - T.pos v‖) =
      T.conductanceReal v w * (h (T.pos w) - h (T.pos v)) := by
    rw [T.conductanceReal_of_adj hvw]
    simp only [div_eq_mul_inv]
    ring
  rw [hconstant] at hres
  exact hres

/-- The energy estimate of Proposition 2.6 in the once-oriented normalization, with the Hessian
bound on the cells of `R` and on the segments of the edges incident to `A`. -/
theorem energy_error_le_hessian_segment (hd : 1 ≤ d) (T : OrthogonalTiling d) (R : Set T.V)
    [Fintype R] (A : Set R) (hD : R → ℝ) (h : Euc d → ℝ) {M ε : ℝ} (hM : 0 ≤ M)
    (hsol : (T.finiteNetwork R).SolvesDirichlet A (fun v : R => h (T.pos v)) hD)
    (hcellD : ∀ v ∈ A, (T.cell v.val).carrier ⊆ interior T.domain)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v.val w → w ∈ R)
    {W : Set (Euc d)} (hW : IsOpen W) (hh : IsHarmonicOn h W)
    (hcells : ∀ v : R, (T.cell v.val).carrier ⊆ W)
    {W' : Set (Euc d)} (hW' : IsOpen W') (hh' : ContDiffOn ℝ 2 h W')
    (hsegs : ∀ v w : R, (w ∈ A ∨ v ∈ A) → T.adj v.val w.val →
      segment ℝ (T.pos v) (T.pos w) ⊆ W')
    (hdiam : ∀ v : R, Metric.diam (T.cell v.val).carrier ≤ ε)
    (hHcell : ∀ v : R, ∀ x ∈ (T.cell v.val).carrier, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M)
    (hHseg : ∀ v w : R, (w ∈ A ∨ v ∈ A) → T.adj v.val w.val →
      ∀ x ∈ segment ℝ (T.pos v) (T.pos w), ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M) :
    (T.finiteNetwork R).energy (hD - fun v : R => h (T.pos v)) ≤
      9 * M ^ 2 * ε ^ 2 * T.incidentMass R A := by
  have hdiv : ∀ v ∈ A, discreteDiv (fun w u : R => T.supportedSurfaceField h w u) v = 0 := by
    intro v hv
    have hfinite := T.neighbors_finite v.val ((hcellD v hv).trans interior_subset)
    rw [T.finite_div_supportedSurfaceField R h v hfinite (fun w hw => hneighbors v hv w hw)]
    exact T.sum_surfaceFlux_eq_zero_of_harmonic hd v.val (hcellD v hv) hfinite hW (hcells v) hh
  have hres : ∀ v w : R, w ∈ A ∨ v ∈ A → T.adj v.val w.val →
      |T.surfaceFlux h v w - T.conductanceReal v w * (h (T.pos w) - h (T.pos v))| ≤
        (3 * M * |ε|) * (T.facetVolume v w).toReal := by
    intro v w hinc hvw
    rw [abs_sub_comm]
    exact surfaceFlux_residual_bound_segment T h hvw ((hdiam v).trans (le_abs_self ε))
      ((hdiam w).trans (le_abs_self ε)) hW hh.contDiffOn (hcells w) hW' hh'
      (hsegs v w hinc hvw) hM (hHseg v w hinc hvw) (hHcell w)
  have hbound := T.energy_error_le_surfaceFlux_mass R A hD h (C := 3 * M * |ε|)
    (by positivity) hsol hdiv hres
  have hmass : ((1 / 2 : ℝ) * ∑ v : R, ∑ w : R,
      if (w ∈ A ∨ v ∈ A) ∧ T.adj v.val w.val then
        (T.facetVolume v w).toReal * ‖T.pos w - T.pos v‖ else 0) =
      T.incidentMass R A := by
    rw [T.incidentMass_eq_half_ordered]
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro w _
    congr 1
    exact propext (by tauto)
  rw [hmass] at hbound
  calc _ ≤ _ := hbound
    _ = 9 * M ^ 2 * ε ^ 2 * T.incidentMass R A := by rw [mul_pow, mul_pow, sq_abs]; ring

/-- Proposition 2.6 (`prop:energy-bound`) under the edge-segment hypothesis (intermediate result, not
registered): `h_C` is harmonic near the cells of
`V̄[U]` and `C²` near the segments of the edges of `E[Ū]`, with Hessian at most `M` on both; `ε`
bounds the diameters of the cells of `V̄[U]`; the cells of `V[U]` lie in the interior of the ambient
set (not the weakest such hypothesis). -/
theorem harmonic_energy_bound_segment (hd : 1 ≤ d) (T : OrthogonalTiling d) (U : Set (Euc d))
    [Fintype (T.closedVertices U)]
    (hcellD : ∀ v ∈ T.interiorVertices U, (T.cell v).carrier ⊆ interior T.domain)
    {W : Set (Euc d)} (hW : IsOpen W) {hC : Euc d → ℝ} (hh : IsHarmonicOn hC W)
    (hcells : ∀ v ∈ T.closedVertices U, (T.cell v).carrier ⊆ W)
    {W' : Set (Euc d)} (hW' : IsOpen W') (hC2 : ContDiffOn ℝ 2 hC W')
    (hsegs : ∀ v ∈ T.closedVertices U, ∀ w ∈ T.closedVertices U, T.adj v w →
      v ∈ T.interiorVertices U ∨ w ∈ T.interiorVertices U →
      segment ℝ (T.pos v) (T.pos w) ⊆ W')
    {M ε : ℝ} (hM : 0 ≤ M)
    (hdiam : ∀ v ∈ T.closedVertices U, Metric.diam (T.cell v).carrier ≤ ε)
    (hHcell : ∀ v ∈ T.closedVertices U, ∀ x ∈ (T.cell v).carrier,
      ‖fderiv ℝ (fderiv ℝ hC) x‖ ≤ M)
    (hHseg : ∀ v ∈ T.closedVertices U, ∀ w ∈ T.closedVertices U, T.adj v w →
      v ∈ T.interiorVertices U ∨ w ∈ T.interiorVertices U →
      ∀ x ∈ segment ℝ (T.pos v) (T.pos w), ‖fderiv ℝ (fderiv ℝ hC) x‖ ≤ M)
    (hD : T.V → ℝ) (hsol : T.SolvesDirichlet U (fun v => hC (T.pos v)) hD) :
    T.incidentEnergy (T.closedVertices U) (T.finiteInterior U) (fun v => hD v - hC (T.pos v)) ≤
      9 * M ^ 2 * ε ^ 2 * T.incidentMass (T.closedVertices U) (T.finiteInterior U) := by
  have hsolR := T.solvesDirichlet_restrict hsol
  have hzero : ∀ w : T.closedVertices U, w ∉ T.finiteInterior U →
      (hD - fun w => hC (T.pos w)) w = 0 :=
    fun w hw => sub_eq_zero.mpr (hsolR.2 w hw)
  rw [show (fun v => hD v - hC (T.pos v)) = (hD - fun w => hC (T.pos w)) from rfl,
    T.incidentEnergy_eq_networkEnergy (T.closedVertices U) (T.finiteInterior U)
      (hD - fun w => hC (T.pos w)) hzero]
  exact energy_error_le_hessian_segment hd T (T.closedVertices U) (T.finiteInterior U)
    (fun w => hD w) hC hM hsolR (fun v hv => hcellD (v : T.V) hv)
    (fun v hv w hvw => T.neighbor_mem_closedVertices (show (v : T.V) ∈ T.interiorVertices U from hv) hvw)
    hW hh (fun v => hcells v v.property) hW' hC2
    (fun v w hinc hvw => hsegs v v.property w w.property hvw hinc.symm)
    (fun v => hdiam v v.property) (fun v => hHcell v v.property)
    (fun v w hinc hvw => hHseg v v.property w w.property hvw hinc.symm)

/-- Proposition 3.2 (`prop:energy-poincare-bound`) under the hypotheses of the edge-segment form of
Proposition 2.6, for columns in any direction `e ≠ 0`. -/
theorem harmonic_column_bound_segment (hd : 1 ≤ d) (T : OrthogonalTiling d) (U : Set (Euc d))
    [Fintype (T.closedVertices U)]
    (hcellD : ∀ v ∈ T.interiorVertices U, (T.cell v).carrier ⊆ interior T.domain)
    {W : Set (Euc d)} (hW : IsOpen W) {hC : Euc d → ℝ} (hh : IsHarmonicOn hC W)
    (hcells : ∀ v ∈ T.closedVertices U, (T.cell v).carrier ⊆ W)
    {W' : Set (Euc d)} (hW' : IsOpen W') (hC2 : ContDiffOn ℝ 2 hC W')
    (hsegs : ∀ v ∈ T.closedVertices U, ∀ w ∈ T.closedVertices U, T.adj v w →
      v ∈ T.interiorVertices U ∨ w ∈ T.interiorVertices U →
      segment ℝ (T.pos v) (T.pos w) ⊆ W')
    {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hdiam : ∀ v ∈ T.closedVertices U, Metric.diam (T.cell v).carrier ≤ ε)
    (hHcell : ∀ v ∈ T.closedVertices U, ∀ x ∈ (T.cell v).carrier,
      ‖fderiv ℝ (fderiv ℝ hC) x‖ ≤ M)
    (hHseg : ∀ v ∈ T.closedVertices U, ∀ w ∈ T.closedVertices U, T.adj v w →
      v ∈ T.interiorVertices U ∨ w ∈ T.interiorVertices U →
      ∀ x ∈ segment ℝ (T.pos v) (T.pos w), ‖fderiv ℝ (fderiv ℝ hC) x‖ ≤ M)
    (hD : T.V → ℝ) (hsol : T.SolvesDirichlet U (fun v => hC (T.pos v)) hD)
    (e : Euc d) (he : e ≠ 0) {k : ℝ} (hk : 0 < k) :
    μHE[d - 1] (T.columnBadSet (T.closedVertices U) (T.finiteInterior U) e he
        (fun v => hD v - hC (T.pos v))
        (3 * k * M * ε * T.incidentMass (T.closedVertices U) (T.finiteInterior U))) ≤
      ENNReal.ofReal (1 / k) := by
  rw [← abs_of_nonneg hε]
  have hC0 : 0 ≤ 3 * M * |ε| := by positivity
  have henergy : T.incidentEnergy (T.closedVertices U) (T.finiteInterior U)
      (fun v => hD v - hC (T.pos v)) ≤ (3 * M * |ε|) ^ 2 *
        T.incidentMass (T.closedVertices U) (T.finiteInterior U) :=
    (harmonic_energy_bound_segment hd T U hcellD hW hh hcells hW' hC2 hsegs hM hdiam hHcell
      hHseg hD hsol).trans_eq (by rw [mul_pow, mul_pow, sq_abs]; ring)
  have hsolR := T.solvesDirichlet_restrict hsol
  have key := T.column_poincare_of_energy_bound hd e he (T.closedVertices U) (T.finiteInterior U)
    (fun v hv w hvw => T.neighbor_mem_closedVertices
      (show (v : T.V) ∈ T.interiorVertices U from hv) hvw)
    (fun v hv => hcellD (v : T.V) hv)
    (fun v => hD v - hC (T.pos v)) (fun w hw => sub_eq_zero.mpr (hsolR.2 w hw)) hC0 hk henergy
  have harg : 3 * k * M * |ε| * T.incidentMass (T.closedVertices U) (T.finiteInterior U) =
      k * (3 * M * |ε|) * T.incidentMass (T.closedVertices U) (T.finiteInterior U) := by
    ring
  rw [harg]
  exact key

end SpherePackings
