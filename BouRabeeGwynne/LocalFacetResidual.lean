module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/LocalFacetResidual.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.FacetAffineResidual

@[expose] public section

/-! The contact residual at the diameter scale of its two incident cells. -/

open scoped ENNReal MeasureTheory
open MeasureTheory

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

theorem dist_pos_le_diam_bound {v : T.V} {y : Euc d} {δ : ℝ}
    (hy : y ∈ (T.cell v).carrier) (hv : Metric.diam (T.cell v).carrier ≤ δ) :
    dist (T.pos v) y ≤ δ :=
  (Metric.dist_le_diam_of_mem (T.cell v).compact.isBounded
    (interior_subset (T.pos_mem_interior v)) hy).trans hv

theorem edge_dist_le_two_diam_bound {v w : T.V} (hvw : T.adj v w) {δ : ℝ}
    (hv : Metric.diam (T.cell v).carrier ≤ δ)
    (hw : Metric.diam (T.cell w).carrier ≤ δ) : dist (T.pos v) (T.pos w) ≤ 2 * δ := by
  obtain ⟨y, hy⟩ := hvw.2.1
  calc
    _ ≤ dist (T.pos v) y + dist y (T.pos w) := dist_triangle _ _ _
    _ ≤ δ + δ := add_le_add (T.dist_pos_le_diam_bound hy.1 hv)
      (by simpa only [dist_comm] using T.dist_pos_le_diam_bound hy.2 hw)
    _ = _ := by ring

/-- This version uses only the two endpoint cell diameters, not the global
mesh, so it applies at every shrinking interior-interior edge in case III. -/
theorem surfaceFlux_residual_bound_of_cell_diameters (h : Euc d → ℝ)
    {v w : T.V} (hvw : T.adj v w) {δ M : ℝ} (hδ : 0 ≤ δ) (hM : 0 ≤ M)
    (hv : Metric.diam (T.cell v).carrier ≤ δ)
    (hw : Metric.diam (T.cell w).carrier ≤ δ)
    {W : Set (Euc d)} (hW : IsOpen W) (hh : ContDiffOn ℝ 2 h W)
    (hball : Metric.closedBall (T.pos v) (2 * δ) ⊆ W)
    (hH : ∀ x ∈ Metric.closedBall (T.pos v) (2 * δ),
      ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M) :
    |T.surfaceFlux h v w - T.conductanceReal v w *
      (h (T.pos w) - h (T.pos v))| ≤
        3 * M * δ * (T.facetVolume v w).toReal := by
  have hfacetB : T.facet v w ⊆ Metric.closedBall (T.pos v) (2 * δ) := by
    intro y hy
    apply Metric.mem_closedBall.mpr
    have hdist := T.dist_pos_le_diam_bound hy.1 hv
    rw [dist_comm]
    linarith
  have hCF : ContDiffOn ℝ 1 (fderiv ℝ h) W :=
    hh.fderiv_of_isOpen hW (by norm_num)
  have hlength : 0 < ‖T.pos w - T.pos v‖ := T.edge_norm_pos hvw
  have hpoint : ∀ y ∈ T.facet v w,
      |(h (T.pos w) - h (T.pos v)) / ‖T.pos w - T.pos v‖ -
        (fderiv ℝ h y) (T.unitEdgeDirection v w)| ≤ 3 * M * δ := by
    intro y hy
    have hraw := fluxResidual_bound_on_closedBall h hδ hM
      (T.edge_dist_le_two_diam_bound hvw hv hw) (T.dist_pos_le_diam_bound hy.1 hv)
      (fun x hx => (hh.differentiableOn (by norm_num)).differentiableAt
        (hW.mem_nhds (hball hx)))
      (fun x hx => (hCF.differentiableOn (by norm_num)).differentiableAt
        (hW.mem_nhds (hball hx))) hH
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
    (C := 3 * M * δ) (T.toTilingData.facetVolume_pos_lt_top hvw).2
    (T.surfaceFlux_integrable h hvw hW hh (hfacetB.trans hball)) hpoint
  have hconstant : (T.facetVolume v w).toReal *
      ((h (T.pos w) - h (T.pos v)) / ‖T.pos w - T.pos v‖) =
      T.conductanceReal v w * (h (T.pos w) - h (T.pos v)) := by
    rw [T.conductanceReal_of_adj hvw]
    simp only [div_eq_mul_inv]
    ring
  change |(T.facetVolume v w).toReal *
    ((h (T.pos w) - h (T.pos v)) / ‖T.pos w - T.pos v‖) - T.surfaceFlux h v w| ≤ _ at hres
  rw [hconstant, abs_sub_comm] at hres
  exact hres

end BouRabeeGwynne.OrthogonalTiling
