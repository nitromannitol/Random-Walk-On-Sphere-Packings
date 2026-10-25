module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/FacetAffineResidual.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.FacetFlux

@[expose] public section

/-!
# Contact flux compared with the interior affine approximation

Only the diameter and Hessian bound on the source cell enter this estimate.
The adjacent cell and the edge length may be much larger. This is the analytic
input for the boundary-reward correction in the diameter hypothesis of B(a).
-/

open scoped ENNReal MeasureTheory
open MeasureTheory

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

/-- Gradient variation on the actual convex cell, measured from its marked point. -/
theorem gradient_variation_on_cell (h : Euc d → ℝ) (v : T.V)
    {W : Set (Euc d)} (hW : IsOpen W) (hPW : (T.cell v).carrier ⊆ W)
    (hh : ContDiffOn ℝ 2 h W) {M ε : ℝ} (hM : 0 ≤ M)
    (hdiam : Metric.diam (T.cell v).carrier ≤ ε)
    (hH : ∀ x ∈ (T.cell v).carrier, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M)
    {y : Euc d} (hy : y ∈ (T.cell v).carrier) :
    ‖fderiv ℝ h y - fderiv ℝ h (T.pos v)‖ ≤ M * ε := by
  have hF : ContDiffOn ℝ 1 (fderiv ℝ h) W :=
    hh.fderiv_of_isOpen hW (by norm_num)
  have hv : T.pos v ∈ (T.cell v).carrier := interior_subset (T.pos_mem_interior v)
  have hdist : ‖y - T.pos v‖ ≤ ε := by
    rw [← dist_eq_norm]
    exact (Metric.dist_le_diam_of_mem (T.cell v).compact.isBounded hy hv).trans hdiam
  calc
    _ ≤ M * ‖y - T.pos v‖ :=
      (T.cell v).convex.norm_image_sub_le_of_norm_fderiv_le
        (fun x hx => (hF.differentiableOn (by norm_num)).differentiableAt
          (hW.mem_nhds (hPW hx))) hH hv hy
    _ ≤ M * ε := mul_le_mul_of_nonneg_left hdist hM

/-- The actual contact integral differs from the interior affine increment by
at most `M * ε * area`. No diameter bound on the adjacent cell is assumed. -/
theorem surfaceFlux_affine_residual_bound (h : Euc d → ℝ) {v w : T.V}
    (hvw : T.adj v w) {W : Set (Euc d)} (hW : IsOpen W)
    (hPW : (T.cell v).carrier ⊆ W) (hh : ContDiffOn ℝ 2 h W)
    {M ε : ℝ} (hM : 0 ≤ M) (hdiam : Metric.diam (T.cell v).carrier ≤ ε)
    (hH : ∀ x ∈ (T.cell v).carrier, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M) :
    |T.surfaceFlux h v w - T.conductanceReal v w *
      (fderiv ℝ h (T.pos v)) (T.pos w - T.pos v)| ≤
        M * ε * (T.facetVolume v w).toReal := by
  have hpoint : ∀ y ∈ T.facet v w,
      |(fderiv ℝ h (T.pos v)) (T.unitEdgeDirection v w) -
        (fderiv ℝ h y) (T.unitEdgeDirection v w)| ≤ M * ε := by
    intro y hy
    rw [← Real.norm_eq_abs]
    change ‖((fderiv ℝ h (T.pos v)) - (fderiv ℝ h y)) (T.unitEdgeDirection v w)‖ ≤ _
    calc
      _ ≤ ‖fderiv ℝ h (T.pos v) - fderiv ℝ h y‖ * ‖T.unitEdgeDirection v w‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ h y - fderiv ℝ h (T.pos v)‖ := by
        rw [T.norm_unitEdgeDirection hvw, mul_one, norm_sub_rev]
      _ ≤ M * ε := T.gradient_variation_on_cell h v hW hPW hh hM hdiam hH hy.1
  have hbound := abs_const_mul_sub_setIntegral_le
    (μ := μHE[d - 1]) (s := T.facet v w)
    (c := (fderiv ℝ h (T.pos v)) (T.unitEdgeDirection v w)) (C := M * ε)
    (T.toTilingData.facetVolume_pos_lt_top hvw).2
    (T.surfaceFlux_integrable h hvw hW hh (fun _ hy => hPW hy.1)) hpoint
  have hconstant : (T.facetVolume v w).toReal *
      (fderiv ℝ h (T.pos v)) (T.unitEdgeDirection v w) =
        T.conductanceReal v w * (fderiv ℝ h (T.pos v)) (T.pos w - T.pos v) := by
    rw [T.conductanceReal_of_adj hvw]
    simp only [unitEdgeDirection, map_smul, smul_eq_mul, div_eq_mul_inv]
    ring
  change |(T.facetVolume v w).toReal *
      (fderiv ℝ h (T.pos v)) (T.unitEdgeDirection v w) - T.surfaceFlux h v w| ≤ _ at hbound
  rw [hconstant, abs_sub_comm] at hbound
  exact hbound

end BouRabeeGwynne.OrthogonalTiling
