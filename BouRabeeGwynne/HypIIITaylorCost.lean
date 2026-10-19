-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/HypIIITaylorCost.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.CorrectedSurfaceField

/-! A sufficient quadratic bound for actual new boundary Taylor rewards. -/

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

/-- The constant six comes directly from the checked residual estimate and is
sufficient for the qualitative convergence of the correction series. -/
theorem surfaceTaylorRemainder_abs_le (h : Euc d → ℝ) {v w : T.V} {δ M : ℝ}
    (hδ : 0 ≤ δ) (hM : 0 ≤ M) (hdist : dist (T.pos v) (T.pos w) ≤ 2 * δ)
    {W : Set (Euc d)} (hW : IsOpen W) (hh : ContDiffOn ℝ 2 h W)
    (hball : Metric.closedBall (T.pos v) (2 * δ) ⊆ W)
    (hH : ∀ x ∈ Metric.closedBall (T.pos v) (2 * δ),
      ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M) :
    |T.surfaceTaylorRemainder h v w| ≤ 6 * M * δ ^ 2 := by
  have hCF : ContDiffOn ℝ 1 (fderiv ℝ h) W :=
    hh.fderiv_of_isOpen hW (by norm_num)
  have hres := fluxResidual_bound_on_closedBall h hδ hM hdist
    (show dist (T.pos v) (T.pos v) ≤ δ by simpa using hδ)
    (fun x hx => (hh.differentiableOn (by norm_num)).differentiableAt
      (hW.mem_nhds (hball hx)))
    (fun x hx => (hCF.differentiableOn (by norm_num)).differentiableAt
      (hW.mem_nhds (hball hx))) hH
  have hnorm : ‖T.pos w - T.pos v‖ ≤ 2 * δ := by
    simpa only [dist_eq_norm, norm_sub_rev] using hdist
  calc
    _ ≤ 3 * M * δ * ‖T.pos w - T.pos v‖ := hres
    _ ≤ 3 * M * δ * (2 * δ) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = _ := by ring

end BouRabeeGwynne.OrthogonalTiling
