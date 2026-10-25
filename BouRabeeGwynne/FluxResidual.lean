module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/FluxResidual.lean` at commit cf73d6e); unchanged apart from this header.
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

open scoped Topology

namespace BouRabeeGwynne

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The pointwise flux residual estimate on a convex ball. Every derivative is
an actual Fréchet derivative, and the Hessian bound holds throughout that ball. -/
theorem fluxResidual_bound_on_closedBall (h : E → ℝ) {v w y : E} {ε M : ℝ}
    (hε : 0 ≤ ε) (hM : 0 ≤ M)
    (hw : dist v w ≤ 2 * ε) (hy : dist v y ≤ ε)
    (hh : ∀ x ∈ Metric.closedBall v (2 * ε), DifferentiableAt ℝ h x)
    (hF : ∀ x ∈ Metric.closedBall v (2 * ε),
      DifferentiableAt ℝ (fderiv ℝ h) x)
    (hH : ∀ x ∈ Metric.closedBall v (2 * ε),
      ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M) :
    |h w - h v - (fderiv ℝ h y) (w - v)| ≤ 3 * M * ε * ‖w - v‖ := by
  have hvB : v ∈ Metric.closedBall v (2 * ε) :=
    Metric.mem_closedBall_self (by positivity)
  have hwB : w ∈ Metric.closedBall v (2 * ε) :=
    Metric.mem_closedBall.mpr (by simpa only [dist_comm] using hw)
  have hyB : y ∈ Metric.closedBall v (2 * ε) := by
    apply Metric.mem_closedBall.mpr
    have hle : ε ≤ 2 * ε := by linarith
    simpa only [dist_comm] using hy.trans hle
  have hbound : ∀ x ∈ Metric.closedBall v (2 * ε),
      ‖fderiv ℝ h x - fderiv ℝ h y‖ ≤ 3 * M * ε := by
    intro x hx
    have hxy : ‖x - y‖ ≤ 3 * ε := by
      have hxv : dist x v ≤ 2 * ε := Metric.mem_closedBall.mp hx
      calc
        ‖x - y‖ = dist x y := (dist_eq_norm x y).symm
        _ ≤ dist x v + dist v y := dist_triangle x v y
        _ ≤ 2 * ε + ε := add_le_add hxv hy
        _ = 3 * ε := by ring
    calc
      ‖fderiv ℝ h x - fderiv ℝ h y‖ ≤ M * ‖x - y‖ :=
        (convex_closedBall v (2 * ε)).norm_image_sub_le_of_norm_fderiv_le hF hH hyB hx
      _ ≤ M * (3 * ε) := mul_le_mul_of_nonneg_left hxy hM
      _ = 3 * M * ε := by ring
  have hg : ∀ x ∈ Metric.closedBall v (2 * ε),
      HasFDerivWithinAt (fun z => h z - (fderiv ℝ h y) z)
        (fderiv ℝ h x - fderiv ℝ h y) (Metric.closedBall v (2 * ε)) x := by
    intro x hx
    exact ((hh x hx).hasFDerivAt.sub
      (fderiv ℝ h y).hasFDerivAt).hasFDerivWithinAt
  have hres := (convex_closedBall v (2 * ε)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hg hbound hvB hwB
  have hid : (h w - (fderiv ℝ h y) w) - (h v - (fderiv ℝ h y) v) =
      h w - h v - (fderiv ℝ h y) (w - v) := by
    rw [map_sub]
    ring
  rw [hid, Real.norm_eq_abs] at hres
  exact hres

/-- A C² function on a fixed open neighborhood of a bounded closure has a
uniform bound for its genuine second Fréchet derivative on a positive compact
collar. Both first-derivative differentiability requirements hold there as well. -/
theorem exists_collar_derivative_bounds [ProperSpace E] (h : E → ℝ)
    {U W : Set E} (hU : Bornology.IsBounded U) (hW : IsOpen W)
    (hUW : closure U ⊆ W) (hh : ContDiffOn ℝ 2 h W) :
    ∃ r : ℝ, 0 < r ∧ ∃ M : ℝ, 0 ≤ M ∧
      Metric.cthickening r (closure U) ⊆ W ∧
      (∀ x ∈ Metric.cthickening r (closure U), DifferentiableAt ℝ h x) ∧
      (∀ x ∈ Metric.cthickening r (closure U),
        DifferentiableAt ℝ (fderiv ℝ h) x) ∧
      (∀ x ∈ Metric.cthickening r (closure U),
        ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M) := by
  obtain ⟨r, hr, hrW⟩ := hU.isCompact_closure.exists_cthickening_subset_open hW hUW
  have hF : ContDiffOn ℝ 1 (fderiv ℝ h) W :=
    hh.fderiv_of_isOpen hW (by norm_num)
  have hH : ContinuousOn (fderiv ℝ (fderiv ℝ h)) W :=
    hF.continuousOn_fderiv_of_isOpen hW (by norm_num)
  have hK : IsCompact (Metric.cthickening r (closure U)) :=
    hU.isCompact_closure.cthickening
  obtain ⟨M₀, hM₀⟩ := hK.exists_bound_of_continuousOn
    (f := fderiv ℝ (fderiv ℝ h)) (hH.mono hrW)
  refine ⟨r, hr, max M₀ 0, le_max_right _ _, hrW, ?_, ?_, ?_⟩
  · intro x hx
    exact (hh.differentiableOn (by norm_num)).differentiableAt (hW.mem_nhds (hrW hx))
  · intro x hx
    exact (hF.differentiableOn (by norm_num)).differentiableAt (hW.mem_nhds (hrW hx))
  · intro x hx
    exact (hM₀ x hx).trans (le_max_left _ _)

/-- The B(a) analytic flux estimate has constants depending only on the fixed
C² neighborhood and bounded set. The estimate is uniform over all sufficiently
short pairs near a point of `U`; no convexity of `U` is required. -/
theorem exists_uniform_fluxResidual_bound [ProperSpace E] (h : E → ℝ)
    {U W : Set E} (hU : Bornology.IsBounded U) (hW : IsOpen W)
    (hUW : closure U ⊆ W) (hh : ContDiffOn ℝ 2 h W) :
    ∃ r : ℝ, 0 < r ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ v ∈ U, ∀ ε : ℝ, 0 ≤ ε → 2 * ε ≤ r →
      ∀ w y : E, dist v w ≤ 2 * ε → dist v y ≤ ε →
      |h w - h v - (fderiv ℝ h y) (w - v)| ≤ 3 * M * ε * ‖w - v‖ := by
  obtain ⟨r, hr, M, hM, _, hh', hF, hH⟩ :=
    exists_collar_derivative_bounds h hU hW hUW hh
  refine ⟨r, hr, M, hM, ?_⟩
  intro v hv ε hε hεr w y hw hy
  have hBK : Metric.closedBall v (2 * ε) ⊆ Metric.cthickening r (closure U) :=
    (Metric.closedBall_subset_cthickening (subset_closure hv) (2 * ε)).trans
      (Metric.cthickening_mono hεr (closure U))
  exact fluxResidual_bound_on_closedBall h hε hM hw hy
    (fun x hx => hh' x (hBK hx)) (fun x hx => hF x (hBK hx))
    (fun x hx => hH x (hBK hx))

end BouRabeeGwynne
