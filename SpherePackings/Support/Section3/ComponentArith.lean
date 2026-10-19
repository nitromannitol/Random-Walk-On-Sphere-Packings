-- Built on Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne (commit cf73d6e).
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The case analysis for the component term of Theorem 3.6

On a connected set of small cells the error is at most both the path bound `L (D_Q + ε)` and the
quadratic bound `M ρ²`, with `ρ` the distance to the exit vertices.  Together they give
`D L + C M K ε log(1/ε)`.
-/

namespace SpherePackings

/-- **The case analysis** combining the path bound and the quadratic bound on a component. -/
theorem component_case_bound {x L M ε K Dq Dc ρ R : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hK : 1 ≤ K) (hR : 0 ≤ R) (hDq : 0 ≤ Dq)
    (hDqc : Dq ≤ Dc) (hρ0 : 0 ≤ ρ) (hρq : ρ ≤ Dq + ε) (hρR : ρ ≤ 2 * R)
    (hpath : x ≤ L * (Dq + ε)) (hquad : x ≤ M * ρ ^ 2) :
    x ≤ Dc * L + 4 * (R + 1) / Real.log 2 * M * K * ε * Real.log (1 / ε) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h2ε : (2 : ℝ) ≤ 1 / ε := (le_div_iff₀ hε).2 (by linarith)
  have hlog : Real.log 2 ≤ Real.log (1 / ε) := Real.log_le_log two_pos h2ε
  have hlog0 : 0 ≤ Real.log (1 / ε) := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hDc0 : 0 ≤ Dc := le_trans hDq hDqc
  set C := 4 * (R + 1) / Real.log 2 with hC_def
  have hC0 : 0 ≤ C := by
    rw [hC_def]
    exact div_nonneg (mul_nonneg (by norm_num) (by linarith)) hlog2.le
  have hCl : C * Real.log 2 = 4 * (R + 1) := by
    rw [hC_def, div_mul_cancel₀ _ hlog2.ne']
  -- the key lower bound `4 (R + 1) ≤ C K log (1/ε)`
  have hkey : 4 * (R + 1) ≤ C * K * Real.log (1 / ε) := by
    have h1 : Real.log 2 ≤ K * Real.log (1 / ε) := by
      nlinarith [mul_nonneg (sub_nonneg.2 hK) hlog0]
    calc 4 * (R + 1) = C * Real.log 2 := hCl.symm
      _ ≤ C * (K * Real.log (1 / ε)) := mul_le_mul_of_nonneg_left h1 hC0
      _ = C * K * Real.log (1 / ε) := by ring
  have hT : 0 ≤ C * M * K * ε * Real.log (1 / ε) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC0 hM) hK0) hε.le) hlog0
  have hpath' : x ≤ Dc * L + L * ε := by
    linarith [hpath, mul_le_mul_of_nonneg_left hDqc hL]
  rcases le_or_gt L (C * M * K * Real.log (1 / ε)) with hcase | hcase
  · -- Case 1: the path bound
    have h1 : L * ε ≤ C * M * K * Real.log (1 / ε) * ε :=
      mul_le_mul_of_nonneg_right hcase hε.le
    have h2 : C * M * K * Real.log (1 / ε) * ε = C * M * K * ε * Real.log (1 / ε) := by ring
    linarith
  · rcases lt_or_ge Dc ε with hεD | hεD
    · -- Case 2b: `Dc < ε`, so `ρ ≤ 2 ε` and the quadratic bound gives `O(M ε²)`
      have hρ4 : ρ ≤ 2 * ε := by linarith
      have hsq : ρ ^ 2 ≤ (2 * ε) * (2 * ε) := by
        rw [sq]
        exact mul_le_mul hρ4 hρ4 hρ0 (by linarith)
      have hM2 : M * ρ ^ 2 ≤ M * ((2 * ε) * (2 * ε)) := mul_le_mul_of_nonneg_left hsq hM
      have hCK : 4 ≤ C * K * Real.log (1 / ε) := by linarith
      have hMε : 0 ≤ M * ε := mul_nonneg hM hε.le
      have hT' : M * ε * 4 ≤ M * ε * (C * K * Real.log (1 / ε)) :=
        mul_le_mul_of_nonneg_left hCK hMε
      have hε1 : ε ≤ 1 := by linarith
      have hMε2 : M * ((2 * ε) * (2 * ε)) ≤ M * ε * 4 := by
        nlinarith [mul_nonneg hMε (sub_nonneg.2 hε1)]
      have h3 : C * M * K * ε * Real.log (1 / ε) = M * ε * (C * K * Real.log (1 / ε)) := by
        ring
      linarith [mul_nonneg hDc0 hL]
    · -- Case 2a: `ε ≤ Dc`, so `ρ ≤ 2 Dc` and the quadratic bound gives `M ρ² ≤ 4 R M Dc ≤ L Dc`
      have hρ2 : ρ ≤ 2 * Dc := by linarith
      have hsq : ρ ^ 2 ≤ (2 * Dc) * (2 * R) := by
        rw [sq]
        exact mul_le_mul hρ2 hρR hρ0 (by linarith)
      have hM2 : M * ρ ^ 2 ≤ M * ((2 * Dc) * (2 * R)) := mul_le_mul_of_nonneg_left hsq hM
      have hLbig : 4 * (R + 1) * M ≤ L := by
        have h4 : M * (4 * (R + 1)) ≤ M * (C * K * Real.log (1 / ε)) :=
          mul_le_mul_of_nonneg_left hkey hM
        linarith
      have hfin : M * ((2 * Dc) * (2 * R)) ≤ L * Dc := by
        nlinarith [mul_le_mul_of_nonneg_right hLbig hDc0, mul_nonneg hM hDc0]
      linarith

end SpherePackings
