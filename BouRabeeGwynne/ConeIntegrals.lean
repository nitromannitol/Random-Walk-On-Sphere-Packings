module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/ConeIntegrals.lean` at commit cf73d6e); unchanged apart from this header.
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

open scoped ENNReal
open MeasureTheory

namespace BouRabeeGwynne

/-- The scalar integral producing the height-over-dimension pyramid factor. -/
theorem integral_scaled_pow_Icc {r : ℝ} (hr : 0 < r) (k : ℕ) :
    (∫ t in Set.Icc (0 : ℝ) r, (t / r) ^ k) = r / (k + 1 : ℝ) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr.le]
  simp_rw [div_pow]
  rw [intervalIntegral.integral_div, integral_pow]
  simp only [zero_pow (Nat.succ_ne_zero k), sub_zero, Nat.cast_add, Nat.cast_one]
  rw [pow_succ]
  have hk : (k + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hr.ne', hk]

/-- The same exact integral in the extended nonnegative form used by the
orthogonal cross-section formula. -/
theorem lintegral_scaled_pow_Icc {r : ℝ} (hr : 0 < r) (k : ℕ) :
    (∫⁻ t in Set.Icc (0 : ℝ) r, ENNReal.ofReal ((t / r) ^ k)) =
      ENNReal.ofReal (r / (k + 1 : ℝ)) := by
  have hc : Continuous (fun t : ℝ => (t / r) ^ k) := by fun_prop
  have hi : IntegrableOn (fun t : ℝ => (t / r) ^ k) (Set.Icc (0 : ℝ) r) :=
    hc.integrableOn_Icc
  have hn : 0 ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) r)] (fun t : ℝ => (t / r) ^ k) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact pow_nonneg (div_nonneg ht.1 hr.le) k
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn, integral_scaled_pow_Icc hr k]

/-- Normalized Hausdorff homothety factors have the same scalar integral. -/
theorem lintegral_nnnorm_scaled_pow_Icc {r : ℝ} (hr : 0 < r) (k : ℕ) :
    (∫⁻ t in Set.Icc (0 : ℝ) r, (‖t / r‖₊ : ℝ≥0∞) ^ k) =
      ENNReal.ofReal (r / (k + 1 : ℝ)) := by
  rw [← lintegral_scaled_pow_Icc hr k]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have ht0 : 0 ≤ t / r := div_nonneg ht.1 hr.le
  have hn : (‖t / r‖₊ : ℝ≥0∞) = ENNReal.ofReal (t / r) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    change ENNReal.ofReal ‖t / r‖ = _
    rw [Real.norm_of_nonneg ht0]
  rw [hn, ← ENNReal.ofReal_pow ht0]

end BouRabeeGwynne
