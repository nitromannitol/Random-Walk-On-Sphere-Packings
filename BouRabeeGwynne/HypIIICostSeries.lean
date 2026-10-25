module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/HypIIICostSeries.lean` at commit cf73d6e); unchanged apart from this header.
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Convergence of the corrected hypothesis III iteration cost

The local diameters are bounded by the global mesh and by a fixed geometric
sequence. Mathlib's dominated convergence theorem for series then proves
that the complete cost tends to zero, including the square-root trimming
cutoffs and newly exposed boundary corrections. The main theorems need this
qualitative limit, so no logarithmic rate is required here.
-/

open Filter
open scoped Topology BigOperators

namespace BouRabeeGwynne

noncomputable def hypIIICost (A M ε : ℝ) (δ : ℕ → ℝ) : ℝ :=
  2 * M * ε ^ 2 + ∑' i, (A * M * δ i + Real.sqrt (ε * δ i) + 2 * M * δ i ^ 2)

theorem hypIIICost_tendsto_zero (ε : ℕ → ℝ) (δ : ℕ → ℕ → ℝ)
    {A M K r : ℝ} (hA : 0 ≤ A) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hr : 0 ≤ r) (hr1 : r < 1)
    (hεnonneg : ∀ n, 0 ≤ ε n) (hε : Tendsto ε atTop (𝓝 0))
    (hδnonneg : ∀ n i, 0 ≤ δ n i)
    (hδmesh : ∀ n i, δ n i ≤ ε n)
    (hδgeom : ∀ n i, δ n i ≤ K * r ^ i) :
    Tendsto (fun n => hypIIICost A M (ε n) (δ n)) atTop (𝓝 0) := by
  let f : ℕ → ℕ → ℝ := fun n i =>
    A * M * δ n i + Real.sqrt (ε n * δ n i) + 2 * M * δ n i ^ 2
  let b : ℕ → ℝ := fun i =>
    ((A * M + 2 * M) * K) * r ^ i + Real.sqrt K * (Real.sqrt r) ^ i
  have hroot : Real.sqrt r < 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt hr hr1
  have hsumb : Summable b :=
    ((summable_geometric_of_lt_one hr hr1).mul_left ((A * M + 2 * M) * K)).add
      ((summable_geometric_of_lt_one (Real.sqrt_nonneg r) hroot).mul_left (Real.sqrt K))
  have hrootpow : ∀ i : ℕ, Real.sqrt (r ^ i) = (Real.sqrt r) ^ i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg hr i), ih, pow_succ]
  have hpoint : ∀ i, Tendsto (fun n => f n i) atTop (𝓝 0) := by
    intro i
    have hd : Tendsto (fun n => δ n i) atTop (𝓝 0) :=
      squeeze_zero (fun n => hδnonneg n i) (fun n => hδmesh n i) hε
    have ht := (((tendsto_const_nhds (x := A * M)).mul hd).add (hε.mul hd).sqrt).add
      ((tendsto_const_nhds (x := 2 * M)).mul (hd.pow 2))
    simpa only [mul_zero, Real.sqrt_zero, add_zero, zero_pow (by decide : 2 ≠ 0), f]
      using ht
  have hbound : ∀ᶠ n in atTop, ∀ i, ‖f n i‖ ≤ b i := by
    filter_upwards [hε (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hn
    intro i
    have he : ε n ≤ 1 := le_of_lt hn
    have hd0 := hδnonneg n i
    have hd1 : δ n i ≤ 1 := (hδmesh n i).trans he
    have hsq : δ n i ^ 2 ≤ δ n i := by
      nlinarith [mul_nonneg hd0 (sub_nonneg.mpr hd1)]
    have hmain : A * M * δ n i ≤ A * M * (K * r ^ i) :=
      mul_le_mul_of_nonneg_left (hδgeom n i) (mul_nonneg hA hM)
    have hcorrection : 2 * M * δ n i ^ 2 ≤ 2 * M * (K * r ^ i) :=
      mul_le_mul_of_nonneg_left (hsq.trans (hδgeom n i)) (by positivity)
    have hprod : ε n * δ n i ≤ K * r ^ i := by
      calc
        _ ≤ 1 * δ n i := mul_le_mul_of_nonneg_right he hd0
        _ = δ n i := one_mul _
        _ ≤ _ := hδgeom n i
    have hcutoff := Real.sqrt_le_sqrt hprod
    rw [Real.sqrt_mul hK, hrootpow] at hcutoff
    have hf0 : 0 ≤ f n i := by dsimp [f]; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hf0]
    dsimp only [f, b]
    nlinarith
  have hsum : Tendsto (fun n => ∑' i, f n i) atTop (𝓝 0) := by
    simpa only [tsum_zero] using
      (tendsto_tsum_of_dominated_convergence hsumb hpoint hbound)
  have hfirst : Tendsto (fun n => 2 * M * ε n ^ 2) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := 2 * M)).mul (hε.pow 2)
  simpa only [hypIIICost, f, zero_add] using hfirst.add hsum

end BouRabeeGwynne
