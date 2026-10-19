-- Built on Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne (commit cf73d6e).
import BouRabeeGwynne.HypIIICostBound
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The corrected Case III cost is `O(M ε log(1/ε))`

leobon12's corrected iteration for Theorem 3.7 bounds the error by `hypIIICost A M ε δ`, where the
scales satisfy `δ_i ≤ ε` and `δ_i ≤ J r^i` with `r < 1`.  Splitting the series at the first index
`i₀` with `J r^{i₀} ≤ ε` gives the rate of Theorem 3.7 (`rw-spheres.tex:1314-1340`): the first `i₀`
terms are each `O(M ε)` and `i₀ = O(log(1/ε))`; the tail is geometric and `O(M ε)`.
-/

namespace SpherePackings

open BouRabeeGwynne

/-- The constant of the Case III rate. -/
noncomputable def hypIIIRateConstant (A J r : ℝ) : ℝ :=
  (A + 2) * ((Real.log (max J 1) / Real.log 2 + 1) / Real.log (1 / r) + 1 / Real.log 2) +
    (1 + A / (1 - r) + 1 / (1 - Real.sqrt r) + 1 / (1 - r ^ 2)) / Real.log 2

/-- A term before the cutoff: `δ ≤ ε` makes it at most `(A + 2) M ε`. -/
private lemma hypIIIterm_early {A M ε d : ℝ} (hA : 0 ≤ A) (hM : 1 ≤ M) (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) (hd0 : 0 ≤ d) (hdε : d ≤ ε) :
    A * M * d + Real.sqrt (ε * d) + 2 * M * d ^ 2 ≤ (A + 2) * M * ε := by
  have hM0 : 0 ≤ M := by linarith
  have h1 : A * M * d ≤ A * M * ε := mul_le_mul_of_nonneg_left hdε (mul_nonneg hA hM0)
  have h2 : Real.sqrt (ε * d) ≤ M * ε := by
    calc Real.sqrt (ε * d) ≤ Real.sqrt (ε * ε) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hdε hε.le)
      _ = ε := Real.sqrt_mul_self hε.le
      _ ≤ M * ε := le_mul_of_one_le_left hε.le hM
  have h3 : 2 * M * d ^ 2 ≤ M * ε := by
    calc 2 * M * d ^ 2 ≤ 2 * M * ε ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd0 hdε 2) (by linarith)
      _ = M * ε * (2 * ε) := by ring
      _ ≤ M * ε * 1 := mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hM0 hε.le)
      _ = M * ε := mul_one _
  have e : (A + 2) * M * ε = A * M * ε + 2 * (M * ε) := by ring
  linarith

/-- A term after the cutoff: `δ ≤ ε r ^ k` makes it at most
`M ε (A r^k + (√r)^k + (r²)^k)`. -/
private lemma hypIIIterm_tail {A M ε r d : ℝ} (hA : 0 ≤ A) (hM : 1 ≤ M) (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) (hr0 : 0 ≤ r) (k : ℕ) (hd0 : 0 ≤ d) (hdε : d ≤ ε * r ^ k) :
    A * M * d + Real.sqrt (ε * d) + 2 * M * d ^ 2 ≤
      M * ε * (A * r ^ k + Real.sqrt r ^ k + (r ^ 2) ^ k) := by
  have hM0 : 0 ≤ M := by linarith
  have hpowsqrt : ∀ n : ℕ, Real.sqrt (r ^ n) = Real.sqrt r ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg hr0 n), ih, pow_succ]
  have hsk : 0 ≤ Real.sqrt r ^ k := pow_nonneg (Real.sqrt_nonneg r) k
  have hr2k : 0 ≤ (r ^ 2) ^ k := pow_nonneg (sq_nonneg r) k
  have hpow2 : (r ^ 2) ^ k = (r ^ k) ^ 2 := by
    rw [← pow_mul, ← pow_mul, mul_comm]
  have h1 : A * M * d ≤ M * ε * (A * r ^ k) := by
    calc A * M * d ≤ A * M * (ε * r ^ k) := mul_le_mul_of_nonneg_left hdε (mul_nonneg hA hM0)
      _ = M * ε * (A * r ^ k) := by ring
  have hsq : Real.sqrt (ε * d) ≤ ε * Real.sqrt r ^ k := by
    calc Real.sqrt (ε * d) ≤ Real.sqrt (ε * (ε * r ^ k)) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hdε hε.le)
      _ = Real.sqrt (ε ^ 2) * Real.sqrt (r ^ k) := by
          rw [show ε * (ε * r ^ k) = ε ^ 2 * r ^ k by ring, Real.sqrt_mul (sq_nonneg ε)]
      _ = ε * Real.sqrt r ^ k := by rw [Real.sqrt_sq hε.le, hpowsqrt k]
  have h2 : ε * Real.sqrt r ^ k ≤ M * ε * Real.sqrt r ^ k :=
    mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hε.le hM) hsk
  have h3 : 2 * M * d ^ 2 ≤ M * ε * (r ^ 2) ^ k := by
    calc 2 * M * d ^ 2 ≤ 2 * M * (ε * r ^ k) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd0 hdε 2) (by linarith)
      _ = M * ε * (r ^ 2) ^ k * (2 * ε) := by rw [hpow2]; ring
      _ ≤ M * ε * (r ^ 2) ^ k * 1 :=
          mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (mul_nonneg hM0 hε.le) hr2k)
      _ = M * ε * (r ^ 2) ^ k := mul_one _
  have e : M * ε * (A * r ^ k + Real.sqrt r ^ k + (r ^ 2) ^ k) =
      M * ε * (A * r ^ k) + M * ε * Real.sqrt r ^ k + M * ε * (r ^ 2) ^ k := by ring
  linarith

/-- **The Case III cost bound.** -/
theorem hypIIICost_le_rate {A M ε J r : ℝ} (δ : ℕ → ℝ) (hA : 0 ≤ A) (hM : 1 ≤ M)
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hJ : 0 ≤ J) (hr0 : 0 < r) (hr1 : r < 1)
    (hδ0 : ∀ i, 0 ≤ δ i) (hδε : ∀ i, δ i ≤ ε) (hδJ : ∀ i, δ i ≤ J * r ^ i) :
    hypIIICost A M ε δ ≤ hypIIIRateConstant A J r * M * ε * Real.log (1 / ε) := by
  unfold hypIIIRateConstant hypIIICost
  -- the bound only uses `1 ≤ M` and `ε ≤ 1/2`; `M * ε ≤ 1` is not needed here
  have hM0 : 0 ≤ M := by linarith
  have hr1' : 0 < 1 - r := by linarith
  have hr2 : r ^ 2 < 1 := by nlinarith
  have hs0 : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
  have hs1 : Real.sqrt r < 1 := by simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt hr0.le hr1
  -- abbreviations for the quantities of the rate
  set N : ℝ := max J 1 with hNdef
  set ρ : ℝ := Real.log (1 / r) with hρdef
  set L : ℝ := Real.log (1 / ε) with hLdef
  have hN1 : 1 ≤ N := le_max_right J 1
  have hNJ : J ≤ N := le_max_left J 1
  have hN0 : 0 < N := by linarith
  have hP0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hρ : 0 < ρ := Real.log_pos (one_lt_one_div hr0 hr1)
  have hρr : ρ = -Real.log r := by rw [hρdef, one_div, Real.log_inv]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL2 : Real.log 2 ≤ L :=
    Real.log_le_log (by norm_num) ((le_div_iff₀ hε).mpr (by linarith))
  have hL0 : 0 ≤ L := by linarith
  have hLε : L = -Real.log ε := by rw [hLdef, one_div, Real.log_inv]
  have h1L : 1 ≤ L / Real.log 2 := by rw [le_div_iff₀ hlog2]; linarith
  have hlogNε : Real.log (N / ε) = Real.log N + L := by
    rw [Real.log_div hN0.ne' hε.ne', hLε]; ring
  -- the cutoff index `i₀`, for which `J r^{i₀} ≤ ε`
  set i₀ : ℕ := ⌈Real.log (N / ε) / ρ⌉₊ with hi₀def
  have hlogNε0 : 0 ≤ Real.log (N / ε) := by rw [hlogNε]; linarith
  have hi₀le : Real.log (N / ε) / ρ ≤ (i₀ : ℝ) := Nat.le_ceil _
  have hi₀lt : (i₀ : ℝ) < Real.log (N / ε) / ρ + 1 :=
    Nat.ceil_lt_add_one (div_nonneg hlogNε0 hρ.le)
  have hlogle : Real.log (N / ε) ≤ (i₀ : ℝ) * ρ := (div_le_iff₀ hρ).mp hi₀le
  have hrpow : r ^ i₀ * N ≤ ε := by
    have hlog : Real.log (r ^ i₀ * N) ≤ Real.log ε := by
      rw [Real.log_mul (pow_pos hr0 i₀).ne' hN0.ne', Real.log_pow]
      rw [hlogNε, hρr] at hlogle
      linarith
    exact (Real.log_le_log_iff (mul_pos (pow_pos hr0 i₀) hN0) hε).mp hlog
  have hJr : J * r ^ i₀ ≤ ε :=
    calc J * r ^ i₀ ≤ N * r ^ i₀ := mul_le_mul_of_nonneg_right hNJ (pow_nonneg hr0.le i₀)
      _ = r ^ i₀ * N := mul_comm _ _
      _ ≤ ε := hrpow
  have hterm : ∀ k : ℕ, δ (k + i₀) ≤ ε * r ^ k := fun k =>
    calc δ (k + i₀) ≤ J * r ^ (k + i₀) := hδJ _
      _ = J * r ^ i₀ * r ^ k := by ring
      _ ≤ ε * r ^ k := mul_le_mul_of_nonneg_right hJr (pow_nonneg hr0.le k)
  -- split the series at `i₀`
  have hsum : Summable (fun i => A * M * δ i + Real.sqrt (ε * δ i) + 2 * M * δ i ^ 2) :=
    hypIIICost_summable δ hA hM0 hε.le hJ hr0.le hr1 hδ0 hδε hδJ
  have hsplit := Summable.sum_add_tsum_nat_add i₀ hsum
  have hshift := (summable_nat_add_iff i₀).mpr hsum
  -- the terms before the cutoff
  have hearly : ∑ i ∈ Finset.range i₀,
      (A * M * δ i + Real.sqrt (ε * δ i) + 2 * M * δ i ^ 2) ≤
        (i₀ : ℝ) * ((A + 2) * M * ε) := by
    calc ∑ i ∈ Finset.range i₀, (A * M * δ i + Real.sqrt (ε * δ i) + 2 * M * δ i ^ 2)
        ≤ ∑ i ∈ Finset.range i₀, (A + 2) * M * ε :=
          Finset.sum_le_sum fun i _ => hypIIIterm_early hA hM hε hε2 (hδ0 i) (hδε i)
      _ = (i₀ : ℝ) * ((A + 2) * M * ε) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- the terms after the cutoff: a geometric majorant
  have hgsum : Summable (fun k : ℕ => M * ε * (A * r ^ k + Real.sqrt r ^ k + (r ^ 2) ^ k)) := by
    have h1 := (summable_geometric_of_lt_one hr0.le hr1).mul_left A
    have h2 := summable_geometric_of_lt_one hs0 hs1
    have h3 := summable_geometric_of_lt_one (sq_nonneg r) hr2
    exact ((h1.add h2).add h3).mul_left (M * ε)
  set S : ℝ := A / (1 - r) + 1 / (1 - Real.sqrt r) + 1 / (1 - r ^ 2) with hSdef
  have hgval : ∑' k : ℕ, M * ε * (A * r ^ k + Real.sqrt r ^ k + (r ^ 2) ^ k) = M * ε * S := by
    have h1 := (summable_geometric_of_lt_one hr0.le hr1).mul_left A
    have h2 := summable_geometric_of_lt_one hs0 hs1
    have h3 := summable_geometric_of_lt_one (sq_nonneg r) hr2
    rw [tsum_mul_left, Summable.tsum_add (h1.add h2) h3, Summable.tsum_add h1 h2, tsum_mul_left,
      tsum_geometric_of_lt_one hr0.le hr1, tsum_geometric_of_lt_one hs0 hs1,
      tsum_geometric_of_lt_one (sq_nonneg r) hr2, hSdef]
    ring
  have htail_term : ∀ k : ℕ, A * M * δ (k + i₀) + Real.sqrt (ε * δ (k + i₀)) +
      2 * M * δ (k + i₀) ^ 2 ≤ M * ε * (A * r ^ k + Real.sqrt r ^ k + (r ^ 2) ^ k) := fun k =>
    hypIIIterm_tail hA hM hε hε2 hr0.le k (hδ0 (k + i₀)) (hterm k)
  have htail : ∑' k : ℕ, (A * M * δ (k + i₀) + Real.sqrt (ε * δ (k + i₀)) +
      2 * M * δ (k + i₀) ^ 2) ≤ M * ε * S :=
    (Summable.tsum_le_tsum htail_term hshift hgsum).trans_eq hgval
  have hbound := add_le_add hearly htail
  have h2M : 2 * M * ε ^ 2 ≤ M * ε := by
    calc 2 * M * ε ^ 2 = M * ε * (2 * ε) := by ring
      _ ≤ M * ε * 1 := mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hM0 hε.le)
      _ = M * ε := mul_one _
  -- the cutoff index is `O(log (1/ε))`
  have hi₀W : (i₀ : ℝ) ≤ ((Real.log N / Real.log 2 + 1) / ρ + 1 / Real.log 2) * L := by
    rw [hlogNε] at hi₀lt
    have e1 : ((Real.log N / Real.log 2 + 1) / ρ + 1 / Real.log 2) * L =
        Real.log N * L / Real.log 2 / ρ + L / ρ + L / Real.log 2 := by ring
    have e2 : (Real.log N + L) / ρ = Real.log N / ρ + L / ρ := add_div _ _ _
    have h2 : Real.log N ≤ Real.log N * L / Real.log 2 := by
      rw [mul_div_assoc]; exact le_mul_of_one_le_right hP0 h1L
    have h3 : Real.log N / ρ ≤ Real.log N * L / Real.log 2 / ρ :=
      div_le_div_of_nonneg_right h2 hρ.le
    linarith
  -- the constant
  have hfin : 1 + (A + 2) * (i₀ : ℝ) + S ≤
      ((A + 2) * ((Real.log N / Real.log 2 + 1) / ρ + 1 / Real.log 2) +
        (1 + A / (1 - r) + 1 / (1 - Real.sqrt r) + 1 / (1 - r ^ 2)) / Real.log 2) * L := by
    have hS0 : 0 ≤ S := by
      rw [hSdef]
      have a1 : 0 ≤ A / (1 - r) := div_nonneg hA hr1'.le
      have a2 : 0 ≤ 1 / (1 - Real.sqrt r) := div_nonneg zero_le_one (by linarith)
      have a3 : 0 ≤ 1 / (1 - r ^ 2) := div_nonneg zero_le_one (by linarith)
      linarith
    have e : ((A + 2) * ((Real.log N / Real.log 2 + 1) / ρ + 1 / Real.log 2) +
        (1 + A / (1 - r) + 1 / (1 - Real.sqrt r) + 1 / (1 - r ^ 2)) / Real.log 2) * L =
        (A + 2) * (((Real.log N / Real.log 2 + 1) / ρ + 1 / Real.log 2) * L) +
          (1 + S) * (L / Real.log 2) := by
      rw [hSdef]; ring
    have h4 : 1 + S ≤ (1 + S) * (L / Real.log 2) := le_mul_of_one_le_right (by linarith) h1L
    have h5 : (A + 2) * (i₀ : ℝ) ≤
        (A + 2) * (((Real.log N / Real.log 2 + 1) / ρ + 1 / Real.log 2) * L) :=
      mul_le_mul_of_nonneg_left hi₀W (by linarith)
    rw [e]
    linarith
  have hfinal := mul_le_mul_of_nonneg_left hfin (mul_nonneg hM0 hε.le)
  linarith [hsplit, hbound, h2M, hfinal]

end SpherePackings
