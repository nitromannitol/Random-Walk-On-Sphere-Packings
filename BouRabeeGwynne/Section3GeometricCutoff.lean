-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/Section3GeometricCutoff.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.Section3HarmonicIteration
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! The actual hypothesis II witness terminates the harmonic-replacement iteration. -/

open scoped Classical BigOperators

namespace BouRabeeGwynne

noncomputable def geometricVolumeCutoff (K q : ℝ) : ℕ :=
  ⌈(q + Real.log K) / Real.log 2⌉₊ + 1

lemma geometricVolumeCutoff_lt {K q : ℝ} (hK : 1 ≤ K) (hq : 0 ≤ q) :
    (geometricVolumeCutoff K q : ℝ) < (q + Real.log K) / Real.log 2 + 2 := by
  have hlog : 0 ≤ Real.log K := Real.log_nonneg hK
  have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hceil := Nat.ceil_lt_add_one (div_nonneg (add_nonneg hq hlog) hpos.le)
  simp only [geometricVolumeCutoff, Nat.cast_add, Nat.cast_one]
  linarith

/-- The cutoff makes the geometric mass strictly smaller than `exp(-q)`.
This is the volume lower bound appearing in the actual hypothesis (II). -/
theorem geometric_mass_lt_exp_neg {K q : ℝ} (hK : 1 ≤ K) :
    K * (1 / 2 : ℝ) ^ geometricVolumeCutoff K q < Real.exp (-q) := by
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hceil := Nat.le_ceil ((q + Real.log K) / Real.log 2)
  have hN : (q + Real.log K) / Real.log 2 < (geometricVolumeCutoff K q : ℝ) := by
    simp only [geometricVolumeCutoff, Nat.cast_add, Nat.cast_one]
    linarith
  have hN' : q + Real.log K < (geometricVolumeCutoff K q : ℝ) * Real.log 2 :=
    (div_lt_iff₀ hlog).mp hN
  have hpow : (1 / 2 : ℝ) ^ geometricVolumeCutoff K q < Real.exp (-q) / K := by
    rw [Real.pow_lt_iff_lt_log (by norm_num) (div_pos (Real.exp_pos _) hKpos),
      Real.log_div (Real.exp_ne_zero _) hKpos.ne', Real.log_exp]
    simp only [one_div, Real.log_inv]
    linarith
  simpa only [mul_comm] using (lt_div_iff₀ hKpos).mp hpow

lemma geometricVolumeCutoff_cost {K q ε : ℝ} (hK : 1 ≤ K) (hq : 0 ≤ q)
    (hε : 0 ≤ ε) :
    (geometricVolumeCutoff K q : ℝ) * ε ≤
      (ε * q) / Real.log 2 + ε * (Real.log K / Real.log 2 + 2) := by
  calc
    _ ≤ ((q + Real.log K) / Real.log 2 + 2) * ε :=
      mul_le_mul_of_nonneg_right (geometricVolumeCutoff_lt hK hq).le hε
    _ = _ := by ring

namespace FiniteConductanceNetwork

variable {V : Type*} [Fintype V] (N : FiniteConductanceNetwork V)

/-- The actual harmonic-replacement sequence terminates once its geometric
volume upper bound falls below the positive tile-volume lower bound. -/
theorem harmonicIteration_empty_at_volume_cutoff
    (A : Set V) (haccess : N.BoundaryAccessible A) (g : V → ℝ)
    (κ δ : ℕ → ℝ) (vol : V → ℝ) {K q : ℝ} (hK : 1 ≤ K)
    (hlower : ∀ v ∈ A, Real.exp (-q) ≤ vol v)
    (hupper : ∀ j, ∀ v ∈ (N.harmonicIteration A haccess g κ δ j).region,
      vol v ≤ K * (1 / 2 : ℝ) ^ j) :
    (N.harmonicIteration A haccess g κ δ (geometricVolumeCutoff K q)).region = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have hvA : v ∈ A := by
    have hsub := N.harmonicIteration_region_antitone A haccess g κ δ
      (Nat.zero_le (geometricVolumeCutoff K q)) hv
    exact hsub
  exact (not_lt_of_ge (hlower v hvA))
    ((hupper _ v hv).trans_lt (geometric_mass_lt_exp_neg hK))

/-- Once the independently proved geometric upper bound is supplied, the
maximum-principle iteration controls every solution with the expected linear
cost in the number of replacements. -/
theorem harmonicIteration_uniform_error_of_volume_decay
    (A : Set V) (haccess : N.BoundaryAccessible A) (g h : V → ℝ)
    (hsol : N.SolvesDirichlet A g h) {κ δ : ℝ} (hκ : 0 ≤ κ) (hδ : 0 ≤ δ)
    (vol : V → ℝ) {K q : ℝ} (hK : 1 ≤ K)
    (hlower : ∀ v ∈ A, Real.exp (-q) ≤ vol v)
    (hupper : ∀ j, ∀ v ∈
      (N.harmonicIteration A haccess g (fun _ => κ) (fun _ => δ) j).region,
      vol v ≤ K * (1 / 2 : ℝ) ^ j) :
    ∀ v, |h v - g v| ≤ (geometricVolumeCutoff K q : ℝ) * (κ + δ) := by
  intro v
  have hempty := N.harmonicIteration_empty_at_volume_cutoff A haccess g
    (fun _ => κ) (fun _ => δ) vol hK hlower hupper
  have hv : v ∉ (N.harmonicIteration A haccess g
      (fun _ => κ) (fun _ => δ) (geometricVolumeCutoff K q)).region := by
    rw [hempty]
    simp
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
    N.harmonicIteration_error_outside_of_solves A haccess g h hsol
      (fun _ => κ) (fun _ => δ) (fun _ => hκ) (fun _ => hδ) _ hv

end FiniteConductanceNetwork
end BouRabeeGwynne
