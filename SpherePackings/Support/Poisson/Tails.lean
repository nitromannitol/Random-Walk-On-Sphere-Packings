import SpherePackings.Support.Poisson.Basic

/-!
# Tail bounds for Poisson counts

The two estimates on Poisson counts used in the proof of Proposition 1.1
(`rw-spheres.tex:1690-1764`): an empty cube has probability `exp(-λ)`, and two or more points
have probability at most `λ²` (display (5.2), with constant 1 for every `λ ≥ 0`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace SpherePackings

variable {d : ℕ}

theorem poissonMeasure_real_zero (r : ℝ≥0) :
    (poissonMeasure r).real {0} = Real.exp (-(r : ℝ)) := by
  rw [poissonMeasure_real_singleton]
  simp

/-- `1 - e^{-x} (1 + x) ≤ x²` for `x ≥ 0`. -/
private lemma one_sub_exp_neg_add_le {x : ℝ} (hx : 0 ≤ x) :
    1 - (Real.exp (-x) + Real.exp (-x) * x) ≤ x ^ 2 := by
  rcases le_total x 1 with h | h
  · have hexp : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hmul : Real.exp x * Real.exp (-x) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hbound : Real.exp x - 1 - x ≤ x ^ 2 :=
      (le_abs_self _).trans (Real.abs_exp_sub_one_sub_id_le (by rw [abs_of_nonneg hx]; exact h))
    have hid : 1 - (Real.exp (-x) + Real.exp (-x) * x) =
        Real.exp (-x) * (Real.exp x - 1 - x) := by
      linear_combination -hmul
    rw [hid]
    calc Real.exp (-x) * (Real.exp x - 1 - x) ≤ Real.exp (-x) * x ^ 2 :=
          mul_le_mul_of_nonneg_left hbound (Real.exp_nonneg _)
      _ ≤ x ^ 2 := mul_le_of_le_one_left (sq_nonneg x) hexp
  · have h1 : (1 : ℝ) ≤ x ^ 2 := one_le_pow₀ h
    have h2 : 0 ≤ Real.exp (-x) * x := mul_nonneg (Real.exp_nonneg _) hx
    have h3 : 0 ≤ Real.exp (-x) := Real.exp_nonneg _
    linarith

/-- Display (5.2): a Poisson count with mean `r` is at least two with probability at most `r²`. -/
theorem poissonMeasure_real_two_le (r : ℝ≥0) :
    (poissonMeasure r).real {n | 2 ≤ n} ≤ (r : ℝ) ^ 2 := by
  have hset : {n : ℕ | 2 ≤ n} = ({0} ∪ {1} : Set ℕ)ᶜ := by
    ext n
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff]
    omega
  have hdisj : Disjoint ({0} : Set ℕ) {1} := Set.disjoint_singleton.2 (by norm_num)
  have hunion : (poissonMeasure r).real ({0} ∪ {1} : Set ℕ) =
      Real.exp (-(r : ℝ)) + Real.exp (-(r : ℝ)) * r := by
    rw [measureReal_union hdisj MeasurableSet.of_discrete, poissonMeasure_real_zero,
      poissonMeasure_real_singleton]
    simp
  rw [hset, measureReal_compl MeasurableSet.of_discrete, probReal_univ, hunion]
  exact one_sub_exp_neg_add_le (NNReal.coe_nonneg r)

namespace IsPoissonPointProcess

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Λ : Ω → Set (EuclideanSpace ℝ (Fin d))} {ν : Measure (EuclideanSpace ℝ (Fin d))}

omit [IsProbabilityMeasure P] in
/-- A bounded measurable set of finite intensity contains no point with probability
`exp (-ν B)`. -/
theorem measureReal_empty (h : IsPoissonPointProcess P Λ ν) {B : Set (EuclideanSpace ℝ (Fin d))}
    (hB : MeasurableSet B) (hBb : Bornology.IsBounded B) (hνB : ν B ≠ ∞) :
    P.real {ω | Λ ω ∩ B = ∅} = Real.exp (-(ν B).toReal) := by
  have hL : HasLaw (fun ω => (Λ ω ∩ B).ncard) (poissonMeasure (ν B).toNNReal) P :=
    h.hasLaw B hB hνB
  have key : P.real {ω | (Λ ω ∩ B).ncard = 0} =
      (poissonMeasure (ν B).toNNReal).real {n | n = 0} :=
    hL.measureReal_eq (p := fun n : ℕ => n = 0) MeasurableSet.of_discrete
  have hset : {ω | Λ ω ∩ B = ∅} = {ω | (Λ ω ∩ B).ncard = 0} := by
    ext ω
    exact (Set.ncard_eq_zero (h.finite B hBb ω)).symm
  have hsing : {n : ℕ | n = 0} = {0} := by
    ext n
    simp
  rw [hset, key, hsing]
  exact poissonMeasure_real_zero _

omit [IsProbabilityMeasure P] in
/-- A bounded measurable set of finite intensity contains at least two points with probability at
most `(ν B)²`. -/
theorem measureReal_not_subsingleton_le (h : IsPoissonPointProcess P Λ ν)
    {B : Set (EuclideanSpace ℝ (Fin d))} (hB : MeasurableSet B) (hBb : Bornology.IsBounded B)
    (hνB : ν B ≠ ∞) :
    P.real {ω | ¬ (Λ ω ∩ B).Subsingleton} ≤ (ν B).toReal ^ 2 := by
  have hL : HasLaw (fun ω => (Λ ω ∩ B).ncard) (poissonMeasure (ν B).toNNReal) P :=
    h.hasLaw B hB hνB
  have key : P.real {ω | 2 ≤ (Λ ω ∩ B).ncard} =
      (poissonMeasure (ν B).toNNReal).real {n | 2 ≤ n} :=
    hL.measureReal_eq (p := fun n : ℕ => 2 ≤ n) MeasurableSet.of_discrete
  have hset : {ω | ¬ (Λ ω ∩ B).Subsingleton} = {ω | 2 ≤ (Λ ω ∩ B).ncard} := by
    ext ω
    have hiff : (Λ ω ∩ B).ncard ≤ 1 ↔ (Λ ω ∩ B).Subsingleton :=
      Set.ncard_le_one (h.finite B hBb ω)
    show ¬ (Λ ω ∩ B).Subsingleton ↔ 2 ≤ (Λ ω ∩ B).ncard
    rw [← hiff]
    omega
  rw [hset, key]
  exact poissonMeasure_real_two_le _

end IsPoissonPointProcess

end SpherePackings
