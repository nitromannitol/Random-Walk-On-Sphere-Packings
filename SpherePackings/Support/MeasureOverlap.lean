-- Built on Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne (commit cf73d6e).
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.Set.Card

/-!
# Sums of measures of sets with bounded overlap

If every point lies in at most `M` of finitely many measurable sets, the sum of their measures is
at most `M` times the measure of their union.  Used in the union bound of the proof of
Proposition 1.1 (`rw-spheres.tex:1717-1755`).
-/

open MeasureTheory
open scoped ENNReal

namespace SpherePackings

/-- Pointwise bound: the number of sets containing `y` is at most `M` times the indicator of the
union. -/
private lemma sum_indicator_le_of_ncard_le {α ι : Type*} (B : ι → Set α) (F : Finset ι) {M : ℕ}
    (hM : ∀ y, {i | i ∈ F ∧ y ∈ B i}.ncard ≤ M) (y : α) :
    ∑ i ∈ F, (B i).indicator (1 : α → ℝ≥0∞) y ≤
      (M : ℝ≥0∞) * (⋃ i ∈ F, B i).indicator 1 y := by
  classical
  by_cases hy : y ∈ ⋃ i ∈ F, B i
  · rw [Set.indicator_of_mem hy, Pi.one_apply, mul_one]
    have hset : {i | i ∈ F ∧ y ∈ B i} = ↑(F.filter fun i => y ∈ B i) := by
      ext i
      simp
    have hcard := hM y
    rw [hset, Set.ncard_coe_finset] at hcard
    simp only [Set.indicator_apply, Pi.one_apply]
    rw [Finset.sum_boole]
    exact_mod_cast hcard
  · rw [Set.indicator_of_notMem hy, mul_zero]
    refine le_of_eq (Finset.sum_eq_zero fun i hi => ?_)
    refine Set.indicator_of_notMem (fun hyi => hy (Set.mem_biUnion hi hyi)) _

theorem sum_measure_le_of_ncard_le {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    (F : Finset ι) (B : ι → Set α) (hB : ∀ i ∈ F, MeasurableSet (B i)) {M : ℕ}
    (hM : ∀ y, {i | i ∈ F ∧ y ∈ B i}.ncard ≤ M) :
    ∑ i ∈ F, μ (B i) ≤ M * μ (⋃ i ∈ F, B i) := by
  have hU : MeasurableSet (⋃ i ∈ F, B i) := Finset.measurableSet_biUnion F hB
  calc ∑ i ∈ F, μ (B i) = ∑ i ∈ F, ∫⁻ y, (B i).indicator 1 y ∂μ := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [lintegral_indicator_one (hB i hi)]
    _ = ∫⁻ y, ∑ i ∈ F, (B i).indicator 1 y ∂μ :=
        (lintegral_finsetSum F fun i hi => measurable_one.indicator (hB i hi)).symm
    _ ≤ ∫⁻ y, (M : ℝ≥0∞) * (⋃ i ∈ F, B i).indicator 1 y ∂μ :=
        lintegral_mono fun y => sum_indicator_le_of_ncard_le B F hM y
    _ = M * μ (⋃ i ∈ F, B i) := by
        rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top M), lintegral_indicator_one hU]

end SpherePackings
