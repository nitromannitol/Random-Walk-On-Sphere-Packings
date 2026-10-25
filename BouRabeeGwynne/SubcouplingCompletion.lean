module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/SubcouplingCompletion.lean` at commit cf73d6e); unchanged apart from this header.
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Sub

@[expose] public section

/-!
# Completing a finite matched coupling by an actual product measure

A partial coupling with dominated marginals is completed using the product of
its two residual marginals, normalized by their common mass. This includes the
zero-residual case. It is the explicit coupling construction for finite spatial
partitions in the Section 4 skeleton argument.
-/

open MeasureTheory Set
open scoped ENNReal
namespace BouRabeeGwynne

/-- Product measure of two equal-mass finite measures, normalized to keep that
mass rather than its square. The formula also handles zero measures. -/
noncomputable def balancedProduct {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (α : Measure X) (β : Measure Y) : Measure (X × Y) :=
  (α univ)⁻¹ • α.prod β

lemma balancedProduct_fst {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (α : Measure X) (β : Measure Y) [IsFiniteMeasure α] [IsFiniteMeasure β]
    (hmass : β univ = α univ) : (balancedProduct α β).fst = α := by
  by_cases hzero : α univ = 0
  · have hα : α = 0 := Measure.measure_univ_eq_zero.mp hzero
    simp [balancedProduct, hα]
  · rw [balancedProduct, Measure.fst, Measure.map_smul _ measurable_fst.aemeasurable, Measure.map_fst_prod,
      hmass, smul_smul, ENNReal.inv_mul_cancel hzero (measure_ne_top α univ), one_smul]

lemma balancedProduct_snd {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (α : Measure X) (β : Measure Y) [IsFiniteMeasure α] [IsFiniteMeasure β]
    (hmass : β univ = α univ) : (balancedProduct α β).snd = β := by
  by_cases hzero : α univ = 0
  · have hα : α = 0 := Measure.measure_univ_eq_zero.mp hzero
    have hβ : β = 0 := Measure.measure_univ_eq_zero.mp (hmass.trans hzero)
    simp [balancedProduct, hα, hβ]
  · rw [balancedProduct, Measure.snd, Measure.map_smul _ measurable_snd.aemeasurable, Measure.map_snd_prod,
      smul_smul, ENNReal.inv_mul_cancel hzero (measure_ne_top α univ), one_smul]

/-- The actual completion of a partial coupling. -/
noncomputable def completeSubcoupling {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (ρ : Measure (X × Y)) : Measure (X × Y) :=
  ρ + balancedProduct (μ - ρ.fst) (ν - ρ.snd)

private lemma residual_masses_eq {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (ρ : Measure (X × Y))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsFiniteMeasure ρ]
    (hfst : ρ.fst ≤ μ) (hsnd : ρ.snd ≤ ν) :
    (ν - ρ.snd) univ = (μ - ρ.fst) univ := by
  rw [Measure.sub_apply MeasurableSet.univ hsnd,
    Measure.sub_apply MeasurableSet.univ hfst, measure_univ (μ := μ), measure_univ (μ := ν),
    Measure.fst_univ, Measure.snd_univ]

lemma completeSubcoupling_fst {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (ρ : Measure (X × Y))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsFiniteMeasure ρ]
    (hfst : ρ.fst ≤ μ) (hsnd : ρ.snd ≤ ν) :
    (completeSubcoupling μ ν ρ).fst = μ := by
  rw [completeSubcoupling, Measure.fst_add,
    balancedProduct_fst _ _ (residual_masses_eq μ ν ρ hfst hsnd),
    add_comm, Measure.sub_add_cancel_of_le hfst]

lemma completeSubcoupling_snd {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (ρ : Measure (X × Y))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsFiniteMeasure ρ]
    (hfst : ρ.fst ≤ μ) (hsnd : ρ.snd ≤ ν) :
    (completeSubcoupling μ ν ρ).snd = ν := by
  rw [completeSubcoupling, Measure.snd_add,
    balancedProduct_snd _ _ (residual_masses_eq μ ν ρ hfst hsnd),
    add_comm, Measure.sub_add_cancel_of_le hsnd]

lemma completeSubcoupling_isProbabilityMeasure {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (ρ : Measure (X × Y))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsFiniteMeasure ρ]
    (hfst : ρ.fst ≤ μ) (hsnd : ρ.snd ≤ ν) :
    IsProbabilityMeasure (completeSubcoupling μ ν ρ) where
  measure_univ := by
    rw [← Measure.fst_univ, completeSubcoupling_fst μ ν ρ hfst hsnd, measure_univ]

/-- Any event avoided by the matched partial coupling has probability at most
the unmatched mass in the actual completed coupling. No existence of a
coupling is assumed. -/
theorem completeSubcoupling_bad_event_le {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (ρ : Measure (X × Y))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsFiniteMeasure ρ]
    (hfst : ρ.fst ≤ μ) (hsnd : ρ.snd ≤ ν)
    {B : Set (X × Y)} (hB : ρ B = 0) :
    completeSubcoupling μ ν ρ B ≤ 1 - ρ univ := by
  rw [completeSubcoupling, Measure.add_apply, hB, zero_add]
  calc
    balancedProduct (μ - ρ.fst) (ν - ρ.snd) B ≤
        balancedProduct (μ - ρ.fst) (ν - ρ.snd) univ := measure_mono (subset_univ B)
    _ = (μ - ρ.fst) univ := by
      rw [← Measure.fst_univ,
        balancedProduct_fst _ _ (residual_masses_eq μ ν ρ hfst hsnd)]
    _ = 1 - ρ univ := by
      rw [Measure.sub_apply MeasurableSet.univ hfst, measure_univ, Measure.fst_univ]

end BouRabeeGwynne
