-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/MatchedCellCoupling.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.SubcouplingCompletion

/-!
# Actual coupling of the common mass of two measurable cells

The common mass is the minimum of the two cell probabilities. Restricted
measures are scaled to exactly that mass and coupled by their normalized
product. Zero-probability cells are included in the formulas.
-/

open MeasureTheory Set
open scoped ENNReal
namespace BouRabeeGwynne

noncomputable def cappedRestrict {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (E : Set X) (c : ℝ≥0∞) : Measure X :=
  (c / μ E) • μ.restrict E

lemma cappedRestrict_univ {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (E : Set X) {c : ℝ≥0∞}
    (hc : c ≤ μ E) : cappedRestrict μ E c univ = c := by
  rw [cappedRestrict, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
  exact ENNReal.div_mul_cancel' (fun h ↦ le_zero_iff.mp (h ▸ hc))
    (fun h ↦ (measure_ne_top μ E h).elim)

lemma cappedRestrict_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (E : Set X) {c : ℝ≥0∞}
    (hc : c ≤ μ E) : cappedRestrict μ E c ≤ μ.restrict E := by
  have hratio : c / μ E ≤ 1 := by
    by_cases hzero : μ E = 0
    · have hc0 : c = 0 := le_zero_iff.mp (hzero ▸ hc)
      simp [hc0]
    · exact (ENNReal.div_le_iff hzero (measure_ne_top μ E)).mpr (by simpa using hc)
  intro A
  rw [cappedRestrict, Measure.smul_apply, smul_eq_mul]
  exact (mul_le_mul_left hratio (μ.restrict E A)).trans_eq (one_mul _)

lemma cappedRestrict_isFiniteMeasure {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (E : Set X) {c : ℝ≥0∞}
    (hc : c ≤ μ E) : IsFiniteMeasure (cappedRestrict μ E c) :=
  isFiniteMeasure_of_le (μ.restrict E) (cappedRestrict_le μ E hc)

/-- The exact matched product of the common mass in two cells. -/
noncomputable def matchedCellCoupling {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (E : Set X) (F : Set Y) : Measure (X × Y) :=
  balancedProduct (cappedRestrict μ E (min (μ E) (ν F)))
    (cappedRestrict ν F (min (μ E) (ν F)))

lemma matchedCellCoupling_fst {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set X) (F : Set Y) :
    (matchedCellCoupling μ ν E F).fst = cappedRestrict μ E (min (μ E) (ν F)) := by
  letI := cappedRestrict_isFiniteMeasure μ E (min_le_left _ (ν F))
  letI := cappedRestrict_isFiniteMeasure ν F (min_le_right (μ E) _)
  apply balancedProduct_fst
  rw [cappedRestrict_univ ν F (min_le_right _ _),
    cappedRestrict_univ μ E (min_le_left _ _)]

lemma matchedCellCoupling_snd {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set X) (F : Set Y) :
    (matchedCellCoupling μ ν E F).snd = cappedRestrict ν F (min (μ E) (ν F)) := by
  letI := cappedRestrict_isFiniteMeasure μ E (min_le_left _ (ν F))
  letI := cappedRestrict_isFiniteMeasure ν F (min_le_right (μ E) _)
  apply balancedProduct_snd
  rw [cappedRestrict_univ ν F (min_le_right _ _),
    cappedRestrict_univ μ E (min_le_left _ _)]

lemma matchedCellCoupling_univ {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set X) (F : Set Y) :
    matchedCellCoupling μ ν E F univ = min (μ E) (ν F) := by
  rw [← Measure.fst_univ, matchedCellCoupling_fst,
    cappedRestrict_univ μ E (min_le_left _ _)]

instance matchedCellCoupling_isFiniteMeasure {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set X) (F : Set Y) : IsFiniteMeasure (matchedCellCoupling μ ν E F) where
  measure_univ_lt_top := by
    rw [matchedCellCoupling_univ]
    exact (min_le_left _ _).trans_lt (measure_lt_top μ E)

/-- The matched measure is supported on the actual product of its cells. -/
lemma matchedCellCoupling_compl_prod_eq_zero {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {E : Set X} {F : Set Y} (hE : MeasurableSet E) (hF : MeasurableSet F) :
    matchedCellCoupling μ ν E F (E ×ˢ F)ᶜ = 0 := by
  have hleft : matchedCellCoupling μ ν E F (Prod.fst ⁻¹' Eᶜ) = 0 := by
    rw [← Measure.fst_apply hE.compl, matchedCellCoupling_fst]
    apply le_zero_iff.mp
    exact (cappedRestrict_le μ E (min_le_left _ _) Eᶜ).trans_eq (by
      rw [Measure.restrict_apply hE.compl, compl_inter_self, measure_empty])
  have hright : matchedCellCoupling μ ν E F (Prod.snd ⁻¹' Fᶜ) = 0 := by
    rw [← Measure.snd_apply hF.compl, matchedCellCoupling_snd]
    apply le_zero_iff.mp
    exact (cappedRestrict_le ν F (min_le_right _ _) Fᶜ).trans_eq (by
      rw [Measure.restrict_apply hF.compl, compl_inter_self, measure_empty])
  apply le_zero_iff.mp
  calc
    matchedCellCoupling μ ν E F (E ×ˢ F)ᶜ ≤
        matchedCellCoupling μ ν E F ((Prod.fst ⁻¹' Eᶜ) ∪ (Prod.snd ⁻¹' Fᶜ)) := by
      apply measure_mono
      intro p hp
      simpa only [mem_compl_iff, mem_prod, not_and_or, mem_union, mem_preimage] using hp
    _ ≤ matchedCellCoupling μ ν E F (Prod.fst ⁻¹' Eᶜ) +
        matchedCellCoupling μ ν E F (Prod.snd ⁻¹' Fᶜ) := measure_union_le _ _
    _ = 0 := by rw [hleft, hright, zero_add]

end BouRabeeGwynne
