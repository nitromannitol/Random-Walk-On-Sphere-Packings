module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/FinitePartitionCoupling.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.MatchedCellCoupling

@[expose] public section

/-!
# Explicit finite spatial partition coupling

Pair disjoint measurable cells on the two spaces. In cell i the construction
matches exactly min(μ(Eᵢ),ν(Fᵢ)) mass. Its two marginals are the original laws;
any event disjoint from every paired cell has probability at most the unmatched
mass. The cells need not cover the whole space, so compact truncations are
allowed without introducing a special outside cell.
-/

open MeasureTheory Set
open scoped ENNReal
namespace BouRabeeGwynne

noncomputable def finiteMatchedCoupling {ι X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (E : ι → Set X) (F : ι → Set Y) : Measure (X × Y) :=
  Measure.sum (fun i ↦ matchedCellCoupling μ ν (E i) (F i))

lemma finiteMatchedCoupling_univ {ι X Y : Type*} [Fintype ι]
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : ι → Set X) (F : ι → Set Y) :
    finiteMatchedCoupling μ ν E F univ = ∑ i, min (μ (E i)) (ν (F i)) := by
  simp only [finiteMatchedCoupling, Measure.sum_apply _ MeasurableSet.univ,
    matchedCellCoupling_univ, tsum_fintype]

instance finiteMatchedCoupling_isFiniteMeasure {ι X Y : Type*} [Fintype ι]
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : ι → Set X) (F : ι → Set Y) :
    IsFiniteMeasure (finiteMatchedCoupling μ ν E F) where
  measure_univ_lt_top := by
    rw [finiteMatchedCoupling_univ, ENNReal.sum_lt_top]
    intro i hi
    exact (min_le_left _ _).trans_lt (measure_lt_top μ (E i))

lemma finiteMatchedCoupling_fst_le {ι X Y : Type*} [Fintype ι]
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {E : ι → Set X} (F : ι → Set Y)
    (hE : ∀ i, MeasurableSet (E i)) (hdE : Pairwise (fun i j ↦ Disjoint (E i) (E j))) :
    (finiteMatchedCoupling μ ν E F).fst ≤ μ := by
  calc
    (finiteMatchedCoupling μ ν E F).fst =
        Measure.sum (fun i ↦ cappedRestrict μ (E i) (min (μ (E i)) (ν (F i)))) := by
      simp only [finiteMatchedCoupling, Measure.fst_sum, matchedCellCoupling_fst]
    _ ≤ Measure.sum (fun i ↦ μ.restrict (E i)) := by
      apply Measure.le_iff.mpr
      intro A hA
      rw [Measure.sum_apply _ hA, Measure.sum_apply _ hA]
      exact ENNReal.tsum_le_tsum (fun i ↦ cappedRestrict_le μ (E i) (min_le_left _ _) A)
    _ = μ.restrict (⋃ i, E i) := (Measure.restrict_iUnion hdE hE).symm
    _ ≤ μ := Measure.restrict_le_self

lemma finiteMatchedCoupling_snd_le {ι X Y : Type*} [Fintype ι]
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : ι → Set X) {F : ι → Set Y}
    (hF : ∀ i, MeasurableSet (F i)) (hdF : Pairwise (fun i j ↦ Disjoint (F i) (F j))) :
    (finiteMatchedCoupling μ ν E F).snd ≤ ν := by
  calc
    (finiteMatchedCoupling μ ν E F).snd =
        Measure.sum (fun i ↦ cappedRestrict ν (F i) (min (μ (E i)) (ν (F i)))) := by
      simp only [finiteMatchedCoupling, Measure.snd_sum, matchedCellCoupling_snd]
    _ ≤ Measure.sum (fun i ↦ ν.restrict (F i)) := by
      apply Measure.le_iff.mpr
      intro A hA
      rw [Measure.sum_apply _ hA, Measure.sum_apply _ hA]
      exact ENNReal.tsum_le_tsum (fun i ↦ cappedRestrict_le ν (F i) (min_le_right _ _) A)
    _ = ν.restrict (⋃ i, F i) := (Measure.restrict_iUnion hdF hF).symm
    _ ≤ ν := Measure.restrict_le_self

noncomputable def finitePartitionCoupling {ι X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (E : ι → Set X) (F : ι → Set Y) : Measure (X × Y) :=
  completeSubcoupling μ ν (finiteMatchedCoupling μ ν E F)

/-- Both actual marginals and the quantitative unmatched-mass bound for the
explicit finite partition coupling. This constructs the measure itself. -/
theorem finitePartitionCoupling_spec {ι X Y : Type*} [Fintype ι]
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : ι → Set X} {F : ι → Set Y}
    (hE : ∀ i, MeasurableSet (E i)) (hF : ∀ i, MeasurableSet (F i))
    (hdE : Pairwise (fun i j ↦ Disjoint (E i) (E j))) (hdF : Pairwise (fun i j ↦ Disjoint (F i) (F j))) :
    IsProbabilityMeasure (finitePartitionCoupling μ ν E F) ∧
      (finitePartitionCoupling μ ν E F).fst = μ ∧
      (finitePartitionCoupling μ ν E F).snd = ν ∧
      ∀ B : Set (X × Y), (∀ i, Disjoint B (E i ×ˢ F i)) →
        finitePartitionCoupling μ ν E F B ≤ 1 - ∑ i, min (μ (E i)) (ν (F i)) := by
  have hfst := finiteMatchedCoupling_fst_le μ ν F hE hdE
  have hsnd := finiteMatchedCoupling_snd_le μ ν E hF hdF
  refine ⟨completeSubcoupling_isProbabilityMeasure μ ν _ hfst hsnd,
    completeSubcoupling_fst μ ν _ hfst hsnd,
    completeSubcoupling_snd μ ν _ hfst hsnd, ?_⟩
  intro B hB
  have hzero : finiteMatchedCoupling μ ν E F B = 0 := by
    apply Measure.sum_apply_eq_zero.mpr
    intro i
    apply le_zero_iff.mp
    exact (measure_mono ((Set.disjoint_left.mp (hB i)))).trans_eq
      (matchedCellCoupling_compl_prod_eq_zero μ ν (hE i) (hF i))
  exact (completeSubcoupling_bad_event_le μ ν _ hfst hsnd hzero).trans_eq
    (by rw [finiteMatchedCoupling_univ])

end BouRabeeGwynne
