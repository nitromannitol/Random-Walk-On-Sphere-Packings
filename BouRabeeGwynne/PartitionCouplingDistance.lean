-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/PartitionCouplingDistance.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.FinitePartitionCoupling
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# From the explicit spatial coupling to the actual law distance

A coupling concentrated near the diagonal bounds Lévy--Prokhorov distance.
Applying this to the constructed finite cell coupling uses only the actual cell
masses and diameters; no abstract coupling existence theorem is required.
-/

open MeasureTheory Metric Set
open scoped NNReal ENNReal
namespace BouRabeeGwynne

lemma levyProkhorovEDist_le_of_coupling {X : Type*} [PseudoEMetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ ν : Measure X) (ρ : Measure (X × X))
    (hfst : ρ.fst = μ) (hsnd : ρ.snd = ν) (r : ℝ≥0)
    (hbad : ρ {p | (r : ℝ≥0∞) ≤ edist p.1 p.2} ≤ r) :
    levyProkhorovEDist μ ν ≤ r := by
  apply sInf_le
  intro A hA
  have hleft : Prod.fst ⁻¹' A ⊆
      (Prod.snd ⁻¹' thickening (r : ℝ) A) ∪ {p : X × X | (r : ℝ≥0∞) ≤ edist p.1 p.2} := by
    intro p hp
    by_cases h : (r : ℝ≥0∞) ≤ edist p.1 p.2
    · exact Or.inr h
    · apply Or.inl
      apply (mem_thickening_iff_exists_edist_lt _ _).mpr
      refine ⟨p.1, hp, ?_⟩
      simpa only [edist_comm, ENNReal.ofReal_coe_nnreal] using (lt_of_not_ge h)
  have hright : Prod.snd ⁻¹' A ⊆
      (Prod.fst ⁻¹' thickening (r : ℝ) A) ∪ {p : X × X | (r : ℝ≥0∞) ≤ edist p.1 p.2} := by
    intro p hp
    by_cases h : (r : ℝ≥0∞) ≤ edist p.1 p.2
    · exact Or.inr h
    · apply Or.inl
      apply (mem_thickening_iff_exists_edist_lt _ _).mpr
      refine ⟨p.2, hp, ?_⟩
      simpa only [ENNReal.ofReal_coe_nnreal] using (lt_of_not_ge h)
  constructor
  · change μ A ≤ ν (thickening (r : ℝ) A) + (r : ℝ≥0∞)
    rw [← hfst, ← hsnd, Measure.fst_apply hA,
      Measure.snd_apply isOpen_thickening.measurableSet]
    exact (measure_mono hleft).trans ((measure_union_le _ _).trans (add_le_add le_rfl hbad))
  · change ν A ≤ μ (thickening (r : ℝ) A) + (r : ℝ≥0∞)
    rw [← hfst, ← hsnd, Measure.snd_apply hA,
      Measure.fst_apply isOpen_thickening.measurableSet]
    exact (measure_mono hright).trans ((measure_union_le _ _).trans (add_le_add le_rfl hbad))

/-- Finite matching directly controls the law distance whenever its paired
cells are spatially close and its actual unmatched probability is small. -/
theorem levyProkhorovEDist_le_of_finite_cells {ι X : Type*} [Fintype ι]
    [PseudoEMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E F : ι → Set X}
    (hE : ∀ i, MeasurableSet (E i)) (hF : ∀ i, MeasurableSet (F i))
    (hdE : Pairwise (fun i j ↦ Disjoint (E i) (E j))) (hdF : Pairwise (fun i j ↦ Disjoint (F i) (F j)))
    (r : ℝ≥0)
    (hclose : ∀ i, ∀ x ∈ E i, ∀ y ∈ F i, edist x y < (r : ℝ≥0∞))
    (hmass : 1 - ∑ i, min (μ (E i)) (ν (F i)) ≤ (r : ℝ≥0∞)) :
    levyProkhorovEDist μ ν ≤ r := by
  have hs := finitePartitionCoupling_spec μ ν hE hF hdE hdF
  apply levyProkhorovEDist_le_of_coupling μ ν (finitePartitionCoupling μ ν E F)
    hs.2.1 hs.2.2.1 r
  apply (hs.2.2.2 _ ?_).trans hmass
  intro i
  apply Set.disjoint_left.mpr
  intro p hp hcell
  exact (not_lt_of_ge hp) (hclose i p.1 hcell.1 p.2 hcell.2)

end BouRabeeGwynne
