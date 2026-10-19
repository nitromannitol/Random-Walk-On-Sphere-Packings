-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/FinitePartitionCouplingKernel.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.FinitePartitionCoupling
import Mathlib.Probability.Kernel.Composition.Prod

/-!
# The explicit finite-cell coupling is a measurable kernel

The source laws may be laws of entire stopped excursions. Thus using endpoint
preimages as cells couples genuine paths while preserving their full laws.
All parameter dependence is proved measurable here, rather than inferred from
pointwise existence of a coupling.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace BouRabeeGwynne

variable {S X Y ι : Type*} [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace Y]

private noncomputable def weightedKernel (κ : Kernel S X) (c : S → ℝ≥0∞)
    (hc : Measurable c) : Kernel S X where
  toFun a := c a • κ a
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    simp only [Measure.smul_apply, smul_eq_mul]
    exact hc.mul (κ.measurable_coe hA)

private noncomputable def cappedCellKernel (κ : Kernel S X) (ν : Kernel S Y)
    {E : Set X} {F : Set Y} (hE : MeasurableSet E) (hF : MeasurableSet F) : Kernel S X :=
  weightedKernel (κ.restrict hE) (fun a ↦ min (κ a E) (ν a F) / κ a E)
    (((κ.measurable_coe hE).min (ν.measurable_coe hF)).div (κ.measurable_coe hE))

private lemma cappedCellKernel_apply (κ : Kernel S X) (ν : Kernel S Y)
    {E : Set X} {F : Set Y} (hE : MeasurableSet E) (hF : MeasurableSet F) (a : S) :
    cappedCellKernel κ ν hE hF a = cappedRestrict (κ a) E (min (κ a E) (ν a F)) := rfl

private instance cappedCellKernel_isFinite (κ : Kernel S X) (ν : Kernel S Y)
    [IsFiniteKernel κ] {E : Set X} {F : Set Y}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    IsFiniteKernel (cappedCellKernel κ ν hE hF) := by
  apply isFiniteKernel_of_le (ν := κ)
  intro a A
  exact (cappedRestrict_le (κ a) E (min_le_left _ _) A).trans (Measure.restrict_le_self A)

private noncomputable def balancedProductKernel (κ : Kernel S X) (ν : Kernel S Y)
    [IsFiniteKernel κ] [IsFiniteKernel ν] : Kernel S (X × Y) :=
  weightedKernel (κ ×ₖ ν) (fun a ↦ (κ a univ)⁻¹)
    (κ.measurable_coe MeasurableSet.univ).inv

private lemma balancedProductKernel_apply (κ : Kernel S X) (ν : Kernel S Y)
    [IsFiniteKernel κ] [IsFiniteKernel ν] (a : S) :
    balancedProductKernel κ ν a = balancedProduct (κ a) (ν a) := by
  change (κ a univ)⁻¹ • (κ ×ₖ ν) a = _
  rw [Kernel.prod_apply]
  rfl

private noncomputable def matchedCellKernel (κ : Kernel S X) (ν : Kernel S Y)
    [IsFiniteKernel κ] [IsFiniteKernel ν]
    {E : Set X} {F : Set Y} (hE : MeasurableSet E) (hF : MeasurableSet F) : Kernel S (X × Y) :=
  balancedProductKernel (cappedCellKernel κ ν hE hF) (cappedCellKernel ν κ hF hE)

private lemma matchedCellKernel_apply (κ : Kernel S X) (ν : Kernel S Y)
    [IsFiniteKernel κ] [IsFiniteKernel ν]
    {E : Set X} {F : Set Y} (hE : MeasurableSet E) (hF : MeasurableSet F) (a : S) :
    matchedCellKernel κ ν hE hF a = matchedCellCoupling (κ a) (ν a) E F := by
  rw [matchedCellKernel, balancedProductKernel_apply, cappedCellKernel_apply,
    cappedCellKernel_apply]
  simp only [matchedCellCoupling, min_comm (ν a F) (κ a E)]

private noncomputable def finiteMatchedKernel [Fintype ι]
    (κ : Kernel S X) (ν : Kernel S Y) [IsFiniteKernel κ] [IsFiniteKernel ν]
    {E : ι → Set X} {F : ι → Set Y}
    (hE : ∀ i, MeasurableSet (E i)) (hF : ∀ i, MeasurableSet (F i)) : Kernel S (X × Y) :=
  Kernel.sum (fun i ↦ matchedCellKernel κ ν (hE i) (hF i))

private lemma finiteMatchedKernel_apply [Fintype ι]
    (κ : Kernel S X) (ν : Kernel S Y) [IsFiniteKernel κ] [IsFiniteKernel ν]
    {E : ι → Set X} {F : ι → Set Y}
    (hE : ∀ i, MeasurableSet (E i)) (hF : ∀ i, MeasurableSet (F i)) (a : S) :
    finiteMatchedKernel κ ν hE hF a = finiteMatchedCoupling (κ a) (ν a) E F := by
  simp only [finiteMatchedKernel, Kernel.sum_apply, matchedCellKernel_apply, finiteMatchedCoupling]

private instance finiteMatchedKernel_isFinite [Fintype ι]
    (κ : Kernel S X) (ν : Kernel S Y) [IsMarkovKernel κ] [IsMarkovKernel ν]
    {E : ι → Set X} {F : ι → Set Y}
    (hE : ∀ i, MeasurableSet (E i)) (hF : ∀ i, MeasurableSet (F i)) :
    IsFiniteKernel (finiteMatchedKernel κ ν hE hF) := by
  refine ⟨⟨Fintype.card ι, ENNReal.natCast_lt_top _, fun a ↦ ?_⟩⟩
  rw [finiteMatchedKernel_apply, finiteMatchedCoupling_univ]
  calc
    ∑ i, min (κ a (E i)) (ν a (F i)) ≤ ∑ _i : ι, (1 : ℝ≥0∞) :=
      Finset.sum_le_sum (fun i hi ↦ (min_le_left _ _).trans prob_le_one)
    _ = _ := by simp

private noncomputable def residualKernel (κ η : Kernel S X) [IsFiniteKernel η]
    (hle : ∀ a, η a ≤ κ a) : Kernel S X where
  toFun a := κ a - η a
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    simp only [Measure.sub_apply hA (hle _)]
    exact (κ.measurable_coe hA).sub (η.measurable_coe hA)

private instance residualKernel_isFinite (κ η : Kernel S X)
    [IsFiniteKernel κ] [IsFiniteKernel η] (hle : ∀ a, η a ≤ κ a) :
    IsFiniteKernel (residualKernel κ η hle) := by
  apply isFiniteKernel_of_le (ν := κ)
  intro a A
  exact Measure.sub_le A

/-- A genuine measurable coupling kernel, constructed by matching each cell's
common mass and taking the normalized product of the two residual laws. -/
noncomputable def finitePartitionCouplingKernel [Fintype ι]
    (κ : Kernel S X) (ν : Kernel S Y) [IsMarkovKernel κ] [IsMarkovKernel ν]
    {E : ι → Set X} {F : ι → Set Y}
    (hE : ∀ i, MeasurableSet (E i)) (hF : ∀ i, MeasurableSet (F i))
    (hdE : Pairwise (fun i j ↦ Disjoint (E i) (E j)))
    (hdF : Pairwise (fun i j ↦ Disjoint (F i) (F j))) : Kernel S (X × Y) := by
  let ρ := finiteMatchedKernel κ ν hE hF
  have hfst (a : S) : ρ.fst a ≤ κ a := by
    change (ρ a).fst ≤ κ a
    rw [finiteMatchedKernel_apply]
    exact finiteMatchedCoupling_fst_le (κ a) (ν a) F hE hdE
  have hsnd (a : S) : ρ.snd a ≤ ν a := by
    change (ρ a).snd ≤ ν a
    rw [finiteMatchedKernel_apply]
    exact finiteMatchedCoupling_snd_le (κ a) (ν a) E hF hdF
  exact ρ + balancedProductKernel (residualKernel κ ρ.fst hfst)
    (residualKernel ν ρ.snd hsnd)

lemma finitePartitionCouplingKernel_apply [Fintype ι]
    (κ : Kernel S X) (ν : Kernel S Y) [IsMarkovKernel κ] [IsMarkovKernel ν]
    {E : ι → Set X} {F : ι → Set Y}
    (hE : ∀ i, MeasurableSet (E i)) (hF : ∀ i, MeasurableSet (F i))
    (hdE : Pairwise (fun i j ↦ Disjoint (E i) (E j)))
    (hdF : Pairwise (fun i j ↦ Disjoint (F i) (F j))) (a : S) :
    finitePartitionCouplingKernel κ ν hE hF hdE hdF a =
      finitePartitionCoupling (κ a) (ν a) E F := by
  simp only [finitePartitionCouplingKernel, Kernel.add_apply, balancedProductKernel_apply,
    residualKernel, Kernel.coe_mk, Kernel.fst_apply, Kernel.snd_apply,
    finiteMatchedKernel_apply, finitePartitionCoupling, completeSubcoupling,
    Measure.fst, Measure.snd]

instance finitePartitionCouplingKernel_isMarkov [Fintype ι]
    (κ : Kernel S X) (ν : Kernel S Y) [IsMarkovKernel κ] [IsMarkovKernel ν]
    {E : ι → Set X} {F : ι → Set Y}
    (hE : ∀ i, MeasurableSet (E i)) (hF : ∀ i, MeasurableSet (F i))
    (hdE : Pairwise (fun i j ↦ Disjoint (E i) (E j)))
    (hdF : Pairwise (fun i j ↦ Disjoint (F i) (F j))) :
    IsMarkovKernel (finitePartitionCouplingKernel κ ν hE hF hdE hdF) where
  isProbabilityMeasure a := by
    rw [finitePartitionCouplingKernel_apply]
    exact (finitePartitionCoupling_spec (κ a) (ν a) hE hF hdE hdF).1

/-- Exact full-law marginals and the quantitative failure bound. -/
theorem finitePartitionCouplingKernel_spec [Fintype ι]
    (κ : Kernel S X) (ν : Kernel S Y) [IsMarkovKernel κ] [IsMarkovKernel ν]
    {E : ι → Set X} {F : ι → Set Y}
    (hE : ∀ i, MeasurableSet (E i)) (hF : ∀ i, MeasurableSet (F i))
    (hdE : Pairwise (fun i j ↦ Disjoint (E i) (E j)))
    (hdF : Pairwise (fun i j ↦ Disjoint (F i) (F j))) (a : S) :
    (finitePartitionCouplingKernel κ ν hE hF hdE hdF a).fst = κ a ∧
    (finitePartitionCouplingKernel κ ν hE hF hdE hdF a).snd = ν a ∧
    ∀ B : Set (X × Y), (∀ i, Disjoint B (E i ×ˢ F i)) →
      finitePartitionCouplingKernel κ ν hE hF hdE hdF a B ≤
        1 - ∑ i, min (κ a (E i)) (ν a (F i)) := by
  rw [finitePartitionCouplingKernel_apply]
  exact (finitePartitionCoupling_spec (κ a) (ν a) hE hF hdE hdF).2

end BouRabeeGwynne
