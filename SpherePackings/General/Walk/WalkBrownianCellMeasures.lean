-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/WalkBrownianCellMeasures.lean` at commit cf73d6e): its declarations that assume a
-- finite state space or a finite conductance network, for the chain of an arbitrary Markov
-- kernel on a measurable space.
import BouRabeeGwynne.WalkBrownianCellMeasures
import SpherePackings.General.MarkovChain.Absorbed
import SpherePackings.General.Walk.ClockedWalkExcursion
import SpherePackings.General.Walk.DiscreteHarmonicMeasure
import SpherePackings.General.Walk.SkeletonKernels

/-! General-state-space version of `BouRabeeGwynne.WalkBrownianCellMeasures`: the declarations of that file
that assume a finite state space or a finite conductance network. -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval ENNReal
namespace SpherePackings.MarkovChain

open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork BouRabeeGwynne.TrajectoryCoupling
variable {d : ℕ}
variable {V : Type*}  [MeasurableSpace V] [MeasurableEq V]
variable (κ : Kernel V V) [IsMarkovKernel κ]

omit [MeasurableEq V] in
/-- The walk endpoint cell of a measurable set is measurable. The range of the position map is
measurable because `pos` is a measurable embedding, which replaces the finiteness of `V`. -/
lemma measurableSet_walkEndpointCell (pos : V → Euc d) (hpos : MeasurableEmbedding pos)
    {E : Set (Euc d)} (hE : MeasurableSet E) : MeasurableSet (walkEndpointCell pos E) :=
  measurableSet_activeEndpointCell _ ClockedWalkExcursion.measurable_endPoint
    (hE.inter hpos.measurableSet_range)

lemma walkEndpointCell_mass (pos : V → Euc d) (hpos : MeasurableEmbedding pos) (B : Set V)
    (hB : MeasurableSet B) (v : V)
    {E : Set (Euc d)} (hE : MeasurableSet E) :
    ((clockedWalkExcursionKernel κ pos hB v).map (fun e => (false, e)))
        (walkEndpointCell pos E) = ((discreteHarmonicMeasure κ B hB v).map pos) E := by
  change ((clockedWalkExcursionKernel κ pos hB v).map (fun e => (false, e)))
    (activeEndpointCell ClockedWalkExcursion.endPoint (E ∩ Set.range pos)) = _
  rw [activeEndpointCell_map_false _ ClockedWalkExcursion.measurable_endPoint _
      (hE.inter hpos.measurableSet_range),
    clockedWalkExcursionKernel_endPoint κ pos B hB hpos.measurable,
    Measure.map_apply hpos.measurable (hE.inter hpos.measurableSet_range),
    Measure.map_apply hpos.measurable hE]
  congr 1
  ext w
  simp only [Set.mem_preimage, Set.mem_inter_iff]
  exact and_iff_left ⟨w, rfl⟩

/-- The actual full-excursion coupling has small bad mass whenever the actual
spatial exit measures have small cell errors. The Brownian support is derived
from its genuine stopped path, including the exit endpoint. -/
theorem finite_walkBrownian_excursion_bad_le (hd : 1 ≤ d)
    (pos : V → Euc d) (hpos : MeasurableEmbedding pos) (B : Set V) (hB : MeasurableSet B)
    (v : V) {U : Set (Euc d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ] (hμ : IsStandardBrownianLaw μ)
    {z : Euc d} (hz : z ∈ U) {m : ℕ} (E : Fin m → Set (Euc d))
    (hE : ∀ i, MeasurableSet (E i)) (hdE : Pairwise (fun i j => Disjoint (E i) (E j)))
    (hcover : closure U ⊆ ⋃ i, E i) {b : ℝ} (hb : 0 ≤ b)
    (herror : ∀ i, |(((discreteHarmonicMeasure κ B hB v).map pos) (E i)).toReal -
      (((stoppedBrownianLaw U z μ).map CurveSpace.endPoint) (E i)).toReal| ≤ b / (m + 1))
    (Bad : Set ((Bool × ClockedWalkExcursion d) × (Bool × C(unitInterval, Euc d))))
    (hBad : ∀ i, Disjoint Bad (walkEndpointCell pos (E i) ×ˢ
      activeEndpointCell (fun c : C(unitInterval, Euc d) => c 1) (E i))) :
    finitePartitionCoupling
      ((clockedWalkExcursionKernel κ pos hB v).map (fun e => (false, e)))
      ((brownianExcursionKernel hU μ z).map (fun c => (false, c)))
      (fun i => walkEndpointCell pos (E i))
      (fun i => activeEndpointCell (fun c : C(unitInterval, Euc d) => c 1) (E i)) Bad ≤
        ENNReal.ofReal b := by
  have := clockedWalkExcursionKernel_isMarkov κ hpos.measurable hB
  have : IsProbabilityMeasure
      ((clockedWalkExcursionKernel κ pos hB v).map (fun e => (false, e))) :=
    (Measure.isProbabilityMeasure_map_iff
      (measurable_const.prodMk measurable_id).aemeasurable).mpr inferInstance
  have : IsProbabilityMeasure
      ((brownianExcursionKernel hU μ z).map (fun c => (false, c))) :=
    (Measure.isProbabilityMeasure_map_iff
      (measurable_const.prodMk measurable_id).aemeasurable).mpr inferInstance
  have herr : ∀ i : Fin m,
      |(((clockedWalkExcursionKernel κ pos hB v).map (fun e => (false, e)))
          (walkEndpointCell pos (E i))).toReal -
        (((brownianExcursionKernel hU μ z).map (fun c => (false, c)))
          (activeEndpointCell (fun c : C(unitInterval, Euc d) => c 1) (E i))).toReal| ≤
            b / (m + 1) := by
    intro i
    rw [walkEndpointCell_mass κ pos hpos B hB v (hE i),
      brownian_activeEndpointCell_mass hU μ z (hE i)]
    exact herror i
  apply (finitePartitionCoupling_bad_le_of_cell_error _ _
    (fun i => measurableSet_walkEndpointCell pos hpos (hE i))
    (fun i => measurableSet_activeEndpointCell _ (ContinuousMap.measurable_eval 1) (hE i))
    (pairwiseDisjoint_walkEndpointCell pos hdE)
    (pairwiseDisjoint_activeEndpointCell _ hdE)
    (brownian_activeEndpointCells_cover hd hU hUb μ hμ hz E hE hcover)
    (div_nonneg hb (by positivity)) herr Bad hBad).trans
      (ENNReal.ofReal_le_ofReal ?_)
  simp only [Fintype.card_fin]
  change (m : ℝ) * (b / (m + 1)) ≤ b
  have hm : (0 : ℝ) < m + 1 := by positivity
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hm).mpr
  nlinarith

end SpherePackings.MarkovChain
