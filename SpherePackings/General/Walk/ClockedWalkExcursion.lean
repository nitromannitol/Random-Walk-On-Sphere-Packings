module

-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/ClockedWalkExcursion.lean` at commit cf73d6e): its declarations that assume a
-- finite state space or a finite conductance network, for the chain of an arbitrary Markov
-- kernel on a measurable space.
public import BouRabeeGwynne.ClockedWalkExcursion
public import SpherePackings.General.MarkovChain.Absorbed
public import SpherePackings.General.Walk.DiscreteHarmonicMeasure
public import SpherePackings.General.Walk.SkeletonKernels
public import SpherePackings.General.Walk.WalkExcursionKernel

@[expose] public section

/-! General-state-space version of `BouRabeeGwynne.ClockedWalkExcursion`: the declarations of that file
that assume a finite state space or a finite conductance network. -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval BigOperators
namespace SpherePackings.MarkovChain

open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork BouRabeeGwynne.TrajectoryCoupling

variable {d : ℕ} {V : Type*} [MeasurableSpace V] [MeasurableEq V]
variable (κ : Kernel V V) [IsMarkovKernel κ]

lemma clockedWalkExcursionKernel_curve (pos : V → Euc d) (B : Set V)
    (hB : MeasurableSet B) (hpos : Measurable pos) (v : V) :
    (clockedWalkExcursionKernel κ pos hB v).map ClockedWalkExcursion.curve =
      walkExcursionKernel κ pos B hB hpos v := by
  rw [clockedWalkExcursionKernel_apply κ hpos hB v, walkExcursionKernel_apply κ pos B hB hpos v,
    Measure.map_map ClockedWalkExcursion.measurable_curve (measurable_ofWalk hpos hB)]
  congr 1
  funext ω
  exact ClockedWalkExcursion.curve_ofWalk pos B ω

lemma clockedWalkExcursionKernel_endPoint (pos : V → Euc d) (B : Set V)
    (hB : MeasurableSet B) (hpos : Measurable pos) (v : V) :
    (clockedWalkExcursionKernel κ pos hB v).map ClockedWalkExcursion.endPoint =
      (discreteHarmonicMeasure κ B hB v).map pos := by
  rw [clockedWalkExcursionKernel_apply κ hpos hB v]
  change ((law (absorbedKernel κ hB) v).map (ClockedWalkExcursion.ofWalk pos B)).map
    ClockedWalkExcursion.endPoint = ((law (absorbedKernel κ hB) v).map (exitVertex B)).map pos
  rw [Measure.map_map ClockedWalkExcursion.measurable_endPoint (measurable_ofWalk hpos hB),
    Measure.map_map hpos (measurable_exitVertex B hB)]
  congr 1
  funext ω
  exact ClockedWalkExcursion.endPoint_ofWalk pos B ω

end SpherePackings.MarkovChain
