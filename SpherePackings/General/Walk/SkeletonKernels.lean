-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (files `BouRabeeGwynne/ClockedWalkExcursion.lean`, `ExcursionEndpointExtension.lean` and
-- `WalkSkeletonKernel.lean` at commit cf73d6e): the excursion and skeleton kernels of the walk of a
-- finite conductance network, for the chain of an arbitrary Markov kernel whose state space embeds
-- measurably in `ℝ^d`.
import SpherePackings.General.Walk.StoppedCurveMeasurable
import BouRabeeGwynne.WalkSkeletonKernel

/-!
# Excursion and skeleton kernels of a Markov chain

For a Markov kernel `κ` on `V`, a position map `pos : V → ℝ^d` that is a measurable embedding,
and a measurable set `B`, the clocked excursion kernel gives the law of the chain absorbed outside
`B`, recorded up to its exit with its integer duration.  It is extended to all spatial starting
points by constant excursions off the embedded vertex set, and the skeleton history kernels run
these excursions in balls chosen by a selector.  Nothing here depends on the paper.
-/

open MeasureTheory ProbabilityTheory Set
open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork

namespace SpherePackings.MarkovChain

variable {d : ℕ} {V J : Type*} [MeasurableSpace V] [MeasurableSingletonClass V]

omit [MeasurableSingletonClass V] in
/-- The excursion recorded up to the first exit from `B` is a measurable function of the path. -/
lemma measurable_ofWalk {pos : V → Euc d} (hpos : Measurable pos) {B : Set V}
    (hB : MeasurableSet B) : Measurable (ClockedWalkExcursion.ofWalk pos B) := by
  have hm : Measurable (fun p : ℕ × (ℕ → V) => (p.1, fun k => pos (p.2 k))) :=
    measurable_fst.prodMk (Measurable.of_eval fun k =>
      hpos.comp ((measurable_pi_apply k).comp measurable_snd))
  exact hm.comp (FiniteConductanceNetwork.measurable_observedHistory
    (exitTime_isStoppingTime' hB).measurable')

variable (κ : Kernel V V) [IsMarkovKernel κ]

/-- The clocked excursion kernel: the chain absorbed outside `B`, from `v`, recorded up to its
exit. -/
noncomputable def clockedWalkExcursionKernel (pos : V → Euc d)
    {B : Set V} (hB : MeasurableSet B) : Kernel V (ClockedWalkExcursion d) :=
  (pathKernel (absorbedKernel κ hB)).map (ClockedWalkExcursion.ofWalk pos B)

omit [MeasurableSingletonClass V] in
lemma clockedWalkExcursionKernel_apply {pos : V → Euc d} (hpos : Measurable pos)
    {B : Set V} (hB : MeasurableSet B) (v : V) :
    clockedWalkExcursionKernel κ pos hB v =
      (law (absorbedKernel κ hB) v).map (ClockedWalkExcursion.ofWalk pos B) := by
  rw [clockedWalkExcursionKernel, Kernel.map_apply _ (measurable_ofWalk hpos hB), pathKernel_apply]

omit [MeasurableSingletonClass V] in
lemma clockedWalkExcursionKernel_isMarkov {pos : V → Euc d} (hpos : Measurable pos)
    {B : Set V} (hB : MeasurableSet B) : IsMarkovKernel (clockedWalkExcursionKernel κ pos hB) := by
  unfold clockedWalkExcursionKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_ofWalk hpos hB)

lemma clockedWalkExcursionKernel_ae_start {pos : V → Euc d} (hpos : Measurable pos)
    {B : Set V} (hB : MeasurableSet B) (v : V) :
    ∀ᵐ e ∂clockedWalkExcursionKernel κ pos hB v, ClockedWalkExcursion.start e = pos v := by
  rw [clockedWalkExcursionKernel_apply κ hpos hB]
  apply (ae_map_iff (measurable_ofWalk hpos hB).aemeasurable
    (measurableSet_eq_fun ClockedWalkExcursion.measurable_start measurable_const)).mpr
  filter_upwards [law_ae_start (absorbedKernel κ hB) v] with ω hω
  simp [ClockedWalkExcursion.start_ofWalk, hω]

end SpherePackings.MarkovChain
