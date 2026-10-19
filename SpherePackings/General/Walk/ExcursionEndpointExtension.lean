-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/ExcursionEndpointExtension.lean` at commit cf73d6e): its declarations that assume a
-- finite state space or a finite conductance network, for the chain of an arbitrary Markov
-- kernel on a measurable space.
import BouRabeeGwynne.ExcursionEndpointExtension
import SpherePackings.General.MarkovChain.Absorbed
import SpherePackings.General.Walk.WalkExcursionKernel

/-! General-state-space version of `BouRabeeGwynne.ExcursionEndpointExtension`: the declarations of that file
that assume a finite state space or a finite conductance network. -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval
namespace SpherePackings.MarkovChain

open BouRabeeGwynne
variable {d : ℕ} {V : Type*} [MeasurableSpace V]

lemma measurableEmbedding_finite_positions (pos : V → Euc d)
    (hpos : Function.Injective pos) (hmeas : Measurable pos)
    (himage : ∀ ⦃s : Set V⦄, MeasurableSet s → MeasurableSet (pos '' s)) :
    MeasurableEmbedding pos where
  injective := hpos
  measurable := hmeas
  measurableSet_image' := himage

/-- Measurable extension retaining the whole supplied excursion state. In
particular the state may include a discrete duration and all visited vertices. -/
noncomputable def finiteVertexKernelExtension {S : Type*} [MeasurableSpace S]
    (pos : V → Euc d) (hpos : MeasurableEmbedding pos) (κ : Kernel V S)
    (constantState : Euc d → S) (hconstant : Measurable constantState) : Kernel (Euc d) S where
  toFun := Function.extend pos κ (fun z => Measure.dirac (constantState z))
  measurable' := hpos.measurable_extend
    κ.measurable (Measure.measurable_dirac.comp hconstant)

@[simp] lemma finiteVertexKernelExtension_apply_vertex {S : Type*} [MeasurableSpace S]
    (pos : V → Euc d) (hpos : MeasurableEmbedding pos) (κ : Kernel V S)
    (constantState : Euc d → S) (hconstant : Measurable constantState) (v : V) :
    finiteVertexKernelExtension pos hpos κ constantState hconstant (pos v) = κ v := by
  change Function.extend pos (fun w => κ w)
    (fun z => Measure.dirac (constantState z)) (pos v) = κ v
  exact hpos.injective.extend_apply (fun w => κ w) (fun z => Measure.dirac (constantState z)) v

lemma finiteVertexKernelExtension_apply_off_graph {S : Type*} [MeasurableSpace S]
    (pos : V → Euc d) (hpos : MeasurableEmbedding pos) (κ : Kernel V S)
    (constantState : Euc d → S) (hconstant : Measurable constantState)
    {z : Euc d} (hz : z ∉ Set.range pos) :
    finiteVertexKernelExtension pos hpos κ constantState hconstant z =
      Measure.dirac (constantState z) := by
  change Function.extend pos (fun w => κ w)
    (fun y => Measure.dirac (constantState y)) z = Measure.dirac (constantState z)
  exact Function.extend_apply' (f := pos) (fun w => κ w)
    (fun y => Measure.dirac (constantState y)) z hz

noncomputable instance finiteVertexKernelExtension_isMarkov {S : Type*} [MeasurableSpace S]
    (pos : V → Euc d) (hpos : MeasurableEmbedding pos) (κ : Kernel V S)
    [IsMarkovKernel κ] (constantState : Euc d → S) (hconstant : Measurable constantState) :
    IsMarkovKernel (finiteVertexKernelExtension pos hpos κ constantState hconstant) where
  isProbabilityMeasure z := by
    by_cases hz : z ∈ Set.range pos
    · obtain ⟨v, rfl⟩ := hz
      rw [finiteVertexKernelExtension_apply_vertex]
      infer_instance
    · rw [finiteVertexKernelExtension_apply_off_graph pos hpos κ constantState hconstant hz]
      infer_instance

noncomputable def vertexExcursionExtension (pos : V → Euc d)
    (hpos : MeasurableEmbedding pos) (κ : Kernel V C(unitInterval, Euc d)) :
    Kernel (Euc d) C(unitInterval, Euc d) :=
  finiteVertexKernelExtension pos hpos κ (ContinuousMap.const unitInterval)
    measurable_constantExcursion

@[simp] lemma vertexExcursionExtension_apply_vertex (pos : V → Euc d)
    (hpos : MeasurableEmbedding pos) (κ : Kernel V C(unitInterval, Euc d)) (v : V) :
    vertexExcursionExtension pos hpos κ (pos v) = κ v :=
  finiteVertexKernelExtension_apply_vertex pos hpos κ (ContinuousMap.const unitInterval)
    measurable_constantExcursion v

lemma vertexExcursionExtension_apply_off_graph (pos : V → Euc d)
    (hpos : MeasurableEmbedding pos) (κ : Kernel V C(unitInterval, Euc d))
    {z : Euc d} (hz : z ∉ Set.range pos) :
    vertexExcursionExtension pos hpos κ z =
      Measure.dirac (ContinuousMap.const unitInterval z) :=
  finiteVertexKernelExtension_apply_off_graph pos hpos κ (ContinuousMap.const unitInterval)
    measurable_constantExcursion hz

noncomputable instance vertexExcursionExtension_isMarkov (pos : V → Euc d)
    (hpos : MeasurableEmbedding pos) (κ : Kernel V C(unitInterval, Euc d))
    [IsMarkovKernel κ] : IsMarkovKernel (vertexExcursionExtension pos hpos κ) where
  isProbabilityMeasure z := by
    by_cases hz : z ∈ Set.range pos
    · obtain ⟨v, rfl⟩ := hz
      rw [vertexExcursionExtension_apply_vertex]
      infer_instance
    · rw [vertexExcursionExtension_apply_off_graph pos hpos κ hz]
      infer_instance

lemma vertexExcursionExtension_ae_start (pos : V → Euc d)
    (hpos : MeasurableEmbedding pos) (κ : Kernel V C(unitInterval, Euc d))
    (hstart : ∀ v, ∀ᵐ c ∂κ v, c 0 = pos v) (z : Euc d) :
    ∀ᵐ c ∂vertexExcursionExtension pos hpos κ z, c 0 = z := by
  by_cases hz : z ∈ Set.range pos
  · obtain ⟨v, rfl⟩ := hz
    rw [vertexExcursionExtension_apply_vertex]
    exact hstart v
  · rw [vertexExcursionExtension_apply_off_graph pos hpos κ hz]
    simp

/-- The next excursion starts at the previous curve's exact endpoint,
including for supplied histories that are not genuine graph paths. -/
noncomputable def nextVertexExcursionKernel (pos : V → Euc d)
    (hpos : MeasurableEmbedding pos) (κ : Kernel V C(unitInterval, Euc d)) :
    Kernel C(unitInterval, Euc d) C(unitInterval, Euc d) :=
  (vertexExcursionExtension pos hpos κ).comap (fun c => c 1)
    (ContinuousMap.measurable_eval 1)

noncomputable instance nextVertexExcursionKernel_isMarkov (pos : V → Euc d)
    (hpos : MeasurableEmbedding pos) (κ : Kernel V C(unitInterval, Euc d))
    [IsMarkovKernel κ] : IsMarkovKernel (nextVertexExcursionKernel pos hpos κ) := by
  unfold nextVertexExcursionKernel
  infer_instance

lemma nextVertexExcursionKernel_ae_start (pos : V → Euc d)
    (hpos : MeasurableEmbedding pos) (κ : Kernel V C(unitInterval, Euc d))
    (hstart : ∀ v, ∀ᵐ c ∂κ v, c 0 = pos v) (c : C(unitInterval, Euc d)) :
    ∀ᵐ e ∂nextVertexExcursionKernel pos hpos κ c, e 0 = c 1 :=
  vertexExcursionExtension_ae_start pos hpos κ hstart (c 1)

lemma extended_walkExcursionKernel_ae_start [MeasurableEq V] (κ : Kernel V V) [IsMarkovKernel κ]
    (pos : V → Euc d) (hinj : MeasurableEmbedding pos) (A : Set V)
    (hA : MeasurableSet A) (z : Euc d) :
    ∀ᵐ c ∂vertexExcursionExtension pos hinj (walkExcursionKernel κ pos A hA hinj.measurable) z,
      c 0 = z :=
  vertexExcursionExtension_ae_start pos hinj _
    (walkExcursionKernel_ae_start κ pos A hA hinj.measurable) z

end SpherePackings.MarkovChain
