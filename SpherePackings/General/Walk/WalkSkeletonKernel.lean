-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/WalkSkeletonKernel.lean` at commit cf73d6e): its declarations that assume a
-- finite state space or a finite conductance network, for the chain of an arbitrary Markov
-- kernel on a measurable space.
import BouRabeeGwynne.WalkSkeletonKernel
import SpherePackings.General.MarkovChain.Absorbed
import SpherePackings.General.Walk.ExcursionEndpointExtension
import SpherePackings.General.Walk.SkeletonKernels

/-! General-state-space version of `BouRabeeGwynne.WalkSkeletonKernel`: the declarations of that file
that assume a finite state space or a finite conductance network. -/

open MeasureTheory ProbabilityTheory Set
namespace SpherePackings.MarkovChain

open BouRabeeGwynne
variable {d : ℕ} {V J : Type*} [MeasurableSpace V] [MeasurableEq V]
variable (κ : Kernel V V) [IsMarkovKernel κ]

noncomputable def spatialClockedExcursionKernel (pos : V → Euc d)
    (hpos : MeasurableEmbedding pos) (B : Set V)
    (hB : MeasurableSet B) : Kernel (Euc d) (ClockedWalkExcursion d) :=
  finiteVertexKernelExtension pos hpos (clockedWalkExcursionKernel κ pos hB)
    ClockedWalkExcursion.constant ClockedWalkExcursion.measurable_constant

instance spatialClockedExcursionKernel_isMarkov (pos : V → Euc d)
    (hpos : MeasurableEmbedding pos) (B : Set V)
    (hB : MeasurableSet B) :
    IsMarkovKernel (spatialClockedExcursionKernel κ pos hpos B hB) := by
  unfold spatialClockedExcursionKernel
  have := clockedWalkExcursionKernel_isMarkov κ hpos.measurable hB
  infer_instance

omit [MeasurableEq V] in
@[simp] lemma spatialClockedExcursionKernel_vertex (pos : V → Euc d)
    (hpos : MeasurableEmbedding pos) (B : Set V)
    (hB : MeasurableSet B) (v : V) :
    spatialClockedExcursionKernel κ pos hpos B hB (pos v) =
      clockedWalkExcursionKernel κ pos hB v :=
  finiteVertexKernelExtension_apply_vertex pos hpos _ _ _ v

lemma spatialClockedExcursionKernel_ae_start (pos : V → Euc d)
    (hpos : MeasurableEmbedding pos) (B : Set V)
    (hB : MeasurableSet B) (z : Euc d) :
    ∀ᵐ e ∂spatialClockedExcursionKernel κ pos hpos B hB z,
      ClockedWalkExcursion.start e = z := by
  by_cases hz : z ∈ Set.range pos
  · obtain ⟨v, rfl⟩ := hz
    rw [spatialClockedExcursionKernel_vertex κ]
    exact clockedWalkExcursionKernel_ae_start κ hpos.measurable hB v
  · change ∀ᵐ e ∂finiteVertexKernelExtension pos hpos
      (clockedWalkExcursionKernel κ pos hB) ClockedWalkExcursion.constant
      ClockedWalkExcursion.measurable_constant z, _
    rw [finiteVertexKernelExtension_apply_off_graph pos hpos _ _ _ hz]
    exact (ae_dirac_iff (measurableSet_eq_fun ClockedWalkExcursion.measurable_start
      measurable_const)).mpr rfl

variable [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
noncomputable def walkSkeletonHistoryKernel (pos : V → Euc d)
    (hpos : MeasurableEmbedding pos) (B : J → Set V)
    (hB : ∀ j, MeasurableSet (B j))
    (select : ℕ → Euc d → Option J) (hs : ∀ n, Measurable (select n)) (n : ℕ) :
    Kernel (Finset.Iic n → Bool × ClockedWalkExcursion d) (Bool × ClockedWalkExcursion d) :=
  (absorbingExcursionKernel (fun j => spatialClockedExcursionKernel κ pos hpos (B j) (hB j))
    ClockedWalkExcursion.endPoint ClockedWalkExcursion.measurable_endPoint
    ClockedWalkExcursion.constant ClockedWalkExcursion.measurable_constant
    (select n) (hs n)).comap (fun h => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _)

instance walkSkeletonHistoryKernel_isMarkov (pos : V → Euc d)
    (hpos : MeasurableEmbedding pos) (B : J → Set V)
    (hB : ∀ j, MeasurableSet (B j))
    (select : ℕ → Euc d → Option J) (hs : ∀ n, Measurable (select n)) (n : ℕ) :
    IsMarkovKernel (walkSkeletonHistoryKernel κ pos hpos B hB select hs n) := by
  unfold walkSkeletonHistoryKernel
  infer_instance

end SpherePackings.MarkovChain
