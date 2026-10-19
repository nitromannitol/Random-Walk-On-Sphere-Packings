-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/WalkBrownianCoupling.lean` at commit cf73d6e): its declarations that assume a
-- finite state space or a finite conductance network, for the chain of an arbitrary Markov
-- kernel on a measurable space.
import BouRabeeGwynne.WalkBrownianCoupling
import SpherePackings.General.MarkovChain.Absorbed
import SpherePackings.General.Walk.WalkBrownianCellMeasures
import SpherePackings.General.Walk.WalkSkeletonKernel
import SpherePackings.General.Walk.WalkSkeletonLaw

/-! General-state-space version of `BouRabeeGwynne.WalkBrownianCoupling`: the declarations of that file
that assume a finite state space or a finite conductance network. -/

set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Preorder
open scoped unitInterval ENNReal
namespace SpherePackings.MarkovChain

open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork BouRabeeGwynne.TrajectoryCoupling
variable {d : ℕ}
variable {V J : Type*} [MeasurableSpace V] [MeasurableEq V] [Countable J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
variable (κ : Kernel V V) [IsMarkovKernel κ]
  (pos : V → Euc d) (hpos : MeasurableEmbedding pos) (B : J → Set V)
  (hB : ∀ j, MeasurableSet (B j))
  (U : J → Set (Euc d)) (hU : ∀ j, IsOpen (U j))
  (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ]
  (select : ℕ → Euc d → Option J) (hs : ∀ n, Measurable (select n))
  (m : ℕ → ℕ) (E : ∀ n, Fin (m n) → Set (Euc d))
  (hE : ∀ n i, MeasurableSet (E n i))
  (hdE : ∀ n, Pairwise (fun i j => Disjoint (E n i) (E n j)))

noncomputable def walkBrownianCouplingKernel (n : ℕ) :
    Kernel (Finset.Iic n → (Bool × ClockedWalkExcursion d) ×
      (Bool × C(unitInterval, Euc d)))
      ((Bool × ClockedWalkExcursion d) × (Bool × C(unitInterval, Euc d))) :=
  finitePartitionCouplingKernel
    ((walkSkeletonHistoryKernel κ pos hpos B hB select hs n).comap
      (TrajectoryCoupling.prefixMap Prod.fst n)
      (TrajectoryCoupling.measurable_prefixMap measurable_fst n))
    ((brownianSkeletonKernel U hU μ (brownianSelectorForWalk select)
      (fun n => hs (n - 1)) n).comap
      (TrajectoryCoupling.prefixMap Prod.snd n)
      (TrajectoryCoupling.measurable_prefixMap measurable_snd n))
    (fun i => measurableSet_walkEndpointCell pos hpos (hE (n + 1) i))
    (fun i => measurableSet_activeEndpointCell (fun c : C(unitInterval, Euc d) => c 1)
      (ContinuousMap.measurable_eval 1) (hE (n + 1) i))
    (pairwiseDisjoint_walkEndpointCell pos (hdE (n + 1)))
    (pairwiseDisjoint_activeEndpointCell _ (hdE (n + 1)))

instance walkBrownianCouplingKernel_isMarkov (n : ℕ) :
    IsMarkovKernel (walkBrownianCouplingKernel κ pos hpos B hB U hU μ select hs m E hE hdE n) := by
  unfold walkBrownianCouplingKernel
  infer_instance

omit [MeasurableEq V] in
lemma walkBrownianCouplingKernel_marginals (n : ℕ) (h) :
    (walkBrownianCouplingKernel κ pos hpos B hB U hU μ select hs m E hE hdE n h).fst =
      walkSkeletonHistoryKernel κ pos hpos B hB select hs n
        (TrajectoryCoupling.prefixMap Prod.fst n h) ∧
    (walkBrownianCouplingKernel κ pos hpos B hB U hU μ select hs m E hE hdE n h).snd =
      brownianSkeletonKernel U hU μ (brownianSelectorForWalk select)
        (fun n => hs (n - 1)) n (TrajectoryCoupling.prefixMap Prod.snd n h) := by
  exact (finitePartitionCouplingKernel_spec _ _ _ _ _ _ h).imp_right (fun h => h.1)

noncomputable def walkBrownianInitialCoupling (initial : J) (v : V) (z : Euc d) :
    Measure ((Bool × ClockedWalkExcursion d) × (Bool × C(unitInterval, Euc d))) :=
  finitePartitionCoupling (walkSkeletonInitialLaw κ pos B hB initial v)
    (brownianSkeletonInitialLaw U hU μ z initial)
    (fun i : Fin (m 0) => walkEndpointCell pos (E 0 i))
    (fun i : Fin (m 0) => activeEndpointCell (fun c : C(unitInterval, Euc d) => c 1) (E 0 i))

omit [MeasurableEq V] in
include hpos hE hdE in
lemma walkBrownianInitialCoupling_isProbability (initial : J) (v : V) (z : Euc d) :
    IsProbabilityMeasure (walkBrownianInitialCoupling κ pos B hB U hU μ m E initial v z) := by
  have := walkSkeletonInitialLaw_isProbability κ pos hpos.measurable B hB initial v
  exact (finitePartitionCoupling_spec _ _
    (fun i => measurableSet_walkEndpointCell pos hpos (hE 0 i))
    (fun i => measurableSet_activeEndpointCell _ (ContinuousMap.measurable_eval 1) (hE 0 i))
    (pairwiseDisjoint_walkEndpointCell pos (hdE 0))
    (pairwiseDisjoint_activeEndpointCell _ (hdE 0))).1

omit [MeasurableEq V] in
include hpos hE hdE in
lemma walkBrownianInitialCoupling_marginals (initial : J) (v : V) (z : Euc d) :
    (walkBrownianInitialCoupling κ pos B hB U hU μ m E initial v z).fst =
      walkSkeletonInitialLaw κ pos B hB initial v ∧
    (walkBrownianInitialCoupling κ pos B hB U hU μ m E initial v z).snd =
      brownianSkeletonInitialLaw U hU μ z initial := by
  have := walkSkeletonInitialLaw_isProbability κ pos hpos.measurable B hB initial v
  exact (finitePartitionCoupling_spec _ _
    (fun i => measurableSet_walkEndpointCell pos hpos (hE 0 i))
    (fun i => measurableSet_activeEndpointCell _ (ContinuousMap.measurable_eval 1) (hE 0 i))
    (pairwiseDisjoint_walkEndpointCell pos (hdE 0))
    (pairwiseDisjoint_activeEndpointCell _ (hdE 0))).2.imp_right (fun h => h.1)

/-- An actual joint measure on whole rich walk and whole Brownian excursion
sequences, obtained from the explicit measurable finite-cell couplings. -/
noncomputable def walkBrownianJointLaw (initial : J) (v : V) (z : Euc d) :
    Measure ((ℕ → Bool × ClockedWalkExcursion d) × (ℕ → Bool × C(unitInterval, Euc d))) := by
  letI := walkBrownianInitialCoupling_isProbability κ pos hpos B hB U hU μ m E hE hdE initial v z
  exact SkeletonCoupling.jointPathLaw
    (walkBrownianInitialCoupling κ pos B hB U hU μ m E initial v z)
    (walkBrownianCouplingKernel κ pos hpos B hB U hU μ select hs m E hE hdE)

/-- Both marginals are pushforwards of the original processes, with their
whole actual excursion histories, rather than only their endpoint marginals. -/
theorem walkBrownianJointLaw_marginals (hd : 1 ≤ d) (hμ : IsStandardBrownianLaw μ)
    (hUb : ∀ j, Bornology.IsBounded (U j))
    {A : Set V} (hBA : ∀ j, B j ⊆ A)
    (hA : MeasurableSet A)
    (hexit : ∀ v, ∀ᵐ ω ∂law (absorbedKernel κ hA) v, exitTime A ω ≠ ⊤)
    (initial : J) (v : V) (z : Euc d) :
    (walkBrownianJointLaw κ pos hpos B hB U hU μ select hs m E hE hdE initial v z).fst =
      (law (absorbedKernel κ hA) v).map (actualWalkExcursionSequence pos B initial select) ∧
    (walkBrownianJointLaw κ pos hpos B hB U hU μ select hs m E hE hdE initial v z).snd =
      μ.map (fun ω k => brownianSkeletonExcursion U z initial
        (brownianSelectorForWalk select) k ω) := by
  have := walkBrownianInitialCoupling_isProbability κ pos hpos B hB U hU μ m E hE hdE initial v z
  have := walkSkeletonInitialLaw_isProbability κ pos hpos.measurable B hB initial v
  have hinit := walkBrownianInitialCoupling_marginals κ pos hpos B hB U hU μ m E hE hdE initial v z
  have hstep := walkBrownianCouplingKernel_marginals κ pos hpos B hB U hU μ select hs m E hE hdE
  constructor
  · rw [trajectoryLaw_walkSkeleton_map κ pos hpos B hBA hA hB hexit initial select hs v]
    exact SkeletonCoupling.jointPathLaw_fst _ _ _ _ hinit.1 (fun n h => (hstep n h).1)
  · rw [standardBrownianLaw_skeleton_map hd hμ U hU hUb z initial
      (brownianSelectorForWalk select) (fun n => hs (n - 1))]
    exact SkeletonCoupling.jointPathLaw_snd _ _ _ _ hinit.2 (fun n h => (hstep n h).2)

end SpherePackings.MarkovChain
