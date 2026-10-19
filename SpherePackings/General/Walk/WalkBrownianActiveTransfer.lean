-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/WalkBrownianActiveTransfer.lean` at commit cf73d6e): its declarations that assume a
-- finite state space or a finite conductance network, for the chain of an arbitrary Markov
-- kernel on a measurable space.
import BouRabeeGwynne.WalkBrownianActiveTransfer
import SpherePackings.General.MarkovChain.Absorbed
import SpherePackings.General.Walk.WalkBrownianCoupling
import SpherePackings.General.Walk.WalkSkeletonLaw

/-! General-state-space version of `BouRabeeGwynne.WalkBrownianActiveTransfer`: the declarations of that file
that assume a finite state space or a finite conductance network. -/

set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped unitInterval ENNReal
namespace SpherePackings.MarkovChain

open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork BouRabeeGwynne.TrajectoryCoupling
variable {d : ℕ}
variable {V J : Type*} [MeasurableSpace V] [MeasurableEq V] [Countable J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
/-- Actual original-walk truncation costs at most the actual Brownian tail
plus the first-failure probability of the explicit full-excursion coupling. -/
theorem trajectoryLaw_walkActive_le_brownianActive_add_failure
    (κ : Kernel V V) [IsMarkovKernel κ] (hd : 1 ≤ d)
    (pos : V → Euc d) (hpos : MeasurableEmbedding pos)
    (B : J → Set V) (hB : ∀ j, MeasurableSet (B j))
    (U : J → Set (Euc d)) (hU : ∀ j, IsOpen (U j)) (hUb : ∀ j, Bornology.IsBounded (U j))
    (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ] (hμ : IsStandardBrownianLaw μ)
    (select : ℕ → Euc d → Option J) (hs : ∀ n, Measurable (select n))
    (m : ℕ → ℕ) (E : ∀ n, Fin (m n) → Set (Euc d))
    (hE : ∀ n i, MeasurableSet (E n i))
    (hdE : ∀ n, Pairwise (fun i j => Disjoint (E n i) (E n j)))
    {A : Set V} (hBA : ∀ j, B j ⊆ A)
    (hA : MeasurableSet A) (hexit : ∀ v, ∀ᵐ ω ∂law (absorbedKernel κ hA) v, exitTime A ω ≠ ⊤)
    (initial : J) (v : V) (z : Euc d) (a : ℝ) (K : ℕ) :
    law (absorbedKernel κ hA) v
      {ω | (actualWalkExcursionSequence pos B initial select ω K).1 = false} ≤
      μ {ω | (brownianSkeletonExcursion U z initial (brownianSelectorForWalk select) K ω).1 = false} +
        walkBrownianJointLaw κ pos hpos B hB U hU μ select hs m E hE hdE initial v z
          {p | ∃ i ≤ K, (p.1 i, p.2 i) ∉ goodExcursionPair pos (E i) a} := by
  have hm := walkBrownianJointLaw_marginals κ pos hpos B hB U hU μ select hs m E hE hdE
    hd hμ hUb hBA hA hexit initial v z
  have hw : Measurable (actualWalkExcursionSequence pos B initial select) :=
    measurable_actualWalkExcursionSequence pos B initial select hpos.measurable hB hs
  have hb : Measurable (fun ω k => brownianSkeletonExcursion U z initial
      (brownianSelectorForWalk select) k ω) :=
    Measurable.of_eval fun k => measurable_brownianSkeletonExcursion U hU z initial
      (fun n => hs (n - 1)) k
  have hbound := coupling_walkActive_le_brownianActive_add_firstFailure pos m E a K
    (walkBrownianJointLaw κ pos hpos B hB U hU μ select hs m E hE hdE initial v z)
  rw [hm.1, hm.2, Measure.map_apply hw (measurableSet_sequenceActive K),
    Measure.map_apply hb (measurableSet_sequenceActive K)] at hbound
  exact hbound

end SpherePackings.MarkovChain
