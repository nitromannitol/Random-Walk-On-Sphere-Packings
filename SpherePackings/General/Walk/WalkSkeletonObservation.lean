-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/WalkSkeletonObservation.lean` at commit cf73d6e): its declarations that assume a
-- finite state space or a finite conductance network, for the chain of an arbitrary Markov
-- kernel on a measurable space.
import BouRabeeGwynne.WalkSkeletonObservation
import SpherePackings.General.MarkovChain.Absorbed
import SpherePackings.General.Walk.ActualWalkSkeleton

/-! General-state-space version of `BouRabeeGwynne.WalkSkeletonObservation`: the declarations of that file
that assume a finite state space or a finite conductance network. -/

open MeasureTheory ProbabilityTheory Set Preorder
namespace SpherePackings.MarkovChain

open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork BouRabeeGwynne.TrajectoryCoupling
variable {d : ℕ} {V J : Type*} [MeasurableSpace V] [MeasurableEq V] [Countable J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

/-- The stage-wise measurability of the actual walk is assumed for the general chain, since
it was automatic on a finite state space. -/
lemma measurable_walkSkeletonPrefixOfPast (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → V → Option J)
    (hpos : Measurable pos) (hB : ∀ j, MeasurableSet (B j)) (hselect : ∀ m, Measurable (select m))
    (n : ℕ) :
    Measurable (walkSkeletonPrefixOfPast pos B initial select n) :=
  Measurable.of_eval fun i =>
    (measurable_actualWalkStage pos B initial select hpos hB hselect i.val).snd.comp measurable_snd

/-- Recovery holds for the entire observed excursion prefix, not only for
its final endpoint or its most recent state. -/
lemma walkSkeletonPrefixOfPast_observed (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → V → Option J)
    (hpos : Measurable pos) (hB : ∀ j, MeasurableSet (B j)) (hselect : ∀ m, Measurable (select m))
    (n : ℕ) (ω : ℕ → V)
    (hfin : (actualWalkStage pos B initial select n ω).1 ≠ ⊤) :
    walkSkeletonPrefixOfPast pos B initial select n
      (observedHistory (fun ξ => (actualWalkStage pos B initial select n ξ).1) ω) =
        frestrictLe n (fun i => (actualWalkStage pos B initial select i ω).2) := by
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hfin
  have hp : frestrictLe k ω = frestrictLe k
      (observedHistory (fun ξ => (actualWalkStage pos B initial select n ξ).1) ω).2 := by
    rw [observedHistory_of_eq hk.symm]
    funext j
    simp only [paddedHistory, frestrictLe_apply,
      Nat.min_eq_left (Finset.mem_Iic.mp j.property)]
  funext i
  have ht : (actualWalkStage pos B initial select i.val ω).1 ≤ (k : WithTop ℕ) :=
    ((actualWalkStage_clock_mono pos B initial select ω)
      (Finset.mem_Iic.mp i.property)).trans_eq hk.symm
  exact congrArg Prod.snd
    (actualWalkStage_eq_of_prefix pos B initial select hpos hB hselect i.val k hp ht).symm

end SpherePackings.MarkovChain
