-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/WalkPathStopping.lean` at commit cf73d6e): its declarations that assume a
-- finite state space or a finite conductance network, for the chain of an arbitrary Markov
-- kernel on a measurable space.
import BouRabeeGwynne.WalkPathStopping
import SpherePackings.General.MarkovChain.Absorbed

/-! General-state-space version of `BouRabeeGwynne.WalkPathStopping`: the declarations of that file
that assume a finite state space or a finite conductance network. -/

open MeasureTheory ProbabilityTheory Set Preorder
open scoped Classical
namespace SpherePackings.MarkovChain

open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork BouRabeeGwynne.TrajectoryCoupling
variable {V : Type*} [MeasurableSpace V] [MeasurableEq V]

lemma measurable_stoppedWalkPath (B : Set V) (hB : MeasurableSet B) :
    Measurable (stoppedWalkPath B) := by
  classical
  apply Measurable.of_eval
  intro n
  induction n with
  | zero => exact measurable_pi_apply 0
  | succ n ih =>
    simp only [stoppedWalkPath_succ]
    exact Measurable.ite (ih hB) (measurable_pi_apply _) ih

lemma measurable_stopHistory (B : Set V) (hB : MeasurableSet B) (n : ℕ) :
    Measurable (stopHistory B n) :=
  (measurable_frestrictLe n).comp
    ((measurable_stoppedWalkPath B hB).comp (measurable_paddedHistory (V := V) n).snd)

end SpherePackings.MarkovChain
