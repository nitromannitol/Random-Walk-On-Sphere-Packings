/- Nonvacuity examples written by the independent reviewer (Claude Haiku 5.5) of audit batch 15;
   see `AUDIT.md`. They show that the hypothesis bundles named below can hold together. -/
import SpherePackings.General.MarkovChain.Dirichlet
import SpherePackings.General.NearestNeighbourWalk

-- The reviewer's examples, kept as written.
set_option linter.unusedVariables false
set_option linter.deprecated false

/-! Nonvacuity witnesses for batch 15 (audit nonvacuity examples).

* `toggleKernel`: the two-state chain on `Bool` that flips its state at every step.
  With `A = {true}`, `B = {false}` and data `0`, the Dirichlet problem has a unique solution
  (`hasUnique`), so the hypothesis of `survival_eq_zero_of_unique` holds, and its conclusion
  `survival toggleKernel {true} true = 0` is then a genuine consequence (`survival_true`).
* `trivialWalk`: a `NearestNeighbourWalk 1` with vertex set `ℝ` (all of it), every pair adjacent,
  and the walk that stays put; `IsNearestVertex` holds for the identity selection. -/

open MeasureTheory ProbabilityTheory SpherePackings.MarkovChain

namespace SpherePackings.Audit15

/-- The chain on `Bool` that flips its state at every step. -/
noncomputable def toggleKernel : Kernel Bool Bool :=
  Kernel.deterministic (fun b : Bool => !b) (measurable_of_countable _)

instance : IsMarkovKernel toggleKernel := by
  unfold toggleKernel
  infer_instance

lemma toggleKernel_true : toggleKernel true = Measure.dirac false := by
  simp [toggleKernel, Kernel.deterministic_apply]

/-- With `A = {true}`, `B = {false}` and data `0`, the Dirichlet problem has a unique solution. -/
lemma hasUnique : HasUniqueDirichletSolution toggleKernel {true} {false} (fun _ => (0 : ℝ)) := by
  refine ⟨fun _ => 0, ⟨fun a ha => ?_, fun b hb => rfl⟩, ?_⟩
  · rw [Set.mem_singleton_iff] at ha
    subst ha
    refine ⟨integrable_const _, ?_⟩
    simp
  · rintro f' ⟨hA, hB⟩ x hx
    have hfalse : f' false = 0 := hB false (Set.mem_singleton _)
    have htrue : f' true = f' false := by
      have h := (hA true (Set.mem_singleton _)).2
      rw [toggleKernel_true, integral_dirac] at h
      exact h.symm
    simp only [Set.mem_union, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · simp [htrue, hfalse]
    · simp [hfalse]

/-- The conclusion of `survival_eq_zero_of_unique` is attained (not vacuous) for this chain. -/
theorem survival_true : survival toggleKernel {true} true = 0 :=
  survival_eq_zero_of_unique toggleKernel (measurableSet_singleton true)
    (Set.disjoint_singleton.mpr (by decide)) hasUnique (by simp)

/-- A nearest-neighbour walk on the whole line: all of `ℝ` is the vertex set, every pair of
vertices is adjacent, and the walk stays put. -/
noncomputable def trivialWalk : SpherePackings.NearestNeighbourWalk 1 where
  V := Set.univ
  adj _ _ := True
  adj_symm _ _ _ := trivial
  kernel := Kernel.deterministic id measurable_id
  isMarkovKernel := inferInstance
  ae_adj _ := ae_of_all _ fun _ => trivial

example : trivialWalk.IsNearestVertex (fun z => ⟨z, Set.mem_univ z⟩) := by
  intro z v
  simp

end SpherePackings.Audit15

#print axioms SpherePackings.Audit15.survival_true
#print axioms SpherePackings.Audit15.trivialWalk
