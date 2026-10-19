/- Nonvacuity examples written by the independent reviewer (Claude Haiku 5.5) of audit batch 01;
   see `AUDIT.md`. They show that the hypothesis bundles named below can hold together. -/
import BouRabeeGwynne.ActualWalkSkeleton

-- The reviewer's examples, kept as written.
set_option linter.unusedVariables false
set_option linter.deprecated false

/-! Scratch nonvacuity checks for batch-1 hypothesis bundles.
Not part of the repository. -/

open MeasureTheory ProbabilityTheory Set

namespace SpherePackings.Audit.Nonvacuity01
open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork
/-- Two vertices joined by one edge of unit conductance. -/
def twoVertexNet : FiniteConductanceNetwork (Fin 2) where
  a v w := if v = w then 0 else 1
  symm v w := by by_cases h : v = w <;> simp [h, eq_comm]
  nonneg v w := by by_cases h : v = w <;> simp [h]
  loop_zero v := by simp

/-- The interior set `{0}`; its only exit is the vertex `1`. -/
def interior0 : Set (Fin 2) := {0}

lemma twoVertexNet_hpos : ∀ v ∈ interior0, 0 < twoVertexNet.totalConductance v := by
  intro v hv
  rw [interior0, Set.mem_singleton_iff] at hv
  subst hv
  simp [totalConductance, twoVertexNet, Fin.sum_univ_two]

lemma twoVertexNet_access : twoVertexNet.BoundaryAccessible interior0 := by
  intro v hv
  rw [interior0, Set.mem_singleton_iff] at hv
  subst hv
  refine ⟨1, by simp [interior0], Relation.ReflTransGen.single ?_⟩
  simp [twoVertexNet]

instance : MeasurableSpace (Option Unit) := ⊤

instance : MeasurableSingletonClass (Option Unit) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- The hypothesis bundle of `actualWalkStage_ae_all_clocks_finite` is satisfiable, and the
conclusion is obtained for the concrete network. -/
example (pos : Fin 2 → Euc 1) :
    ∀ᵐ ω ∂twoVertexNet.trajectoryLaw interior0 twoVertexNet_hpos 0, ∀ n,
      (actualWalkStage pos (fun _ : Unit => interior0) () (fun _ _ => some ()) n ω).1 ≠ ⊤ :=
  actualWalkStage_ae_all_clocks_finite (A := interior0) twoVertexNet pos
    (fun _ : Unit => interior0) (fun _ => subset_rfl) twoVertexNet_hpos twoVertexNet_access
    () (fun _ _ => some ()) 0

/-- The hypothesis bundle of `trajectoryLaw_observed_selectedExcursion` (in particular the
almost-sure finiteness `hfin`, here derived from `BoundaryAccessible`) is satisfiable. -/
theorem nonvacuous_selectedExcursion (pos : Fin 2 → Euc 1) (v : Fin 2) :
    (twoVertexNet.trajectoryLaw interior0 twoVertexNet_hpos v).map (fun ω =>
        (observedHistory (exitTime interior0) ω,
          selectedClockedExcursion pos (fun _ : Unit => interior0)
            (some (), (observedHistory (exitTime interior0) ω).2 (observedHistory (exitTime interior0) ω).1)
            (futureAt (exitTime interior0) ω))) =
      (twoVertexNet.trajectoryLaw interior0 twoVertexNet_hpos v).map (observedHistory (exitTime interior0))
        ⊗ₘ twoVertexNet.selectedClockedRestartKernel pos (fun _ : Unit => interior0)
            (fun _ _ hv => twoVertexNet_hpos _ hv) (fun _ => some ()) measurable_const :=
  twoVertexNet.trajectoryLaw_observed_selectedExcursion pos (fun _ : Unit => interior0)
    (fun _ => subset_rfl) twoVertexNet_hpos (fun _ _ hv => twoVertexNet_hpos _ hv)
    (fun _ => some ()) measurable_const v (exitTime_isStoppingTime interior0)
    (twoVertexNet.trajectoryLaw_ae_finiteExit interior0 twoVertexNet_hpos twoVertexNet_access v)

end SpherePackings.Audit.Nonvacuity01