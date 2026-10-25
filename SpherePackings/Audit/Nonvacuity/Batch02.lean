module

/- Nonvacuity examples written by the independent reviewer (Claude Haiku 5.5) of audit batch 02;
   see `AUDIT.md`. They show that the hypothesis bundles named below can hold together. -/
public import BouRabeeGwynne.WalkSkeletonLaw
public import BouRabeeGwynne.WalkReconstructionLaw

@[expose] public section

-- The reviewer's examples, kept as written.
set_option linter.unusedVariables false
set_option linter.deprecated false

namespace SpherePackings.Audit.Nonvacuity02
open BouRabeeGwynne

/-! Nonvacuity for the hypothesis bundle of
`FiniteConductanceNetwork.trajectoryLaw_walkSkeleton_map`
(pos injective, `B j ⊆ A`, positive total conductance on `A` and on each `B j`,
`BoundaryAccessible A`, measurable selectors) on a concrete two-vertex network. -/

open MeasureTheory ProbabilityTheory Set
open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork

/-- Two-vertex path `0 — 1` with unit conductance and no loops. -/
def toyNet : FiniteConductanceNetwork (Fin 2) where
  a := fun v w => if v = w then 0 else 1
  symm := by
    intro v w
    by_cases h : v = w
    · subst h; rfl
    · simp [h, Ne.symm h]
  nonneg := by
    intro v w
    by_cases h : v = w <;> simp [h]
  loop_zero := by intro v; simp

/-- Injective positions on the line. -/
noncomputable def toyPos : Fin 2 → Euc 1 := fun i => EuclideanSpace.single 0 ((i : ℕ) : ℝ)

lemma toyPos_injective : Function.Injective toyPos := by
  intro i j h
  have h0 := congrArg (fun x : Euc 1 => x 0) h
  simp [toyPos] at h0
  exact Fin.ext (by exact_mod_cast h0)

/-- The `Option` measurable structure is not in Mathlib; use the discrete one. -/
instance toyOptionMeasurableSpace : MeasurableSpace (Option Unit) := ⊤

instance toyOptionSingleton : MeasurableSingletonClass (Option Unit) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- Interior set `A = {0}`; vertex `1` is outside. -/
def toyA : Set (Fin 2) := {0}

lemma toyA_pos : ∀ v ∈ toyA, 0 < toyNet.totalConductance v := by
  intro v hv
  rw [toyA, mem_singleton_iff] at hv
  subst hv
  simp [FiniteConductanceNetwork.totalConductance, toyNet, Fin.sum_univ_two]

lemma toyA_access : toyNet.BoundaryAccessible toyA := by
  intro v hv
  rw [toyA, mem_singleton_iff] at hv
  subst hv
  refine ⟨1, by simp [toyA], Relation.ReflTransGen.single ?_⟩
  simp [toyNet]

/-- One ball, equal to `{0} ⊆ A`. -/
def toyB : Unit → Set (Fin 2) := fun _ => {0}

lemma toyB_subset : ∀ j, toyB j ⊆ toyA := fun _ => subset_rfl

lemma toyB_pos : ∀ j v, v ∈ toyB j → 0 < toyNet.totalConductance v := by
  intro j v hv
  exact toyA_pos v hv

/-- The constant selector always continues from an arbitrary position. -/
def toySelect : ℕ → Euc 1 → Option Unit := fun _ _ => some ()

lemma toySelect_measurable : ∀ n, Measurable (toySelect n) := fun _ => measurable_const

/-- The hypothesis bundle is jointly satisfiable, so the law identity applies here
(not vacuously). -/
example (v : Fin 2) :
    (toyNet.trajectoryLaw toyA toyA_pos v).map
        (actualWalkExcursionSequence toyPos toyB () toySelect) =
      Kernel.trajMeasure (X := fun _ => Bool × ClockedWalkExcursion 1)
        (toyNet.walkSkeletonInitialLaw toyPos toyB toyB_pos () v)
        (toyNet.walkSkeletonHistoryKernel toyPos toyPos_injective toyB toyB_pos
          toySelect toySelect_measurable) :=
  toyNet.trajectoryLaw_walkSkeleton_map toyPos toyPos_injective toyB toyB_subset
    toyA_pos toyB_pos toyA_access () toySelect toySelect_measurable v

open Classical in
/-- A selector that stops exactly at the outside vertex position `toyPos 1`. -/
noncomputable def toyStopSelect : ℕ → Euc 1 → Option Unit :=
  fun _ x => if x = toyPos 1 then none else some ()

lemma toyStopSelect_measurable : ∀ n, Measurable (toyStopSelect n) := by
  intro n
  apply measurable_to_countable'
  intro x
  rcases x with _ | u
  · have h : toyStopSelect n ⁻¹' {none} = {toyPos 1} := by
      ext y
      by_cases hy : y = toyPos 1 <;> simp [toyStopSelect, hy]
    rw [h]
    exact measurableSet_singleton _
  · have h : toyStopSelect n ⁻¹' {some u} = {toyPos 1}ᶜ := by
      ext y
      by_cases hy : y = toyPos 1 <;> simp [toyStopSelect, hy]
    rw [h]
    exact (measurableSet_singleton _).compl

/-- Stopping set `U = {toyPos 0}`: the selector stops only outside `U`. -/
def toyU : Set (Euc 1) := {toyPos 0}

lemma toyU_measurable : MeasurableSet toyU := measurableSet_singleton _

lemma toyStop_select : ∀ i x, toyStopSelect i x = none → x ∉ toyU := by
  intro i x hx hxU
  simp only [toyStopSelect] at hx
  split_ifs at hx with h
  rw [toyU, mem_singleton_iff] at hxU
  exact absurd (toyPos_injective (h.symm.trans hxU)) (by decide)

/-- The reconstruction bundle at `r = 1`: `hselect` and `hU` are nontrivial here. -/
example (n : ℕ) (v : Fin 2) :
    levyProkhorovEDist
      ((toyNet.trajectoryLaw toyA toyA_pos v).map
        (stoppedPolygonalCurve toyPos (toyPos ⁻¹' toyU)))
      (((toyNet.trajectoryLaw toyA toyA_pos v).map
        (actualWalkExcursionSequence toyPos toyB () toyStopSelect)).map
        (reconstructedVertexStoppedCurve toyU n)) ≤ 1 :=
  toyNet.trajectoryLaw_reconstructedStopped_le toyPos toyB toyB_subset toyA_pos
    toyA_access () toyStopSelect toyU toyU_measurable toyStop_select v n 1 one_pos
    (by simpa using prob_le_one)

end SpherePackings.Audit.Nonvacuity02
