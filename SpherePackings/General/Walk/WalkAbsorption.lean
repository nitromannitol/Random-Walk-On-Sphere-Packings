module

-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/WalkAbsorption.lean` at commit cf73d6e): its declarations that assume a
-- finite state space or a finite conductance network, for the chain of an arbitrary Markov
-- kernel on a measurable space.
public import BouRabeeGwynne.WalkAbsorption
public import SpherePackings.General.MarkovChain.Absorbed
public import SpherePackings.General.Walk.SkeletonKernels
public import SpherePackings.General.Walk.WalkPathStopping

@[expose] public section

/-! General-state-space version of `BouRabeeGwynne.WalkAbsorption`: the declarations of that file
that assume a finite state space or a finite conductance network. -/

open MeasureTheory ProbabilityTheory Set Preorder
open scoped Classical
namespace SpherePackings.MarkovChain

open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork BouRabeeGwynne.TrajectoryCoupling
variable {V : Type*}  [MeasurableSpace V] [MeasurableEq V]
open TrajectoryCoupling
variable (κ : Kernel V V) [IsMarkovKernel κ]

lemma historyKernel_map_stopStep {A B : Set V} (hBA : B ⊆ A)
    (hA : MeasurableSet A)
    (hB : MeasurableSet B) (n : ℕ) (h : Finset.Iic n → V) :
    (historyKernel (absorbedKernel κ hA) n h).map
      (fun x => if stopHistory B n h ⟨n, Finset.mem_Iic.mpr le_rfl⟩ ∈ B then x
        else stopHistory B n h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) =
      historyKernel (absorbedKernel κ hB) n (stopHistory B n h) := by
  by_cases hm : stopHistory B n h ⟨n, Finset.mem_Iic.mpr le_rfl⟩ ∈ B
  · simp only [hm, ↓reduceIte]
    change (absorbedKernel κ hA (h ⟨n, _⟩)).map id = _
    rw [Measure.map_id]
    have he := stopHistory_last_mem_imp_eq B n h hm
    change absorbedKernel κ hA (h ⟨n, _⟩) = absorbedKernel κ hB (stopHistory B n h ⟨n, _⟩)
    rw [he, absorbedKernel_of_mem κ hA (hBA (he ▸ hm)),
      absorbedKernel_of_mem κ hB (he ▸ hm)]
  · simp only [hm, ↓reduceIte]
    change (absorbedKernel κ hA (h ⟨n, _⟩)).map (fun _ => stopHistory B n h ⟨n, _⟩) =
      absorbedKernel κ hB (stopHistory B n h ⟨n, _⟩)
    rw [absorbedKernel_of_not_mem κ hB hm, Measure.map_const]
    simp

lemma trajectoryLaw_map_stopHistory {A B : Set V} (hBA : B ⊆ A)
    (hA : MeasurableSet A)
    (hB : MeasurableSet B) (v : V) (n : ℕ) :
    ((law (absorbedKernel κ hA) v).map (frestrictLe n)).map (stopHistory B n) =
      (law (absorbedKernel κ hB) v).map (frestrictLe n) := by
  induction n with
  | zero =>
    rw [law_initialHistory (absorbedKernel κ hA) v, law_initialHistory (absorbedKernel κ hB) v,
      Measure.map_dirac' (measurable_stopHistory B hB 0), stopHistory_zero]
  | succ n ih =>
    unfold law at ih
    have hpA := prefix_succ (Measure.dirac v) (historyKernel (absorbedKernel κ hA)) n
    have hpB := prefix_succ (Measure.dirac v) (historyKernel (absorbedKernel κ hB)) n
    change (law (absorbedKernel κ hA) v).map (frestrictLe (n + 1)) = _ at hpA
    change (law (absorbedKernel κ hB) v).map (frestrictLe (n + 1)) = _ at hpB
    have hlast : Measurable (fun p : (Finset.Iic n → V) × V =>
        stopHistory B n p.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩) :=
      (measurable_pi_apply _).comp ((measurable_stopHistory B hB n).comp measurable_fst)
    have hval : Measurable (fun p : (Finset.Iic n → V) × V =>
        if stopHistory B n p.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩ ∈ B then p.2
        else stopHistory B n p.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩) :=
      Measurable.ite (hlast hB) measurable_snd hlast
    have hstep : Measurable (fun p : (Finset.Iic n → V) × V => (stopHistory B n p.1,
        if stopHistory B n p.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩ ∈ B then p.2
        else stopHistory B n p.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩)) :=
      ((measurable_stopHistory B hB n).comp measurable_fst).prodMk hval
    rw [hpA, hpB, Measure.map_map (measurable_stopHistory B hB (n + 1)) (measurable_append n),
      stopHistory_append, ← Measure.map_map (measurable_append n) hstep,
      compProd_map_dependent_of_kernel_map _ _ _ _ _ (measurable_stopHistory B hB n)
        hval (historyKernel_map_stopStep κ hBA hA hB n), ih]

/-- Actual absorption locality, including paths whose first exit is infinite. -/
theorem trajectoryLaw_map_stoppedWalkPath {A B : Set V} (hBA : B ⊆ A)
    (hA : MeasurableSet A)
    (hB : MeasurableSet B) (v : V) :
    (law (absorbedKernel κ hA) v).map (stoppedWalkPath B) = law (absorbedKernel κ hB) v := by
  apply measure_eq_of_prefix_eq
  intro n
  rw [Measure.map_map (measurable_frestrictLe n) (measurable_stoppedWalkPath B hB)]
  have he : frestrictLe (π := fun _ : ℕ => V) n ∘ stoppedWalkPath B =
      stopHistory B n ∘ frestrictLe (π := fun _ : ℕ => V) n := by
    funext ω
    exact (stopHistory_prefix B n ω).symm
  rw [he, ← Measure.map_map (measurable_stopHistory B hB n) (measurable_frestrictLe n)]
  exact trajectoryLaw_map_stopHistory κ hBA hA hB v n

/-- The richer ball excursion sampled from the original ambient trajectory
has exactly the constructed ball excursion kernel, including its integer clock. -/
theorem trajectoryLaw_map_clockedExcursion {d : ℕ} (pos : V → Euc d) (hpos : Measurable pos)
    {A B : Set V} (hBA : B ⊆ A)
    (hA : MeasurableSet A)
    (hB : MeasurableSet B) (v : V) :
    (law (absorbedKernel κ hA) v).map (ClockedWalkExcursion.ofWalk pos B) =
      clockedWalkExcursionKernel κ pos hB v := by
  rw [clockedWalkExcursionKernel_apply κ hpos hB,
    ← trajectoryLaw_map_stoppedWalkPath κ hBA hA hB v,
    Measure.map_map (measurable_ofWalk hpos hB) (measurable_stoppedWalkPath B hB)]
  congr 1
  funext ω
  exact (clockedExcursion_stoppedWalkPath pos B ω).symm

end SpherePackings.MarkovChain
