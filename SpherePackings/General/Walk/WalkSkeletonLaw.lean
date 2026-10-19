-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/WalkSkeletonLaw.lean` at commit cf73d6e): its declarations that assume a
-- finite state space or a finite conductance network, for the chain of an arbitrary Markov
-- kernel on a measurable space.
import BouRabeeGwynne.WalkSkeletonLaw
import SpherePackings.General.MarkovChain.Absorbed
import SpherePackings.General.Walk.ActualWalkSkeleton
import SpherePackings.General.Walk.SkeletonKernels
import SpherePackings.General.Walk.WalkAbsorption
import SpherePackings.General.Walk.WalkSelectedRestart
import SpherePackings.General.Walk.WalkSkeletonKernel
import SpherePackings.General.Walk.WalkSkeletonObservation

/-! General-state-space version of `BouRabeeGwynne.WalkSkeletonLaw`: the declarations of that file
that assume a finite state space or a finite conductance network. -/

set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Preorder
namespace SpherePackings.MarkovChain

open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork BouRabeeGwynne.TrajectoryCoupling
variable {d : ℕ} {V J : Type*} [MeasurableSpace V] [MeasurableEq V] [Countable J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

lemma measurable_actualWalkExcursionSequence (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → Euc d → Option J)
    (hpos : Measurable pos) (hB : ∀ j, MeasurableSet (B j))
    (hs : ∀ n, Measurable (select n)) :
    Measurable (actualWalkExcursionSequence pos B initial select) :=
  Measurable.of_eval fun n =>
    (measurable_actualWalkStage pos B initial (fun i v => select i (pos v)) hpos hB
      (fun i => (hs i).comp hpos) n).snd

variable (κ : Kernel V V) [IsMarkovKernel κ]
noncomputable def walkSkeletonInitialLaw (pos : V → Euc d) (B : J → Set V)
    (hB : ∀ j, MeasurableSet (B j)) (initial : J) (v : V) :
    Measure (Bool × ClockedWalkExcursion d) :=
  (clockedWalkExcursionKernel κ pos (hB initial) v).map (fun e => (false, e))

omit [MeasurableEq V] [Countable J] [MeasurableSpace (Option J)]
  [MeasurableSingletonClass (Option J)] in
lemma walkSkeletonInitialLaw_isProbability (pos : V → Euc d) (hpos : Measurable pos)
    (B : J → Set V) (hB : ∀ j, MeasurableSet (B j)) (initial : J) (v : V) :
    IsProbabilityMeasure (walkSkeletonInitialLaw κ pos B hB initial v) := by
  have := clockedWalkExcursionKernel_isMarkov κ hpos (hB initial)
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_const.prodMk measurable_id).aemeasurable).mpr inferInstance

omit [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)] in
lemma trajectoryLaw_walkSkeleton_initial (pos : V → Euc d) (hpos : Measurable pos) {A : Set V}
    (B : J → Set V) (hBA : ∀ j, B j ⊆ A)
    (hA : MeasurableSet A)
    (hB : ∀ j, MeasurableSet (B j))
    (initial : J) (select : ℕ → Euc d → Option J) (v : V) :
    (law (absorbedKernel κ hA) v).map (fun ω => actualWalkExcursionSequence pos B initial select ω 0) =
      walkSkeletonInitialLaw κ pos B hB initial v := by
  have hmark : Measurable (fun e : ClockedWalkExcursion d => (false, e)) :=
    measurable_const.prodMk measurable_id
  change (law (absorbedKernel κ hA) v).map
    ((fun e => (false, e)) ∘ ClockedWalkExcursion.ofWalk pos (B initial)) = _
  rw [← Measure.map_map hmark (measurable_ofWalk hpos (hB initial)),
    trajectoryLaw_map_clockedExcursion κ pos hpos (hBA initial) hA (hB initial)]
  rfl

lemma selectedClockedRestartKernel_eq_walkHistory (pos : V → Euc d)
    (hpos : MeasurableEmbedding pos) (B : J → Set V)
    (hB : ∀ j, MeasurableSet (B j)) (initial : J)
    (select : ℕ → Euc d → Option J) (hs : ∀ n, Measurable (select n)) (n : ℕ)
    (h : ℕ × (ℕ → V))
    (hend : ClockedWalkExcursion.endPoint
      (actualWalkStage pos B initial (fun i v => select i (pos v)) n h.2).2.2 =
      pos (h.2 h.1)) :
    selectedClockedRestartKernel κ pos hpos.measurable B hB
      (walkStageSelector (actualWalkStage pos B initial (fun i v => select i (pos v)) n)
        (fun v => select n (pos v)))
      (measurable_walkStageSelector
        (measurable_actualWalkStage pos B initial (fun i v => select i (pos v)) hpos.measurable hB
          (fun i => (hs i).comp hpos.measurable) n)
        (fun v => select n (pos v)) ((hs n).comp hpos.measurable)) h =
      walkSkeletonHistoryKernel κ pos hpos B hB select hs n
        (walkSkeletonPrefixOfPast pos B initial (fun i v => select i (pos v)) n h) := by
  change selectedExcursionKernel (fun j => clockedWalkExcursionKernel κ pos (hB j))
      (ClockedWalkExcursion.constant ∘ pos)
      (ClockedWalkExcursion.measurable_constant.comp hpos.measurable)
      ((if (actualWalkStage pos B initial (fun i v => select i (pos v)) n h.2).2.1 = true
        then none else select n (pos (h.2 h.1))), h.2 h.1) =
    absorbingExcursionKernel (fun j => spatialClockedExcursionKernel κ pos hpos (B j) (hB j))
      ClockedWalkExcursion.endPoint ClockedWalkExcursion.measurable_endPoint
      ClockedWalkExcursion.constant ClockedWalkExcursion.measurable_constant
      (select n) (hs n) (actualWalkStage pos B initial (fun i v => select i (pos v)) n h.2).2
  generalize he : (actualWalkStage pos B initial (fun i v => select i (pos v)) n h.2).2 = e at hend ⊢
  rcases e with ⟨flag, e⟩
  cases flag with
  | true =>
    change Measure.dirac (true, ClockedWalkExcursion.constant (pos (h.2 h.1))) =
      Measure.dirac (true, ClockedWalkExcursion.constant (ClockedWalkExcursion.endPoint e))
    rw [hend]
  | false =>
    change selectedExcursionKernel (fun j => clockedWalkExcursionKernel κ pos (hB j))
        (ClockedWalkExcursion.constant ∘ pos)
        (ClockedWalkExcursion.measurable_constant.comp hpos.measurable)
        (select n (pos (h.2 h.1)), h.2 h.1) =
      selectedExcursionKernel (fun j => spatialClockedExcursionKernel κ pos hpos (B j) (hB j))
        ClockedWalkExcursion.constant ClockedWalkExcursion.measurable_constant
        (select n (ClockedWalkExcursion.endPoint e), ClockedWalkExcursion.endPoint e)
    rw [hend]
    cases hj : select n (pos (h.2 h.1)) with
    | none => rfl
    | some j =>
      simp only [selectedExcursionKernel_some, spatialClockedExcursionKernel_vertex κ]

/-- The full observed excursion history and its next rich state have the
actual own-history transition law. -/
theorem trajectoryLaw_walkSkeleton_history_next (pos : V → Euc d)
    (hpos : MeasurableEmbedding pos) {A : Set V} (B : J → Set V)
    (hBA : ∀ j, B j ⊆ A) (hA : MeasurableSet A)
    (hB : ∀ j, MeasurableSet (B j))
    (hexit : ∀ v, ∀ᵐ ω ∂law (absorbedKernel κ hA) v, exitTime A ω ≠ ⊤) (initial : J)
    (select : ℕ → Euc d → Option J) (hs : ∀ n, Measurable (select n)) (v : V) (n : ℕ) :
    (law (absorbedKernel κ hA) v).map (fun ω =>
      (frestrictLe n (actualWalkExcursionSequence pos B initial select ω),
        actualWalkExcursionSequence pos B initial select ω (n + 1))) =
      (law (absorbedKernel κ hA) v).map
        (fun ω => frestrictLe n (actualWalkExcursionSequence pos B initial select ω))
        ⊗ₘ walkSkeletonHistoryKernel κ pos hpos B hB select hs n := by
  let vselect := fun i v => select i (pos v)
  let τ := fun ω => (actualWalkStage pos B initial vselect n ω).1
  let F := walkSkeletonPrefixOfPast pos B initial vselect n
  let choice := walkStageSelector (actualWalkStage pos B initial vselect n) (vselect n)
  let P := law (absorbedKernel κ hA) v
  have hvs : ∀ i, Measurable (vselect i) := fun i => (hs i).comp hpos.measurable
  have hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => V)) τ :=
    actualWalkStage_clock_isStoppingTime pos B initial vselect hpos.measurable hB hvs n
  have hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤ := by
    filter_upwards [actualWalkStage_ae_all_clocks_finite κ pos B hBA hA hexit
      initial vselect v] with ω hω
    exact hω n
  have hobs : Measurable (observedHistory τ) := measurable_observedHistory hτ.measurable'
  have hF : Measurable F :=
    measurable_walkSkeletonPrefixOfPast pos B initial vselect hpos.measurable hB hvs n
  have hc : Measurable choice := measurable_walkStageSelector
    (measurable_actualWalkStage pos B initial vselect hpos.measurable hB hvs n) (vselect n)
    (hvs n)
  have hend : ∀ᵐ h ∂P.map (observedHistory τ),
      ClockedWalkExcursion.endPoint (actualWalkStage pos B initial vselect n h.2).2.2 =
        pos (h.2 h.1) := by
    apply (ae_map_iff hobs.aemeasurable (measurableSet_eq_fun
      (ClockedWalkExcursion.measurable_endPoint.comp
        ((measurable_actualWalkStage pos B initial vselect hpos.measurable hB hvs n).snd.snd.comp
          measurable_snd))
      (hpos.measurable.comp measurable_historyLast))).mpr
    filter_upwards [hfin] with ω hω
    simp only [Function.comp_def]
    rw [actualWalkStage_observedPast pos B initial vselect hpos.measurable hB hvs n ω hω]
    exact actualWalkStage_endPoint_observed pos B initial vselect n ω hω
  have hrow : ∀ᵐ h ∂P.map (observedHistory τ),
      (selectedClockedRestartKernel κ pos hpos.measurable B hB choice hc h).map id =
        walkSkeletonHistoryKernel κ pos hpos B hB select hs n (F h) := by
    filter_upwards [hend] with h hh
    rw [Measure.map_id]
    exact selectedClockedRestartKernel_eq_walkHistory κ pos hpos B hB initial select hs n h hh
  have hfactor := compProd_map_dependent_of_kernel_map_ae
    (P.map (observedHistory τ)) (selectedClockedRestartKernel κ pos hpos.measurable B hB choice hc)
    (walkSkeletonHistoryKernel κ pos hpos B hB select hs n)
    F (fun _ e => e) hF measurable_snd hrow
  have hrecovery : ∀ᵐ ω ∂P, F (observedHistory τ ω) =
      frestrictLe n (actualWalkExcursionSequence pos B initial select ω) := by
    filter_upwards [hfin] with ω hω
    exact walkSkeletonPrefixOfPast_observed pos B initial vselect hpos.measurable hB hvs n ω hω
  have hpast : (P.map (observedHistory τ)).map F =
      P.map (fun ω => frestrictLe n (actualWalkExcursionSequence pos B initial select ω)) := by
    rw [Measure.map_map hF hobs]
    exact Measure.map_congr hrecovery
  have hnext : Measurable (fun ω : ℕ → V =>
      actualWalkExcursionSequence pos B initial select ω (n + 1)) :=
    (measurable_pi_apply (n + 1)).comp
      (measurable_actualWalkExcursionSequence pos B initial select hpos.measurable hB hs)
  have hcompress : Measurable (fun p : (ℕ × (ℕ → V)) × (Bool × ClockedWalkExcursion d) =>
      (F p.1, p.2)) := (hF.comp measurable_fst).prodMk measurable_snd
  have hjoint : P.map (fun ω => (observedHistory τ ω,
      actualWalkExcursionSequence pos B initial select ω (n + 1))) =
      P.map (observedHistory τ) ⊗ₘ selectedClockedRestartKernel κ pos hpos.measurable B hB choice hc :=
    trajectoryLaw_observed_selectedExcursion κ pos hpos.measurable B hBA hA hB choice hc v hτ hfin
  calc
    _ = P.map (fun ω => (F (observedHistory τ ω),
        actualWalkExcursionSequence pos B initial select ω (n + 1))) := by
      apply Measure.map_congr
      filter_upwards [hrecovery] with ω hω
      exact congrArg (fun h => (h, actualWalkExcursionSequence pos B initial select ω (n + 1)))
        hω.symm
    _ = (P.map (fun ω => (observedHistory τ ω,
        actualWalkExcursionSequence pos B initial select ω (n + 1)))).map
          (fun p => (F p.1, p.2)) := by
      rw [Measure.map_map hcompress (hobs.prodMk hnext)]
      rfl
    _ = _ := by rw [hjoint, hfactor, hpast]

/-- The entire rich excursion sequence extracted from the original ambient
walk is the genuine adaptive trajectory measure, including permanent flags. -/
theorem trajectoryLaw_walkSkeleton_map (pos : V → Euc d)
    (hpos : MeasurableEmbedding pos) {A : Set V} (B : J → Set V)
    (hBA : ∀ j, B j ⊆ A) (hA : MeasurableSet A)
    (hB : ∀ j, MeasurableSet (B j))
    (hexit : ∀ v, ∀ᵐ ω ∂law (absorbedKernel κ hA) v, exitTime A ω ≠ ⊤) (initial : J)
    (select : ℕ → Euc d → Option J) (hs : ∀ n, Measurable (select n)) (v : V) :
    (law (absorbedKernel κ hA) v).map (actualWalkExcursionSequence pos B initial select) =
      Kernel.trajMeasure (X := fun _ => Bool × ClockedWalkExcursion d)
        (walkSkeletonInitialLaw κ pos B hB initial v)
        (walkSkeletonHistoryKernel κ pos hpos B hB select hs) := by
  have := walkSkeletonInitialLaw_isProbability κ pos hpos.measurable B hB initial v
  apply TrajectoryCoupling.map_eq_trajMeasure_of_history_next (law (absorbedKernel κ hA) v) _
    (measurable_actualWalkExcursionSequence pos B initial select hpos.measurable hB hs)
  · exact trajectoryLaw_walkSkeleton_initial κ pos hpos.measurable B hBA hA hB initial select v
  · exact trajectoryLaw_walkSkeleton_history_next κ pos hpos B hBA hA hB hexit initial select hs v

end SpherePackings.MarkovChain
