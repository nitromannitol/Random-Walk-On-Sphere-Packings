-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/WalkReconstructionLaw.lean` at commit cf73d6e): its declarations that assume a
-- finite state space or a finite conductance network, for the chain of an arbitrary Markov
-- kernel on a measurable space.
import BouRabeeGwynne.WalkReconstructionLaw
import SpherePackings.General.MarkovChain.Absorbed
import SpherePackings.General.Walk.ActualWalkSkeleton
import SpherePackings.General.Walk.StoppedCurveMeasurable
import SpherePackings.General.Walk.WalkSkeletonLaw

/-! General-state-space version of `BouRabeeGwynne.WalkReconstructionLaw`: the declarations of that file
that assume a finite state space or a finite conductance network. -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace SpherePackings.MarkovChain

open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork BouRabeeGwynne.TrajectoryCoupling
variable {d : ℕ} {V J : Type*} [MeasurableSpace V] [MeasurableEq V] [Countable J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

theorem actualWalkStage_exit_le_of_stopped (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → V → Option J) (A : Set V)
    (hpos : Measurable pos) (hB : ∀ j, MeasurableSet (B j)) (hs : ∀ n, Measurable (select n))
    (hselect : ∀ n v, select n v = none → v ∉ A) (ω : ℕ → V) (n : ℕ)
    (hfinite : (actualWalkStage pos B initial select n ω).1 ≠ ⊤)
    (hstop : (actualWalkStage pos B initial select n ω).2.1 = true) :
    exitTime A ω ≤ (actualWalkStage pos B initial select n ω).1 := by
  induction n with
  | zero => simp only [actualWalkStage, Bool.false_eq_true] at hstop
  | succ n ih =>
    have hle := actualWalkStage_clock_mono pos B initial select ω (Nat.le_succ n)
    have hprevious : (actualWalkStage pos B initial select n ω).1 ≠ ⊤ :=
      ne_top_of_le_ne_top hfinite hle
    by_cases hflag : (actualWalkStage pos B initial select n ω).2.1 = true
    · exact (ih hprevious hflag).trans hle
    · let τ := fun ξ => (actualWalkStage pos B initial select n ξ).1
      let h := observedHistory τ ω
      let choice := walkStageSelector (actualWalkStage pos B initial select n) (select n)
      have hnone : choice h = none := by
        change (selectedClockedExcursion pos B (choice h, h.2 h.1) (futureAt τ ω)).1 = true at hstop
        cases hc : choice h with
        | none => rfl
        | some j => simp only [hc, selectedClockedExcursion, Bool.false_eq_true] at hstop
      have hsame : actualWalkStage pos B initial select n h.2 =
          actualWalkStage pos B initial select n ω :=
        actualWalkStage_observedPast pos B initial select hpos hB hs n ω hprevious
      have hsel : select n (h.2 h.1) = none := by
        simpa only [choice, walkStageSelector, hsame, hflag, Bool.false_eq_true, ↓reduceIte]
          using hnone
      obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hprevious
      have hlast : h.2 h.1 = ω k := by
        dsimp only [h]
        rw [observedHistory_of_eq (show τ ω = k from hk.symm)]
        simp only [paddedHistory, Preorder.frestrictLe_apply, min_self]
      have hout : ω k ∉ A := hlast ▸ hselect n (h.2 h.1) hsel
      exact ((exitTime_le_iff A ω k).mpr ⟨k, le_rfl, hout⟩).trans (hk.le.trans hle)

theorem trajectoryLaw_reconstructedStopped_le (κ : Kernel V V) [IsMarkovKernel κ]
    (pos : V → Euc d) (hpos : Measurable pos) {A : Set V} (B : J → Set V) (hBA : ∀ j, B j ⊆ A)
    (hB : ∀ j, MeasurableSet (B j)) (hA : MeasurableSet A)
    (hexit : ∀ v, ∀ᵐ ω ∂law (absorbedKernel κ hA) v, exitTime A ω ≠ ⊤)
    (initial : J) (select : ℕ → Euc d → Option J) (hs : ∀ n, Measurable (select n))
    (U : Set (Euc d)) (hU : MeasurableSet U) (hselect : ∀ i x, select i x = none → x ∉ U)
    (v : V) (n : ℕ) (r : ℝ≥0) (hr : 0 < r)
    (hbad : law (absorbedKernel κ hA) v
      {ω | (actualWalkExcursionSequence pos B initial select ω n).1 = false} ≤
        (r : ℝ≥0∞)) :
    levyProkhorovEDist
      ((law (absorbedKernel κ hA) v).map (stoppedPolygonalCurve pos (pos ⁻¹' U)))
      (((law (absorbedKernel κ hA) v).map (actualWalkExcursionSequence pos B initial select)).map
        (reconstructedVertexStoppedCurve U n)) ≤ r := by
  rw [Measure.map_map (measurable_reconstructedVertexStoppedCurve hU n)
    (measurable_actualWalkExcursionSequence pos B initial select hpos hB hs)]
  apply levyProkhorov_curveLaws_le_of_ae_reconstruction (law (absorbedKernel κ hA) v)
    (stoppedPolygonalCurve pos (pos ⁻¹' U))
    ((reconstructedVertexStoppedCurve U n) ∘ actualWalkExcursionSequence pos B initial select)
    (measurable_stoppedPolygonalCurve hpos (hpos hU)).aemeasurable
    ((measurable_reconstructedVertexStoppedCurve hU n).comp
      (measurable_actualWalkExcursionSequence pos B initial select hpos hB hs)).aemeasurable
    _ r hr hbad
  filter_upwards [actualWalkStage_ae_all_clocks_finite κ pos B hBA hA hexit initial
    (fun i v => select i (pos v)) v] with ω hω
  intro hgood
  have hflag : (actualWalkStage pos B initial (fun i v => select i (pos v)) n ω).2.1 = true := by
    change (actualWalkStage pos B initial (fun i v => select i (pos v)) n ω).2.1 ≠ false at hgood
    exact Bool.eq_true_of_not_eq_false hgood
  exact (reconstructedVertexStoppedCurve_actual pos B initial select U ω n (hω n)
    (actualWalkStage_exit_le_of_stopped pos B initial (fun i v => select i (pos v))
      (pos ⁻¹' U) hpos hB (fun i => (hs i).comp hpos) (fun i v hv => hselect i (pos v) hv)
      ω n (hω n) hflag)).symm

end SpherePackings.MarkovChain
