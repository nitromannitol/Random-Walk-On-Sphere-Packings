module

-- Built on Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne (commit cf73d6e).
public import SpherePackings.General.Walk.WalkCanonicalStopping
public import SpherePackings.General.Walk.ExcursionSteps

@[expose] public section

/-!
# Canonical stopping support from excursion ranges

leobon12's `trajectoryLaw_map_ae_canonicalWalkStoppingSupport` uses a deterministic bound on the
steps of the walk.  Here the steps before the exit are bounded by twice the ranges of the
excursions (`actualWalkStage_step_le_of_range`), so the support property holds on the event that
the excursions `0, …, n` stay within `R` of their starts.
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace SpherePackings.MarkovChain

open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork

variable {d : ℕ} {V J : Type*} [MeasurableSpace V] [MeasurableEq V] [Countable J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

theorem trajectoryLaw_map_ae_canonicalWalkStoppingSupport_of_range (κ : Kernel V V)
    [IsMarkovKernel κ] (pos : V → Euc d) (hpos : Measurable pos) {A : Set V} (B : J → Set V)
    (hB : ∀ j, MeasurableSet (B j)) (hBA : ∀ j, B j ⊆ A) (hA : MeasurableSet A)
    (hexit : ∀ v, ∀ᵐ ω ∂law (absorbedKernel κ hA) v, exitTime A ω ≠ ⊤)
    (initial : J) (select : ℕ → Euc d → Option J) (hs : ∀ n, Measurable (select n))
    (U : Set (Euc d)) (hU : MeasurableSet U) (hselect : ∀ i x, select i x = none → x ∉ U)
    (v : V) (n : ℕ) (R : ℝ) (P : TimePartition n) :
    ∀ᵐ e ∂(law (absorbedKernel κ hA) v).map (actualWalkExcursionSequence pos B initial select),
      (∀ i ≤ n, ClockedWalkExcursion.curve (e i).2 ∈ curveOscillationLe R) →
        (e n).1 = false ∨ e ∈ canonicalWalkStoppingSupport U (2 * R) P := by
  have hflag : MeasurableSet {e : ℕ → Bool × ClockedWalkExcursion d | (e n).1 = false} :=
    measurableSet_eq_fun (measurable_pi_apply n).fst measurable_const
  have hrange : MeasurableSet {e : ℕ → Bool × ClockedWalkExcursion d |
      ∀ i ≤ n, ClockedWalkExcursion.curve (e i).2 ∈ curveOscillationLe R} := by
    have hset : {e : ℕ → Bool × ClockedWalkExcursion d |
        ∀ i ≤ n, ClockedWalkExcursion.curve (e i).2 ∈ curveOscillationLe R} =
        ⋂ i, ⋂ (_ : i ≤ n), (fun e : ℕ → Bool × ClockedWalkExcursion d =>
          ClockedWalkExcursion.curve (e i).2) ⁻¹' curveOscillationLe R := by
      ext e
      simp [Set.mem_iInter]
    rw [hset]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
      (ClockedWalkExcursion.measurable_curve.comp (measurable_pi_apply i).snd)
        (measurableSet_curveOscillationLe R)
  apply (ae_map_iff (measurable_actualWalkExcursionSequence pos B initial select hpos hB
    hs).aemeasurable (hrange.imp (hflag.union
      (measurableSet_canonicalWalkStoppingSupport hU (2 * R) P)))).mpr
  filter_upwards [actualWalkStage_ae_all_clocks_finite κ pos B hBA hA hexit initial
    (fun i v => select i (pos v)) v] with ω hfinite
  intro hR
  by_cases hactive : (actualWalkExcursionSequence pos B initial select ω n).1 = false
  · exact Or.inl hactive
  right
  have hstopped : (actualWalkStage pos B initial (fun i v => select i (pos v)) n ω).2.1 = true :=
    Bool.eq_true_of_not_eq_false hactive
  have hle := actualWalkStage_exit_le_of_stopped pos B initial (fun i v => select i (pos v))
    (pos ⁻¹' U) hpos hB (fun i => (hs i).comp hpos) (fun i v hv => hselect i (pos v) hv) ω n
    (hfinite n) hstopped
  apply canonicalWalkStoppingSupport_actual pos B initial select U n ω (2 * R) (hfinite n) hle
    ?_ P
  intro k hk
  exact actualWalkStage_step_le_of_range pos B initial (fun i v => select i (pos v)) n ω
    (hfinite n) hR k (lt_of_lt_of_le hk (WithTop.untopD_mono (hfinite n) hle))

end SpherePackings.MarkovChain
