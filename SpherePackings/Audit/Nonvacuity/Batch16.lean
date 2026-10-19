/- Nonvacuity examples written by the independent reviewer (Claude Haiku 5.5) of audit batch 16;
   see `AUDIT.md`. They show that the hypothesis bundles named below can hold together. -/
import SpherePackings.General.Walk.DiscreteHarmonicMeasure

-- The reviewer's examples, kept as written.
set_option linter.unusedVariables false
set_option linter.deprecated false

/-! Scratch nonvacuity check for audit batch 16 (not part of the repository).

A two-state chain on `Bool` that swaps its states, absorbed outside `A = {false}`, satisfies the
hypothesis bundle of `SpherePackings.MarkovChain.integral_discreteHarmonicMeasure_of_solvesDirichlet`
(almost sure finite exit, measurable and bounded solution, `SolvesDirichlet`), and the conclusion
then gives a nontrivial value. -/

open MeasureTheory ProbabilityTheory Set
open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork BouRabeeGwynne.TrajectoryCoupling
open SpherePackings.MarkovChain

/-- The swap kernel: `swapKernel b` is the point mass at `!b`. -/
noncomputable abbrev swapKernel : Kernel Bool Bool :=
  Kernel.deterministic (fun b : Bool => !b) (measurable_of_countable _)

lemma swap_A_measurable : MeasurableSet ({false} : Set Bool) := measurableSet_singleton false

/-- The absorbed chain from every start has second state `true` almost surely. -/
lemma swap_absorbed_eval_one (v : Bool) :
    ∀ᵐ ω ∂law (absorbedKernel swapKernel swap_A_measurable) v, ω 1 = true := by
  have hdirac : absorbedKernel swapKernel swap_A_measurable v = Measure.dirac true := by
    cases v with
    | false =>
      rw [absorbedKernel_of_mem swapKernel swap_A_measurable (mem_singleton false)]
      simp [Kernel.deterministic_apply]
    | true =>
      rw [absorbedKernel_of_not_mem swapKernel swap_A_measurable
        (by simp : true ∉ ({false} : Set Bool))]
  have hmap := law_map_eval_one (absorbedKernel swapKernel swap_A_measurable) v
  rw [hdirac] at hmap
  have hae : ∀ᵐ x ∂(law (absorbedKernel swapKernel swap_A_measurable) v).map
      (fun ω : ℕ → Bool => ω 1), x = true := by
    rw [hmap]
    exact (MeasureTheory.ae_dirac_iff (measurableSet_singleton true)).mpr rfl
  exact MeasureTheory.ae_of_ae_map (measurable_pi_apply 1).aemeasurable hae

lemma swap_exit_ne_top (v : Bool) :
    ∀ᵐ ω ∂law (absorbedKernel swapKernel swap_A_measurable) v,
      exitTime {false} ω ≠ ⊤ := by
  filter_upwards [swap_absorbed_eval_one v] with ω hω
  have hle : exitTime {false} ω ≤ ((1 : ℕ) : WithTop ℕ) :=
    (exitTime_le_iff {false} ω 1).mpr ⟨1, le_rfl, by simp [hω]⟩
  exact ne_top_of_le_ne_top WithTop.coe_ne_top hle

/-- Boundary data `g` (equal to `2` at `true`). -/
noncomputable def swapBoundary : Bool → ℝ := fun b => if b = true then 2 else 0

lemma swap_solvesDirichlet :
    SolvesDirichlet swapKernel {false} ({false} : Set Bool)ᶜ swapBoundary (fun _ => 2) := by
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · have ha' : a = false := ha
    subst ha'
    refine ⟨integrable_const 2, ?_⟩
    simp [Kernel.deterministic_apply]
  · have hb' : b = true := by simpa using hb
    subst hb'
    simp [swapBoundary]

/-- The bundle of the discrete harmonic measure theorem holds for the swap chain, and the
conclusion gives the value `2` at the start `false`. -/
theorem swap_harmonic_integral : ∫ w, swapBoundary w ∂(SpherePackings.MarkovChain.discreteHarmonicMeasure swapKernel
    {false} swap_A_measurable false) = 2 :=
  integral_discreteHarmonicMeasure_of_solvesDirichlet swapKernel {false} swap_A_measurable
    swap_exit_ne_top (measurable_of_countable _) measurable_const ⟨2, fun _ => by norm_num⟩
    swap_solvesDirichlet false

#print axioms swap_harmonic_integral
