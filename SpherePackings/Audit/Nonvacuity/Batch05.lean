module

/- Nonvacuity examples written by the independent reviewer (Claude Haiku 5.5) of audit batch 05;
   see `AUDIT.md`. They show that the hypothesis bundles named below can hold together. -/
public import BouRabeeGwynne.BrownianSkeletonLaw
public import BouRabeeGwynne.BrownianActiveSkeletonTail
public import BouRabeeGwynne.EuclideanWienerLaw

@[expose] public section

-- The reviewer's examples, kept as written.
set_option linter.unusedVariables false
set_option linter.deprecated false

/-! Scratch nonvacuity checks for audit batch 5 (not part of the repository).
Shows that the hypotheses of `standardBrownianLaw_skeleton_map` and of
`standardBrownianLaw_uniform_activeSkeletonTail` are jointly satisfiable
by the standard Wiener law on `ℝ¹`, a ball domain and a concrete selector. -/

open MeasureTheory ProbabilityTheory Set Metric
open scoped NNReal ENNReal unitInterval

namespace SpherePackings.Audit.Nonvacuity05
open BouRabeeGwynne
-- `J = Unit` is countable, so `MeasurableSingletonClass` forces the discrete
-- σ-algebra on `Option Unit`; `⊤` is the discrete one.
instance nvOptionUnitMeasurableSpace : MeasurableSpace (Option Unit) := ⊤

instance nvOptionUnitMeasurableSingleton :
    MeasurableSingletonClass (Option Unit) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

-- The standard Wiener law on `ℝ¹` is a probability measure.
instance nvWienerIsProbability : IsProbabilityMeasure (euclideanWienerLaw 1) :=
  (isStandardBrownianLaw_euclideanWienerLaw 1).1

/-- Select the unique domain `()` near the origin, and stop elsewhere. -/
noncomputable def nvSelector : ℕ → Euc 1 → Option Unit :=
  fun _ x => if ‖x‖ < 3 / 2 then some () else none

lemma nvSelector_measurable (n : ℕ) : Measurable (nvSelector n) :=
  Measurable.ite (measurableSet_lt measurable_norm measurable_const)
    measurable_const measurable_const

/-- The single domain: the open ball of radius `2` about the origin. -/
noncomputable def nvDomain : Unit → Set (Euc 1) := fun _ => ball (0 : Euc 1) 2

lemma nvDomain_open : ∀ j, IsOpen (nvDomain j) := fun _ => isOpen_ball

lemma nvDomain_bounded : ∀ j, Bornology.IsBounded (nvDomain j) :=
  fun _ => isBounded_ball

-- Premises of `standardBrownianLaw_skeleton_map` are satisfied, so its
-- conclusion (equality of the full excursion-sequence law with the Markov
-- trajectory law) is a genuine, non-vacuous statement for this data.
example : (euclideanWienerLaw 1).map
      (fun ω k => brownianSkeletonExcursion nvDomain (0 : Euc 1) () nvSelector k ω) =
    Kernel.trajMeasure (X := fun _ => Bool × C(unitInterval, Euc 1))
      (brownianSkeletonInitialLaw nvDomain nvDomain_open (euclideanWienerLaw 1) 0 ())
      (brownianSkeletonKernel nvDomain nvDomain_open (euclideanWienerLaw 1)
        nvSelector nvSelector_measurable) :=
  standardBrownianLaw_skeleton_map le_rfl (isStandardBrownianLaw_euclideanWienerLaw 1)
    nvDomain nvDomain_open nvDomain_bounded 0 () nvSelector nvSelector_measurable

-- The margin hypothesis of `standardBrownianLaw_uniform_activeSkeletonTail`
-- holds for `nvSelector` with `ε = 1/2` and ambient `V = ball 0 2`, so the
-- uniform active-tail bound applies to a concrete configuration.
example : ∃ K : ℕ, (euclideanWienerLaw 1)
    {ω | (brownianSkeletonClock nvDomain (0 : Euc 1) () nvSelector K ω).1 = false} ≤
      ENNReal.ofReal (1 / 2) := by
  obtain ⟨K, hK⟩ := standardBrownianLaw_uniform_activeSkeletonTail (d := 1) (J := Unit) le_rfl
    (isStandardBrownianLaw_euclideanWienerLaw 1) (V := ball (0 : Euc 1) 2)
    isBounded_ball (ε := 1 / 2) (η := 1 / 2) (by norm_num) (by norm_num)
  refine ⟨K, hK nvDomain nvDomain_open (fun _ => subset_rfl) 0
    (mem_ball_self (by norm_num)) () nvSelector nvSelector_measurable ?_⟩
  intro n x j hx y hy
  unfold nvSelector at hx
  split_ifs at hx with h
  · have h1 : dist y x < 1 / 2 := hy
    have h2 : dist x 0 < 3 / 2 := by rw [dist_zero_right]; exact h
    have h3 := dist_triangle y x (0 : Euc 1)
    show dist y 0 < 2
    linarith
