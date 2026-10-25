module

/- Nonvacuity examples written by the independent reviewer (Claude Haiku 5.5) of audit batch 17;
   see `AUDIT.md`. They show that the hypothesis bundles named below can hold together. -/
public import SpherePackings.General.Walk.WalkBrownianActiveTransfer
public import BouRabeeGwynne.EuclideanWienerLaw

@[expose] public section

-- The reviewer's examples, kept as written.
set_option linter.unusedVariables false
set_option linter.deprecated false

/-! Nonvacuity for the General-chain hypothesis bundle of
`SpherePackings.MarkovChain.trajectoryLaw_walkActive_le_brownianActive_add_failure`:
the two-point chain `κ x = dirac 1` on `Fin 2`, absorbing set `A = {0}`, one ball `B = A`,
`d = 1`, the standard Wiener law, and the single trivial cell `univ` at every level. -/

open MeasureTheory ProbabilityTheory Set Metric
open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork
open SpherePackings.MarkovChain

namespace SpherePackings.Audit17

/-- Every step of the chain goes to `1`. -/
noncomputable def κ2 : Kernel (Fin 2) (Fin 2) := Kernel.const (Fin 2) (Measure.dirac 1)

instance : IsMarkovKernel κ2 := by
  unfold κ2
  infer_instance

/-- The absorbing set. -/
def A2 : Set (Fin 2) := {0}

lemma A2_meas : MeasurableSet A2 := (Set.toFinite _).measurableSet

/-- `hexit` for the absorbed two-point chain: it leaves `A2` at time one, almost surely. -/
theorem hexit_two_point : ∀ v : Fin 2, ∀ᵐ ω ∂law (absorbedKernel κ2 A2_meas) v,
    exitTime A2 ω ≠ ⊤ := by
  intro v
  have hdirac : absorbedKernel κ2 A2_meas v = Measure.dirac 1 := by
    by_cases hv : v ∈ A2
    · rw [absorbedKernel_of_mem κ2 A2_meas hv]
      rfl
    · rw [absorbedKernel_of_not_mem κ2 A2_meas hv]
      have hv1 : v = 1 := by
        fin_cases v
        · exact absurd (by simp [A2]) hv
        · rfl
      rw [hv1]
  have hone : ∀ᵐ ω ∂law (absorbedKernel κ2 A2_meas) v, ω 1 = 1 := by
    have h := law_map_eval_one (absorbedKernel κ2 A2_meas) v
    rw [hdirac] at h
    have hy : ∀ᵐ y ∂((law (absorbedKernel κ2 A2_meas) v).map (fun ω => ω 1)), y = 1 := by
      rw [h, ae_dirac_eq]
      exact Filter.eventually_pure.mpr rfl
    exact (ae_map_iff (measurable_pi_apply 1).aemeasurable (measurableSet_singleton 1)).mp hy
  filter_upwards [hone] with ω hω
  intro htop
  have h1 : exitTime A2 ω ≤ ((1 : ℕ) : WithTop ℕ) :=
    (exitTime_le_iff A2 ω 1).mpr ⟨1, le_rfl, by simp [A2, hω]⟩
  rw [htop] at h1
  simp at h1

/-- The embedding of the two vertices into `ℝ¹`. -/
noncomputable def pos2 : Fin 2 → Euc 1 := fun i => EuclideanSpace.single 0 ((i : ℕ) : ℝ)

lemma pos2_injective : Function.Injective pos2 := by
  intro a b h
  have h0 : ((a : ℕ) : ℝ) = ((b : ℕ) : ℝ) := by
    have := congrArg (fun x : Euc 1 => x 0) h
    simpa [pos2, PiLp.single_apply] using this
  have : (a : ℕ) = (b : ℕ) := by exact_mod_cast h0
  exact Fin.ext this

lemma pos2_measurableEmbedding : MeasurableEmbedding pos2 where
  injective := pos2_injective
  measurable := measurable_from_top
  measurableSet_image' := by
    intro s _
    exact (s.toFinite.image pos2).measurableSet

/-- The discrete σ-algebra on `Option Unit` (every subset is countable). -/
instance : MeasurableSpace (Option Unit) := ⊤

instance : MeasurableSingletonClass (Option Unit) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- The concrete instance of the headline bundle of `WalkBrownianActiveTransfer`. -/
example : True := by
  have h := SpherePackings.MarkovChain.trajectoryLaw_walkActive_le_brownianActive_add_failure
    κ2 (le_refl 1) pos2
    pos2_measurableEmbedding (B := fun _ : Unit => A2) (fun _ => A2_meas)
    (U := fun _ : Unit => Metric.ball (0 : Euc 1) 1) (fun _ => Metric.isOpen_ball)
    (fun _ => Metric.isBounded_ball) (euclideanWienerLaw 1)
    (isStandardBrownianLaw_euclideanWienerLaw 1) (fun _ _ => some ())
    (fun _ => measurable_const) (fun _ => 1) (fun _ _ => Set.univ)
    (fun _ _ => MeasurableSet.univ) (fun _ => fun i j hij => absurd (Subsingleton.elim i j) hij)
    (fun _ => subset_rfl) A2_meas hexit_two_point () 0 0 1 2
  trivial

end SpherePackings.Audit17
