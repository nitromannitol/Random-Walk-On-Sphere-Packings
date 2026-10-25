module

-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/DiscreteHarmonicMeasure.lean` at commit cf73d6e): its declarations that assume a
-- finite state space or a finite conductance network, for the chain of an arbitrary Markov
-- kernel on a measurable space.
public import BouRabeeGwynne.DiscreteHarmonicMeasure
public import SpherePackings.General.MarkovChain.Absorbed
public import SpherePackings.General.Walk.StoppedCurveMeasurable

@[expose] public section

/-! General-state-space version of `BouRabeeGwynne.DiscreteHarmonicMeasure`: the declarations of that file
that assume a finite state space or a finite conductance network. -/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology
namespace SpherePackings.MarkovChain

open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork BouRabeeGwynne.TrajectoryCoupling
variable {V : Type*}  [MeasurableSpace V] [MeasurableEq V]

omit [MeasurableEq V] in
lemma measurable_exitVertex (A : Set V) (hpos : MeasurableSet A) : Measurable (exitVertex A) := by
  have hev : Measurable (fun p : (ℕ → V) × ℕ ↦ p.1 p.2) :=
    measurable_from_prod_countable_left (fun n ↦ measurable_pi_apply n)
  exact hev.comp (measurable_id.prodMk (measurable_stoppedPolygonalDuration hpos))

variable (κ : Kernel V V) [IsMarkovKernel κ]

omit [MeasurableSpace V] [MeasurableEq V] in
lemma IsAbsorbedPath.eventually_eq_exitVertex {A : Set V} {ω : ℕ → V}
    (hω : IsAbsorbedPath A ω) (hτ : exitTime A ω ≠ ⊤) :
    ∀ᶠ n in atTop, ω n = exitVertex A ω := by
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hτ
  have hout : ω m ∉ A := by
    have h := exitVertex_not_mem' hτ
    rw [exitVertex, ← hm] at h
    exact h
  filter_upwards [eventually_ge_atTop m] with n hn
  calc
    ω n = ω (m + (n - m)) := by rw [Nat.add_sub_of_le hn]
    _ = ω m := hω.after_exit hout (n - m)
    _ = exitVertex A ω := by rw [exitVertex, ← hm]; rfl

omit [MeasurableEq V] in
/-- A bounded measurable function that is harmonic at every state has constant expectation
at every time along the chain, from every starting state. -/
lemma integral_eval_of_isHarmonicAt {f : V → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ v, |f v| ≤ C) (hh : ∀ a, IsHarmonicAt κ f a) (n : ℕ) (a : V) :
    ∫ ω, f (ω n) ∂law κ a = f a := by
  induction n generalizing a with
  | zero =>
    have h := integral_map (μ := law κ a)
      (measurable_pi_apply (X := fun _ : ℕ ↦ V) 0).aemeasurable hf.aestronglyMeasurable
    rw [law_map_eval_zero, integral_dirac' _ _ hf.stronglyMeasurable] at h
    exact h.symm
  | succ n ih =>
    have hF : Measurable fun ω : ℕ → V ↦ f (ω n) := hf.comp (measurable_pi_apply n)
    have hshift : ∀ ω : ℕ → V, f (ω (n + 1)) = (fun ω : ℕ → V ↦ f (ω n)) (walkShift 1 ω) :=
      fun ω ↦ by simp only [walkShift, Nat.add_comm n 1]
    rw [show (∫ ω, f (ω (n + 1)) ∂law κ a) =
        ∫ ω, (fun ω : ℕ → V ↦ f (ω n)) (walkShift 1 ω) ∂law κ a from
      integral_congr_ae (ae_of_all _ hshift)]
    rw [integral_walkShift_one κ a hF (fun ω ↦ hC (ω n))]
    simp only [ih]
    exact (hh a).2

/-- Actual discrete harmonic measure is the pushforward by the first exit vertex. -/
noncomputable def discreteHarmonicMeasure (A : Set V)
    (hpos : MeasurableSet A) (v : V) : Measure V :=
  (law (absorbedKernel κ hpos) v).map (exitVertex A)

instance discreteHarmonicMeasure_isProbabilityMeasure (A : Set V)
    (hpos : MeasurableSet A) (v : V) :
    IsProbabilityMeasure (discreteHarmonicMeasure κ A hpos v) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_exitVertex A hpos).aemeasurable).mpr
    inferInstance

/-- The boundary expectation of a Dirichlet solution equals its starting value.
The proof uses finite-time means and dominated convergence after the almost-sure finite exit
`hexit`; no optional-stopping premise is assumed.  The solution is assumed measurable and bounded,
which the finite state space used to provide. -/
theorem integral_discreteHarmonicMeasure_of_solvesDirichlet (A : Set V)
    (hpos : MeasurableSet A) (hexit : ∀ v, ∀ᵐ ω ∂law (absorbedKernel κ hpos) v, exitTime A ω ≠ ⊤)
    {g f : V → ℝ} (hg : Measurable g) (hf : Measurable f) (hfb : ∃ C, ∀ w, |f w| ≤ C)
    (hsol : SolvesDirichlet κ A Aᶜ g f) (v : V) :
    (∫ w, g w ∂discreteHarmonicMeasure κ A hpos v) = f v := by
  obtain ⟨C, hC⟩ := hfb
  let μ := law (absorbedKernel κ hpos) v
  have hharm : ∀ a, IsHarmonicAt (absorbedKernel κ hpos) f a := by
    intro a
    by_cases ha : a ∈ A
    · rw [IsHarmonicAt, absorbedKernel_of_mem κ hpos ha]
      exact hsol.1 a ha
    · rw [IsHarmonicAt, absorbedKernel_of_not_mem κ hpos ha]
      exact ⟨(integrable_const C).mono' hf.aestronglyMeasurable
        (ae_of_all _ fun b ↦ by rw [Real.norm_eq_abs]; exact hC b),
        integral_dirac' _ _ hf.stronglyMeasurable⟩
  have hlimit : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ f (ω n)) atTop
      (𝓝 (g (exitVertex A ω))) := by
    filter_upwards [law_absorbed_ae_absorbed κ hpos v, hexit v] with ω hω hτ
    have heq : ∀ᶠ n in atTop, f (ω n) = g (exitVertex A ω) := by
      filter_upwards [SpherePackings.MarkovChain.IsAbsorbedPath.eventually_eq_exitVertex hω hτ]
        with n hn
      rw [hn, hsol.2 _ (Set.mem_compl (exitVertex_not_mem' hτ))]
    exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm heq)
  have hbound (n : ℕ) : ∀ᵐ ω ∂μ, ‖f (ω n)‖ ≤ C :=
    ae_of_all _ fun ω ↦ by rw [Real.norm_eq_abs]; exact hC (ω n)
  have hint := tendsto_integral_of_dominated_convergence (fun _ : ℕ → V ↦ C)
    (fun n ↦ (hf.comp (measurable_pi_apply n)).aestronglyMeasurable)
    (integrable_const _) hbound hlimit
  have hconst : Tendsto (fun n ↦ ∫ ω, f (ω n) ∂μ) atTop (𝓝 (f v)) := by
    have hfun : (fun n ↦ ∫ ω, f (ω n) ∂μ) = fun _ ↦ f v :=
      funext fun n ↦ integral_eval_of_isHarmonicAt (absorbedKernel κ hpos) hf hC hharm n v
    rw [hfun]
    exact tendsto_const_nhds
  rw [discreteHarmonicMeasure, integral_map (measurable_exitVertex A hpos).aemeasurable
    hg.aestronglyMeasurable]
  exact tendsto_nhds_unique hint hconst

end SpherePackings.MarkovChain
