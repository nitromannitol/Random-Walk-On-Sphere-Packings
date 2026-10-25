module

public import SpherePackings.Support.HarmonicPolynomials
public import BouRabeeGwynne.HarmonicNearClosureBrownianExit

@[expose] public section

/-!
# Brownian motion leaves the unit ball symmetrically

The continuum half of the proof of Theorem 6.1 (`rw-spheres.tex:1866-1872`, "Brownian motion
satisfies negation symmetry").  For the exit point `X` of Brownian motion from the unit ball started at
the origin, `E[X₀ + min X₀ 0] < 0`.  Indeed `E[X₀] = 0` and `E[X₀² - X_j²] = 0` (harmonic test
functions), and `|X| = 1`; if `E[min X₀ 0] = 0` then `X₀ ≥ 0`, hence `X₀ = 0`, hence `X_j = 0` for
every `j`, almost surely, which is impossible.
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace SpherePackings

open BouRabeeGwynne

variable {d : ℕ}

/-- The exit-point law of Brownian motion from the unit ball, started at the origin. -/
noncomputable def ballExitLaw (μ : Measure (BrownianPath d)) : Measure (Euc d) :=
  (stoppedBrownianLaw (ball (0 : Euc d) 1) 0 μ).map CurveSpace.endPoint

lemma ballExitLaw_isProbabilityMeasure {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) :
    IsProbabilityMeasure (ballExitLaw μ) := by
  have : IsProbabilityMeasure μ := hμ.1
  have := stoppedBrownianLaw_isProbabilityMeasure (isOpen_ball : IsOpen (ball (0 : Euc d) 1)) 0 μ
  exact (Measure.isProbabilityMeasure_map_iff
    CurveSpace.continuous_endPoint.measurable.aemeasurable).mpr this

lemma ballExitLaw_ae_norm (hd : 1 ≤ d) {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) :
    ∀ᵐ x ∂ballExitLaw μ, ‖x‖ = 1 := by
  have : Nontrivial (Euc d) := by
    have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    infer_instance
  filter_upwards [standardBrownianLaw_stopped_endPoint_ae_mem_frontier hd hμ isOpen_ball
    isBounded_ball (mem_ball_self one_pos)] with x hx
  rw [frontier_ball 0 one_ne_zero, mem_sphere_zero_iff_norm] at hx
  exact hx

/-- Mean of a function harmonic on `ℝ^d` at the exit point. -/
lemma integral_ballExitLaw_of_harmonic (hd : 1 ≤ d) {μ : Measure (BrownianPath d)}
    (hμ : IsStandardBrownianLaw μ) {h : Euc d → ℝ} (hh : IsHarmonicOn h univ) :
    ∫ x, h x ∂ballExitLaw μ = h 0 :=
  standardBrownianLaw_integral_stopped_endPoint_harmonicNearClosure hd hμ isOpen_ball
    isBounded_ball ⟨univ, isOpen_univ, subset_univ _, hh⟩ (mem_ball_self one_pos)

/-- Coordinates are bounded by `1` almost surely under the exit law. -/
lemma ballExitLaw_ae_abs_coord_le (hd : 1 ≤ d) {μ : Measure (BrownianPath d)}
    (hμ : IsStandardBrownianLaw μ) (j : Fin d) : ∀ᵐ x ∂ballExitLaw μ, |x j| ≤ 1 := by
  filter_upwards [ballExitLaw_ae_norm hd hμ] with x hx
  have := PiLp.norm_apply_le x j
  rw [Real.norm_eq_abs, hx] at this
  exact this

lemma integrable_ballExitLaw_of_continuous (hd : 1 ≤ d) {μ : Measure (BrownianPath d)}
    (hμ : IsStandardBrownianLaw μ) {f : Euc d → ℝ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ x : Euc d, ‖x‖ = 1 → |f x| ≤ C) : Integrable f (ballExitLaw μ) := by
  have := ballExitLaw_isProbabilityMeasure hμ
  refine Integrable.of_bound hf.aestronglyMeasurable C ?_
  filter_upwards [ballExitLaw_ae_norm hd hμ] with x hx
  rw [Real.norm_eq_abs]
  exact hC x hx

/-- **Asymmetry test.** `E[X₀ + min X₀ 0] < 0` for the Brownian exit point `X` from the unit ball. -/
theorem integral_ballExitLaw_asymmetry_neg (hd : 1 ≤ d) {μ : Measure (BrownianPath d)}
    (hμ : IsStandardBrownianLaw μ) :
    ∫ x, (x ⟨0, hd⟩ + min (x ⟨0, hd⟩) 0) ∂ballExitLaw μ < 0 := by
  have hP := ballExitLaw_isProbabilityMeasure hμ
  set i₀ : Fin d := ⟨0, hd⟩
  set ρ := ballExitLaw μ with hρ
  have hcoord : ∀ j : Fin d, Integrable (fun x : Euc d => x j) ρ := fun j =>
    integrable_ballExitLaw_of_continuous hd hμ (by fun_prop) fun x hx => by
      have := PiLp.norm_apply_le x j
      rw [Real.norm_eq_abs, hx] at this
      exact this
  have hsq : ∀ j : Fin d, Integrable (fun x : Euc d => x j ^ 2) ρ := fun j =>
    integrable_ballExitLaw_of_continuous hd hμ (by fun_prop) fun x hx => by
      have := PiLp.norm_apply_le x j
      rw [Real.norm_eq_abs, hx] at this
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) this
  have hmin : Integrable (fun x : Euc d => min (x i₀) 0) ρ :=
    integrable_ballExitLaw_of_continuous hd hμ (by fun_prop) fun x hx => by
      have := PiLp.norm_apply_le x i₀
      rw [Real.norm_eq_abs, hx] at this
      rw [abs_le] at this ⊢
      exact ⟨le_min this.1 (by norm_num), (min_le_right _ _).trans (by norm_num)⟩
  have h1 : ∫ x, x i₀ ∂ρ = 0 := by
    rw [hρ, integral_ballExitLaw_of_harmonic hd hμ (isHarmonicOn_coord i₀ univ)]
    rfl
  have h2 : ∀ j, ∫ x, (x i₀ ^ 2 - x j ^ 2) ∂ρ = 0 := fun j => by
    rw [hρ, integral_ballExitLaw_of_harmonic hd hμ (isHarmonicOn_sq_sub_sq i₀ j univ)]
    simp
  rw [integral_add (hcoord i₀) hmin, h1, zero_add]
  -- `min X₀ 0 ≤ 0`; suppose its mean vanishes.
  have hle : ∫ x, min (x i₀) 0 ∂ρ ≤ 0 :=
    integral_nonpos fun x => min_le_right _ _
  refine lt_of_le_of_ne hle fun heq => ?_
  have hmin0 : ∀ᵐ x ∂ρ, min (x i₀) 0 = 0 := by
    have hneg : 0 ≤ᵐ[ρ] fun x => -min (x i₀) 0 := ae_of_all _ fun x => by
      simp only [Pi.zero_apply, neg_nonneg]; exact min_le_right _ _
    have := (integral_eq_zero_iff_of_nonneg_ae hneg hmin.neg).mp (by rw [integral_neg, heq, neg_zero])
    filter_upwards [this] with x hx
    simpa using hx
  have hx0nn : 0 ≤ᵐ[ρ] fun x => x i₀ := by
    filter_upwards [hmin0] with x hx
    show (0 : ℝ) ≤ x i₀
    by_contra hlt
    push Not at hlt
    rw [min_eq_left hlt.le] at hx
    linarith
  have hx0 : ∀ᵐ x ∂ρ, x i₀ = 0 := by
    have := (integral_eq_zero_iff_of_nonneg_ae hx0nn (hcoord i₀)).mp h1
    filter_upwards [this] with x hx
    simpa using hx
  have hsq0 : ∀ j, ∀ᵐ x ∂ρ, x j ^ 2 = 0 := by
    intro j
    have hi : ∫ x, x i₀ ^ 2 ∂ρ = 0 := by
      rw [integral_congr_ae (hx0.mono fun x hx => by simp only [hx] : _ =ᵐ[ρ] fun _ => (0 : ℝ) ^ 2)]
      simp
    have hj : ∫ x, x j ^ 2 ∂ρ = 0 := by
      have := h2 j
      rw [integral_sub (hsq i₀) (hsq j), hi, zero_sub, neg_eq_zero] at this
      exact this
    have := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun x : Euc d => sq_nonneg (x j)) (hsq j)).mp hj
    filter_upwards [this] with x hx
    simpa using hx
  have hall : ∀ᵐ x ∂ρ, ∀ j : Fin d, (x : Euc d) j ^ 2 = 0 := ae_all_iff.mpr hsq0
  have hfalse : ∀ᵐ _x ∂ρ, False := by
    filter_upwards [hall, ballExitLaw_ae_norm hd hμ] with x hx hnorm
    have hx' : x = 0 := by
      ext j
      simpa using hx j
    rw [hx', norm_zero] at hnorm
    exact zero_ne_one hnorm
  obtain ⟨_, h⟩ := hfalse.exists
  exact h

end SpherePackings
