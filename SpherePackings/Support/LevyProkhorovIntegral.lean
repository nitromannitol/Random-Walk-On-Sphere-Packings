module

-- Built on Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne (commit cf73d6e).
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

@[expose] public section

/-!
# Lévy–Prokhorov distance and integrals

A quantitative form of the fact that Lévy–Prokhorov closeness controls integrals of bounded
continuous functions with a given oscillation.
-/

open MeasureTheory Metric Set
open scoped BoundedContinuousFunction

namespace SpherePackings

/-- Shifting an antitone `[0, 1]`-valued function by `δ ≥ 0` changes its integral over
`[0, M]` by at most `δ`. -/
private lemma intervalIntegral_comp_sub_le {h : ℝ → ℝ} (hmono : Antitone h)
    (h0 : ∀ s, 0 ≤ h s) (h1 : ∀ s, h s ≤ 1) {δ M : ℝ} (hδ : 0 ≤ δ) (hM : 0 ≤ M) :
    ∫ t in (0 : ℝ)..M, h (t - δ) ≤ δ + ∫ t in (0 : ℝ)..M, h t := by
  have hneg : ∫ s in (-δ : ℝ)..0, h s ≤ ∫ s in (-δ : ℝ)..0, (1 : ℝ) :=
    intervalIntegral.integral_mono_on (by linarith) hmono.intervalIntegrable
      intervalIntegrable_const fun s _ => h1 s
  calc ∫ t in (0 : ℝ)..M, h (t - δ)
      = ∫ s in (0 - δ : ℝ)..(M - δ), h s := intervalIntegral.integral_comp_sub_right h δ
    _ ≤ ∫ s in (-δ : ℝ)..M, h s :=
        intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
          (Filter.Eventually.of_forall fun s => h0 s) hmono.intervalIntegrable
    _ = (∫ s in (-δ : ℝ)..0, h s) + ∫ s in (0 : ℝ)..M, h s :=
        (intervalIntegral.integral_add_adjacent_intervals hmono.intervalIntegrable
          hmono.intervalIntegrable).symm
    _ ≤ (∫ s in (-δ : ℝ)..0, (1 : ℝ)) + ∫ s in (0 : ℝ)..M, h s := add_le_add hneg le_rfl
    _ = δ + ∫ s in (0 : ℝ)..M, h s := by simp

/-- One-sided bound for a nonnegative bounded continuous function under Lévy–Prokhorov
closeness: `∫ g ∂μ ≤ ∫ g ∂ν + δ + ε ‖g‖`. -/
private lemma integral_le_integral_add_of_nonneg
    {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) (hμν : levyProkhorovEDist μ ν < ENNReal.ofReal ε)
    (g : Ω →ᵇ ℝ) (hg0 : ∀ x, 0 ≤ g x) (hg : ∀ x y, dist x y < ε → |g x - g y| ≤ δ) :
    ∫ x, g x ∂μ ≤ ∫ x, g x ∂ν + δ + ε * ‖g‖ := by
  have hM : 0 ≤ ‖g‖ := norm_nonneg _
  have hnn : (0 : Ω → ℝ) ≤ᵐ[μ] g := Filter.Eventually.of_forall hg0
  have hnnν : (0 : Ω → ℝ) ≤ᵐ[ν] g := Filter.Eventually.of_forall hg0
  have hh_anti : Antitone fun t : ℝ => ν.real {a | t ≤ g a} := fun _ _ hst =>
    measureReal_mono fun _ ha => le_trans hst ha
  have hh0 : ∀ t : ℝ, 0 ≤ ν.real {a | t ≤ g a} := fun _ => measureReal_nonneg
  have hh1 : ∀ t : ℝ, ν.real {a | t ≤ g a} ≤ 1 := fun _ =>
    (measureReal_mono (subset_univ _)).trans probReal_univ.le
  have hA_anti : Antitone fun t : ℝ => ν.real (thickening ε {a | t ≤ g a}) := fun _ _ hst =>
    measureReal_mono (thickening_subset_of_subset ε fun _ ha => le_trans hst ha)
  have hA_le : ∀ t : ℝ, ν.real (thickening ε {a | t ≤ g a}) ≤ ν.real {a | t - δ ≤ g a} := by
    intro t
    refine measureReal_mono fun a ha => ?_
    obtain ⟨b, hb, hab⟩ := mem_thickening_iff.1 ha
    have hb' : t ≤ g b := hb
    have hosc := (abs_le.1 (hg a b hab)).1
    show t - δ ≤ g a
    linarith
  have hshift : ∫ t in (0 : ℝ)..‖g‖, ν.real {a | t - δ ≤ g a}
      ≤ δ + ∫ t in (0 : ℝ)..‖g‖, ν.real {a | t ≤ g a} :=
    intervalIntegral_comp_sub_le hh_anti hh0 hh1 hδ hM
  have hAmono : ∫ t in (0 : ℝ)..‖g‖, ν.real (thickening ε {a | t ≤ g a})
      ≤ ∫ t in (0 : ℝ)..‖g‖, ν.real {a | t - δ ≤ g a} :=
    intervalIntegral.integral_mono_on hM hA_anti.intervalIntegrable
      (hh_anti.comp_monotone (fun _ _ hab => sub_le_sub_right hab δ)).intervalIntegrable
      fun t _ => hA_le t
  have hmain : ∫ x, g x ∂μ
      ≤ (∫ t in (0 : ℝ)..‖g‖, ν.real (thickening ε {a | t ≤ g a})) + ε * ‖g‖ := by
    rw [intervalIntegral.integral_of_le hM]
    exact BoundedContinuousFunction.integral_le_of_levyProkhorovEDist_lt μ ν hε hμν g hnn
  have hlayer : ∫ x, g x ∂ν = ∫ t in (0 : ℝ)..‖g‖, ν.real {a | t ≤ g a} := by
    rw [BoundedContinuousFunction.integral_eq_integral_meas_le g ν hnnν,
      intervalIntegral.integral_of_le hM]
  linarith

/-- If `levyProkhorovEDist μ ν < ε` and `f` oscillates by at most `δ` over pairs of points at
distance less than `ε`, then the integrals of `f` differ by at most `δ + 2 ε ‖f‖`. -/
theorem abs_integral_sub_integral_le_of_levyProkhorovEDist_lt
    {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ε δ : ℝ} (hε : 0 < ε) (hμν : levyProkhorovEDist μ ν < ENNReal.ofReal ε)
    (f : Ω →ᵇ ℝ) (hf : ∀ x y, dist x y < ε → |f x - f y| ≤ δ) :
    |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ δ + 2 * ε * ‖f‖ := by
  have hne : Nonempty Ω := by
    rcases isEmpty_or_nonempty Ω with hΩ | hΩ
    · have h1 := measure_univ (μ := μ)
      rw [Set.univ_eq_empty_iff.mpr hΩ, measure_empty] at h1
      exact absurd h1 zero_ne_one
    · exact hΩ
  obtain ⟨x₀⟩ := hne
  have hδ : 0 ≤ δ := by
    have := hf x₀ x₀ (by rw [dist_self]; exact hε)
    simpa using this
  have hfx : ∀ x, |f x| ≤ ‖f‖ := fun x => by
    have := BoundedContinuousFunction.norm_coe_le_norm f x
    rwa [Real.norm_eq_abs] at this
  -- Shift `f` by the constant `‖f‖` to make it nonnegative.
  let g : Ω →ᵇ ℝ := f + BoundedContinuousFunction.const Ω ‖f‖
  have hg_apply : ∀ x, g x = f x + ‖f‖ := fun x => by simp [g]
  have hg0 : ∀ x, 0 ≤ g x := fun x => by
    rw [hg_apply]
    linarith [neg_abs_le (f x), hfx x]
  have hgosc : ∀ x y, dist x y < ε → |g x - g y| ≤ δ := fun x y hxy => by
    rw [hg_apply, hg_apply, add_sub_add_right_eq_sub]
    exact hf x y hxy
  have hgnorm : ‖g‖ ≤ 2 * ‖f‖ := by
    refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]
    linarith [le_abs_self (f x), hfx x, hg_apply x]
  have hgε : ε * ‖g‖ ≤ 2 * ε * ‖f‖ := by
    calc ε * ‖g‖ ≤ ε * (2 * ‖f‖) := mul_le_mul_of_nonneg_left hgnorm hε.le
      _ = 2 * ε * ‖f‖ := by ring
  have key : ∀ ρ : Measure Ω, [IsProbabilityMeasure ρ] →
      ∫ x, g x ∂ρ = ∫ x, f x ∂ρ + ‖f‖ := fun ρ _ => by
    simp only [hg_apply]
    rw [integral_add (f.integrable ρ) (integrable_const _), integral_const]
    simp
  have h1 := integral_le_integral_add_of_nonneg μ ν hε hδ hμν g hg0 hgosc
  have h2 := integral_le_integral_add_of_nonneg ν μ hε hδ
    (by rw [levyProkhorovEDist_comm]; exact hμν) g hg0 fun x y hxy => by
      rw [abs_sub_comm]
      exact hgosc y x (by rwa [dist_comm])
  rw [key μ, key ν] at h1
  rw [key μ, key ν] at h2
  rw [abs_sub_le_iff]
  constructor <;> linarith

end SpherePackings
