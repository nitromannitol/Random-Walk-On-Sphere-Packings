/- Nonvacuity examples written by the independent reviewer (Claude Haiku 5.5) of audit batch 03;
   see `AUDIT.md`. They show that the hypothesis bundles named below can hold together. -/
import BouRabeeGwynne.BrownianStoppedStep
import BouRabeeGwynne.BrownianUniformLanding
import BouRabeeGwynne.EuclideanWienerLaw
import BouRabeeGwynne.HarmonicCutoff
import BouRabeeGwynne.PolynomialAnalyticLaplacian

-- The reviewer's examples, kept as written.
set_option linter.unusedVariables false
set_option linter.deprecated false

open MeasureTheory Set Metric
open scoped NNReal ENNReal

namespace SpherePackings.Audit.Nonvacuity03
open BouRabeeGwynne
/-- The standard Brownian predicate used throughout the batch is satisfied by the Wiener law. -/
example (d : ℕ) : IsStandardBrownianLaw (euclideanWienerLaw d) :=
  isStandardBrownianLaw_euclideanWienerLaw d

/-- Unit-time landing hypotheses are satisfied at `d = 2` by the Wiener law. -/
example : ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧ ∀ c : Euc 2, ‖c‖ ≤ 2 →
    ENNReal.ofReal p ≤ euclideanWienerLaw 2 {ω | ω 1 ∈ ball c 1} :=
  standardBrownianLaw_uniform_landing_probability
    (isStandardBrownianLaw_euclideanWienerLaw 2) one_pos

/-- The coordinate `x₀` is a harmonic polynomial on all of `ℝ²`. -/
lemma nv_harmonic_x0 : IsHarmonicOn (polynomialEval (MvPolynomial.X (0 : Fin 2))) univ :=
  isHarmonicOn_polynomialEval_of_laplacian_eq_zero _
    (by simp [polynomialLaplacian, Fin.sum_univ_two]) _

/-- A genuinely nonzero compactly supported `C²` function, harmonic on an open set `V ∋ 0`,
obtained by cutting off `x₀` with the repository's harmonic cutoff. -/
lemma nv_cutoff : ∃ (g : Euc 2 → ℝ) (V : Set (Euc 2)), IsOpen V ∧ (0 : Euc 2) ∈ V ∧
    ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ IsHarmonicOn g V ∧
      g (EuclideanSpace.single 0 (1 / 2 : ℝ)) ≠ 0 := by
  obtain ⟨g, V, hV, hKV, -, hg, hgc, -, heq, hgh⟩ :=
    IsHarmonicOn.exists_compactSupport_eq_near_compact nv_harmonic_x0
      (isCompact_closedBall (0 : Euc 2) 1) isOpen_univ (subset_univ _)
  have hp : (EuclideanSpace.single 0 (1 / 2 : ℝ) : Euc 2) ∈ closedBall (0 : Euc 2) 1 := by
    rw [mem_closedBall, dist_zero_right, EuclideanSpace.norm_single]
    norm_num
  refine ⟨g, V, hV, hKV (mem_closedBall_self zero_le_one), hg, hgc, hgh, ?_⟩
  rw [heq (hKV hp)]
  simp [polynomialEval]

/-- The hypotheses of the one-step stopped harmonic bound are met by a nonzero function
under the Wiener law (the bound gives a constant `C ≥ 0`). -/
example : ∃ C : ℝ, 0 ≤ C := by
  obtain ⟨g, V, hV, hKV, hg, hgc, hgh, hne⟩ := nv_cutoff
  obtain ⟨C, hC, -⟩ := standardBrownianLaw_stopped_harmonic_step_bound
    (isStandardBrownianLaw_euclideanWienerLaw 2) hg hgc hgh one_pos
  exact ⟨C, hC⟩

/-- The global quartic-tail remainder hypothesis of `standardBrownianLaw_taylor_expectation_bound`
holds for a nonzero compactly supported `C²` function, with `ε = 1` at the starting point `0`. -/
example : ∃ (g : Euc 2 → ℝ) (C : ℝ), ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
    g (EuclideanSpace.single 0 (1 / 2 : ℝ)) ≠ 0 ∧ 0 ≤ C ∧ ∀ y : Euc 2,
      |g (0 + y) - g 0 - fderiv ℝ g 0 y - (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ g) 0 y y| ≤
        1 * ‖y‖ ^ 2 + C * ‖y‖ ^ 4 := by
  obtain ⟨g, V, hV, hKV, hg, hgc, hgh, hne⟩ := nv_cutoff
  obtain ⟨C, hC, hR⟩ := uniform_taylor_remainder_of_contDiff_compactSupport hg hgc one_pos
  exact ⟨g, C, hg, hgc, hne, hC, fun y ↦ hR 0 y⟩

end SpherePackings.Audit.Nonvacuity03