/- Nonvacuity examples written by the independent reviewer (Claude Haiku 5.5) of audit batch 04;
   see `AUDIT.md`. They show that the hypothesis bundles named below can hold together. -/
import BouRabeeGwynne.BrownianBoundaryExcursion
import BouRabeeGwynne.BrownianHarmonicExit
import BouRabeeGwynne.EuclideanWienerLaw
import SpherePackings.Support.Guards.LipschitzBall
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

-- The reviewer's examples, kept as written.
set_option linter.unusedVariables false
set_option linter.deprecated false

open MeasureTheory Metric InnerProductSpace Laplacian
open scoped NNReal ENNReal

namespace SpherePackings.Audit.Nonvacuity04
open BouRabeeGwynne
/-! Witness 1: the hypothesis bundle of `HasLipschitzBoundary.uniform_brownian_excursion_survival`
(`IsOpen U`, bounded `U`, `HasLipschitzBoundary U`, a probability measure with
`IsStandardBrownianLaw`) is satisfied by the open unit ball of `ℝ²` and the Wiener law. -/

#check HasLipschitzBoundary.uniform_brownian_excursion_survival (d := 2) (by norm_num)
    (SpherePackings.isLipschitzDomain_ball (d := 2) (by norm_num)).hasLipschitzBoundary
    isOpen_ball isBounded_ball (euclideanWienerLaw 2) (isStandardBrownianLaw_euclideanWienerLaw 2)

example := HasLipschitzBoundary.uniform_brownian_excursion_survival (d := 2) (by norm_num)
    (SpherePackings.isLipschitzDomain_ball (d := 2) (by norm_num)).hasLipschitzBoundary
    isOpen_ball isBounded_ball (euclideanWienerLaw 2) (isStandardBrownianLaw_euclideanWienerLaw 2)

/-! Witness 2: the hypotheses of `standardBrownianLaw_integral_exit_harmonic_compactSupport`
(`ContDiff ℝ 2 f`, `HasCompactSupport f`, `IsHarmonicOn f U`) with a NONZERO `f` on `U`. -/

/-- Cutoff: `χ = 1` on `ball 0 2`, support in `closedBall 0 3`. -/
noncomputable def nonvacBump : ContDiffBump (0 : Euc 2) :=
  { rIn := 2, rOut := 3, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }

/-- The linear functional `x ↦ x₀`. -/
noncomputable def nonvacCoord : Euc 2 →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin 2)

/-- Compactly supported `C^∞` test function, equal to `x ↦ x₀` on `ball 0 2`, hence
nonzero on the unit ball and harmonic there. -/
noncomputable def nonvacF : Euc 2 → ℝ := fun x => nonvacBump x * nonvacCoord x

lemma nonvacF_contDiff : ContDiff ℝ 2 nonvacF :=
  (nonvacBump.contDiff.mul nonvacCoord.contDiff)

lemma nonvacF_hasCompactSupport : HasCompactSupport nonvacF :=
  nonvacBump.hasCompactSupport.mul_right

lemma laplacian_nonvacCoord (x : Euc 2) : Δ (fun y => nonvacCoord y) x = 0 := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp [iteratedFDeriv_succ_eq_comp_right]

lemma nonvacF_harmonic : IsHarmonicOn nonvacF (ball (0 : Euc 2) 1) := by
  refine ⟨nonvacF_contDiff.contDiffOn, fun x hx => ?_⟩
  have hx2 : x ∈ ball (0 : Euc 2) 2 := ball_subset_ball (by norm_num) hx
  have hev : nonvacF =ᶠ[nhds x] fun y => nonvacCoord y := by
    filter_upwards [isOpen_ball.mem_nhds hx2] with y hy
    have hy' : y ∈ closedBall (0 : Euc 2) nonvacBump.rIn := by
      have hr : nonvacBump.rIn = 2 := rfl
      rw [hr]
      exact ball_subset_closedBall hy
    simp only [nonvacF, nonvacBump.one_of_mem_closedBall hy', one_mul]
  exact ((laplacian_congr_nhds hev).eq_of_nhds).trans (laplacian_nonvacCoord x)

#check standardBrownianLaw_integral_exit_harmonic_compactSupport (d := 2) (by norm_num)
    (isStandardBrownianLaw_euclideanWienerLaw 2) isOpen_ball isBounded_ball
    nonvacF_contDiff nonvacF_hasCompactSupport nonvacF_harmonic (0 : Euc 2)

end SpherePackings.Audit.Nonvacuity04