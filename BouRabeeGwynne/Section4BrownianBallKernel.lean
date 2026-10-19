-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/Section4BrownianBallKernel.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.Section4BrownianBallHarmonicMeasure
import BouRabeeGwynne.HarmonicPolynomialApproximation

/-! Continuity of the actual Brownian ball-exit probability kernel, obtained
from the same harmonic polynomial boundary approximants as the discrete comparison. -/

open MeasureTheory ProbabilityTheory
open scoped Topology Classical BoundedContinuousFunction

namespace BouRabeeGwynne

/-- The actual Brownian exit law from one fixed ball depends continuously on
its interior starting point in the topology of weak convergence. -/
theorem continuous_brownianBallHarmonicMeasure {d : ℕ} (hd : 1 ≤ d)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (c : Euc d) {r : ℝ} (hr : 0 < r) :
    Continuous (fun z : Metric.ball c r =>
      brownianSpatialHarmonicMeasure (Metric.ball c r) Metric.isOpen_ball μ hμ z) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuous_integral.mpr
  intro f
  let F : Metric.ball c r → ℝ := fun z =>
    ∫ x, f x ∂(brownianSpatialHarmonicMeasure (Metric.ball c r) Metric.isOpen_ball
      μ hμ z : Measure (Euc d))
  change Continuous F
  apply continuous_iff_continuousAt.mpr
  intro z
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  have hthird : 0 < ε / 3 := div_pos hε (by norm_num)
  obtain ⟨P, hP, hnear⟩ := exists_harmonic_polynomial_near_sphere_data hd c hr
    (fun x : Metric.sphere c r => f x) (f.continuous.comp continuous_subtype_val) hthird
  have hcont : Continuous (polynomialEval P) := (contDiff_polynomialEval P (n := 0)).continuous
  have hh : HarmonicNearClosure (polynomialEval P) (Metric.ball c r) :=
    ⟨Set.univ, isOpen_univ, Set.subset_univ _,
      isHarmonicOn_polynomialEval_of_laplacian_eq_zero P hP Set.univ⟩
  have hboundary : ∀ x ∈ frontier (Metric.ball c r),
      |f x - polynomialEval P x| ≤ ε / 3 := by
    intro x hx
    simpa only [abs_sub_comm] using
      (hnear ⟨x, Metric.frontier_ball_subset_sphere hx⟩).le
  have happrox (x : Metric.ball c r) : |F x - polynomialEval P x| ≤ ε / 3 :=
    abs_integral_brownianSpatialHarmonicMeasure_sub_le hd hμ
      Metric.isOpen_ball Metric.isBounded_ball f.continuous hcont hh hboundary x.property
  have hPcont : Continuous (fun x : Metric.ball c r => polynomialEval P x) :=
    hcont.comp continuous_subtype_val
  have hPatz : ContinuousAt (fun x : Metric.ball c r => polynomialEval P x) z :=
    hPcont.continuousAt
  obtain ⟨δ, hδ, hcontrol⟩ := Metric.continuousAt_iff.mp hPatz (ε / 3) hthird
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  rw [Real.dist_eq]
  have hpoly : |polynomialEval P y - polynomialEval P z| < ε / 3 := by
    simpa only [Real.dist_eq] using hcontrol hy
  calc
    _ ≤ |F y - polynomialEval P y| + |polynomialEval P y - F z| := abs_sub_le _ _ _
    _ ≤ |F y - polynomialEval P y| +
        (|polynomialEval P y - polynomialEval P z| + |polynomialEval P z - F z|) :=
      add_le_add le_rfl (abs_sub_le _ _ _)
    _ < ε / 3 + (ε / 3 + ε / 3) :=
      add_lt_add_of_le_of_lt (happrox y)
        (add_lt_add_of_lt_of_le hpoly (by simpa only [abs_sub_comm] using happrox z))
    _ = ε := by ring

end BouRabeeGwynne
