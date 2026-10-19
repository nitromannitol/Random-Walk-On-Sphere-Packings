/- Nonvacuity examples written by the independent reviewer (Claude Haiku 5.5) of audit batch 11;
   see `AUDIT.md`. They show that the hypothesis bundles named below can hold together. -/
import BouRabeeGwynne.Section4BallExitConvergence
import BouRabeeGwynne.EuclideanWienerLaw
import BouRabeeGwynne.BrownianBoundaryOscillation
import BouRabeeGwynne.BoundarySurvivalScales
import SpherePackings.Support.Guards.LatticeTilings
import SpherePackings.Support.Guards.LipschitzBall

-- The reviewer's examples, kept as written.
set_option linter.unusedVariables false
set_option linter.deprecated false

namespace SpherePackings.Audit.Nonvacuity11
open BouRabeeGwynne

open MeasureTheory BouRabeeGwynne

/-- Section 4 ball-exit bundle `(G, N, hUD, happrox, hreg, μ)` is jointly satisfiable:
the lattice guard supplies the tiling sequence, nearest vertices with (1.3), the ambient collar
`closure (ball 0 1) ⊆ interior G.domain` and hypothesis (II); the Euclidean Wiener law is the
standard Brownian law. -/
theorem nonvacuous_section4_bundle (d : ℕ) (hd : 1 ≤ d) :
    ∃ (G : TilingSequence d) (N : NearestVertexData G),
      HasAmbientCollar (Metric.ball (0 : Euc d) 1) G.domain ∧
      N.ApproximationCondition ∧ PaperRegularity G ∧
      IsStandardBrownianLaw (euclideanWienerLaw d) := by
  obtain ⟨G, hUD, ⟨N⟩, happrox, hII⟩ := SpherePackings.exists_lattice_tilingSequence hd
  exact ⟨G, N, hUD, happrox N, Or.inr (Or.inl hII), isStandardBrownianLaw_euclideanWienerLaw d⟩

/-- The same bundle feeds the Section 4 theorem `eventually_ball_exit_test_error` with the
constant test function, so its hypotheses are met by actual objects. -/
theorem nonvacuous_section4_applied (d : ℕ) (hd : 1 ≤ d) : True := by
  obtain ⟨G, hUD, ⟨N⟩, happrox, hII⟩ := SpherePackings.exists_lattice_tilingSequence hd
  have _h := eventually_ball_exit_test_error hd G N (0 : Euc d) one_pos hUD (happrox N)
    (Or.inr (Or.inl hII)) (isStandardBrownianLaw_euclideanWienerLaw d)
    (fun _ => (0 : ℝ)) continuous_const one_pos
  trivial

/-- The Lipschitz-domain bundle for the Brownian boundary estimates: the unit ball is a
Lipschitz domain and `euclideanWienerLaw d` is a standard Brownian law. -/
theorem nonvacuous_lipschitz_bundle (d : ℕ) (hd : 1 ≤ d) :
    IsLipschitzDomain (Metric.ball (0 : Euc d) 1) ∧ IsStandardBrownianLaw (euclideanWienerLaw d) :=
  ⟨SpherePackings.isLipschitzDomain_ball hd, isStandardBrownianLaw_euclideanWienerLaw d⟩

/-- The Lipschitz bundle feeds `HasLipschitzBoundary.uniform_brownian_boundary_oscillation`. -/
theorem nonvacuous_boundary_oscillation (d : ℕ) (hd : 1 ≤ d) :
    ∃ a : ℝ, 0 < a := by
  have hL := (SpherePackings.isLipschitzDomain_ball hd).2
  obtain ⟨a, ha, _⟩ := HasLipschitzBoundary.uniform_brownian_boundary_oscillation hd hL
    Metric.isOpen_ball Metric.isBounded_ball (euclideanWienerLaw d)
    (isStandardBrownianLaw_euclideanWienerLaw d) one_pos one_pos
  exact ⟨a, ha⟩

/-- The scalar survival bundle of `exists_boundary_survival_scales` has concrete solutions. -/
theorem nonvacuous_survival_scales :
    ∃ N : ℕ, 0 < N := by
  obtain ⟨N, hN, _⟩ := exists_boundary_survival_scales (q := 1 / 2) (R := 2) (s := 1)
    (κ := 1) (η := 1) (ε := 1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨N, hN⟩

end SpherePackings.Audit.Nonvacuity11
