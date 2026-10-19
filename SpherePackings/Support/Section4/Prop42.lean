-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (files `BouRabeeGwynne/Section4BallExitConvergence.lean` and
-- `BouRabeeGwynne/Section4BallExitLevyProkhorov.lean` at commit cf73d6e): Proposition 4.2 for tilings.
import SpherePackings.Support.Section4.BallExitLevyProkhorov

/-!
# A partial form of Proposition 4.2 for orthogonal tilings

This is not the registered Proposition 4.2, which is `SpherePackings.prop42_general` (any
nearest-neighbour walk, Assumption D as printed, uniform over the whole ball).

`rw-spheres.tex:1511-1516` (label `prop:convergence-of-harmonic-measure`): under Assumption D the
discrete harmonic measures from a ball converge to the Brownian ones.  For the conductance walk on
orthogonal tilings with (1.3) and the localized Assumption D, on any ball with the ambient collar:
the exit means of every continuous function converge uniformly over the interior vertices, and the
exit laws converge in the Lévy–Prokhorov metric uniformly over the vertices in a compact subset of
the ball.
-/

open MeasureTheory ProbabilityTheory Filter BouRabeeGwynne
open scoped Topology Classical BoundedContinuousFunction

namespace SpherePackings

/-- A partial form of Proposition 4.2 for orthogonal tilings under the localized Assumption D:
the Lévy–Prokhorov bound is uniform only over compact subsets of the ball. -/
theorem prop42_assumptionD {d : ℕ} (hd : 1 ≤ d)
    (G : TilingSequence d) (N : NearestVertexData G) (c : Euc d) {r : ℝ} (hr : 0 < r)
    (hUD : HasAmbientCollar (Metric.ball c r) G.domain)
    (happrox : N.ApproximationCondition) (hAD : TilingAssumptionD G)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) :
    (∀ f : Euc d → ℝ, Continuous f → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∃ hfin : ((G.tiling n).closedVertices (Metric.ball c r)).Finite,
        letI : Fintype ((G.tiling n).closedVertices (Metric.ball c r)) := hfin.fintype
        letI : MeasurableSpace ((G.tiling n).closedVertices (Metric.ball c r)) := ⊤
        ∃ ha : ((G.tiling n).finiteNetwork
            ((G.tiling n).closedVertices (Metric.ball c r))).BoundaryAccessible
            ((G.tiling n).finiteInterior (Metric.ball c r)),
          ∀ v : (G.tiling n).closedVertices (Metric.ball c r),
            v ∈ (G.tiling n).finiteInterior (Metric.ball c r) →
            |(∫ x, f x ∂(G.tiling n).spatialHarmonicMeasure (Metric.ball c r) ha v) -
              ∫ x, f x ∂(brownianSpatialHarmonicMeasure (Metric.ball c r) Metric.isOpen_ball
                μ hμ ((G.tiling n).pos v) : Measure (Euc d))| ≤ ε) ∧
    (∀ K : Set (Euc d), IsCompact K → K ⊆ Metric.ball c r → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop,
        ∃ hg : (G.tiling n).HasFiniteAccessibleRegion (Metric.ball c r),
          ∀ v : (G.tiling n).V, ∀ hv : v ∈ (G.tiling n).interiorVertices (Metric.ball c r),
            (G.tiling n).pos v ∈ K →
            levyProkhorovDist
              ((G.tiling n).spatialExitProbability (Metric.ball c r) hg v
                ((G.tiling n).interiorVertices_subset_closedVertices _ hv) : Measure (Euc d))
              (brownianSpatialHarmonicMeasure (Metric.ball c r) Metric.isOpen_ball μ hμ
                ((G.tiling n).pos v) : Measure (Euc d)) < ε) :=
  ⟨fun f hf _ hε =>
      AssumptionD.eventually_ball_exit_test_error hd G N c hr hUD happrox hAD hμ f hf hε,
    fun _ hK hKU =>
      AssumptionD.eventually_ball_exit_levyProkhorov_error hd G N c hr hUD happrox hAD hμ hK hKU⟩

end SpherePackings
