module

public import SpherePackings.MainTheorems

@[expose] public section

/-!
# Solution: Theorem A (`theorem:convergence-of-rw-trace`)

Proves the challenge statement from the repository's main theorem.  The vocabulary constants are
the repository's own declarations, of which the challenge's vocabulary modules are verbatim copies.
-/

namespace SpherePackingsAudit

open scoped ENNReal Topology
open MeasureTheory BouRabeeGwynne

/-- Theorem A (`theorem:convergence-of-rw-trace`). -/
theorem theoremA :
  ∀ (d : ℕ), 1 ≤ d →
  ∀ (G : TilingSequence d) (N : NearestVertexData G) (U : Set (Euc d)),
    IsLipschitzDomain U → Bornology.IsBounded U → HasAmbientCollar U G.domain →
    N.ApproximationCondition → PaperRegularity G →
    ∃ μ : Measure (BrownianPath d),
      IsStandardBrownianLaw μ ∧
      (∀ z ∈ U,
        AEMeasurable (stoppedBrownianCurve U z) μ ∧
        (∀ᵐ ω ∂μ, continuousExitTime U z ω ≠ ∞) ∧
        IsProbabilityMeasure (stoppedBrownianLaw U z μ)) ∧
      ∃ walkLaw : ℕ → Euc d → Measure (CurveSpace d),
        (∀ᶠ n in Filter.atTop, ∀ z ∈ U,
          IsStoppedTilingWalkLaw (G.tiling n) U (N.vertex n z) (walkLaw n z)) ∧
        ∀ η : ℝ, 0 < η → ∀ᶠ n in Filter.atTop, ∀ z ∈ U,
          levyProkhorovEDist (walkLaw n z) (stoppedBrownianLaw U z μ) ≤
            ENNReal.ofReal η :=
  SpherePackings.theorem_A

end SpherePackingsAudit
