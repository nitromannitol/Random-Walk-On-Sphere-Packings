import SpherePackingsAudit.Vocabulary.BouRabeeGwynne.StoppedCurveLaws
import SpherePackingsAudit.Vocabulary.BouRabeeGwynne.Approximation
import SpherePackingsAudit.Vocabulary.BouRabeeGwynne.LipschitzDomain

/-!
# Comparator challenge: Theorem A (`theorem:convergence-of-rw-trace`)

This file imports only Mathlib and the vocabulary modules of `SpherePackingsAudit/Vocabulary/`,
which copy verbatim, under their repository names, the repository declarations needed to read the
statement (`python3 tools/check_vocabulary.py`).  It ends with one `sorry`, the proof being checked.
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
            ENNReal.ofReal η := by
  sorry

end SpherePackingsAudit
