import SpherePackingsAudit.Vocabulary.SpherePackings.Support.Counterexample.WalkLaw

/-!
# Comparator challenge: Theorem 6.1 (`theorem:counter-example`)

This file imports only Mathlib and the vocabulary modules of `SpherePackingsAudit/Vocabulary/`,
which copy verbatim, under their repository names, the repository declarations needed to read the
statement (`python3 tools/check_vocabulary.py`).  It ends with one `sorry`, the proof being checked.
-/

namespace SpherePackingsAudit

open MeasureTheory Metric Filter Set BouRabeeGwynne SpherePackings
open scoped ENNReal NNReal Topology

/-- Theorem 6.1 (`theorem:counter-example`). -/
theorem theorem_6_1 (d : ℕ) (hd : 3 ≤ d) :
    ∃ P : SpherePacking d,
      (∀ i, P.radius i = 1 ∨ P.radius i = 1 / 2) ∧
      (∃ D : ℕ, ∀ i, {j | P.Tangent i j}.Finite ∧ {j | P.Tangent i j}.ncard ≤ D) ∧
      (d = 3 → ∀ i, P.Covered i) ∧
      ∃ i₀ : P.ι, P.center i₀ = 0 ∧
        (∃ walkLaw : ℕ → Measure (CurveSpace d), ∀ n : ℕ, 1 ≤ n →
          P.IsStoppedSRWLaw ((n : ℝ)⁻¹) (ball 0 1) i₀ (walkLaw n)) ∧
        ∀ μ : Measure (BrownianPath d), IsStandardBrownianLaw μ →
        ∀ walkLaw : ℕ → Measure (CurveSpace d),
          (∀ᶠ n : ℕ in atTop, P.IsStoppedSRWLaw ((n : ℝ)⁻¹) (ball 0 1) i₀ (walkLaw n)) →
          ¬ Tendsto (fun n => levyProkhorovEDist (walkLaw n) (stoppedBrownianLaw (ball 0 1) 0 μ))
            atTop (𝓝 0) := by
  sorry

end SpherePackingsAudit
