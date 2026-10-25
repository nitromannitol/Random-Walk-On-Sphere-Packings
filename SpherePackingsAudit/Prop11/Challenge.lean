module

public import SpherePackingsAudit.Vocabulary.SpherePackings.Support.Voronoi.PoissonCells
public import SpherePackingsAudit.Vocabulary.SpherePackings.Support.Poisson.Basic
public import SpherePackingsAudit.Vocabulary.SpherePackings.Support.Voronoi.Basic

@[expose] public section

/-!
# Comparator challenge: Proposition 1.1 (`prop:min-max-edge-length`), cell bounds

This file imports only Mathlib and the vocabulary modules of `SpherePackingsAudit/Vocabulary/`,
which copy verbatim, under their repository names, the repository declarations needed to read the
statement (`python3 tools/check_vocabulary.py`).  It ends with one `sorry`, the proof being checked.
-/

namespace SpherePackingsAudit

open MeasureTheory Metric Filter Set SpherePackings SpherePackings.Voronoi
open scoped ENNReal NNReal Topology

/-- Proposition 1.1 (`prop:min-max-edge-length`), cell bounds. -/
theorem prop_1_1 {d : ℕ} (hd : 1 ≤ d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hUb : Bornology.IsBounded U) {μ : Measure (EuclideanSpace ℝ (Fin d))} {βp βm : ℝ}
    (hβp : 0 < βp) (hβm : 0 < βm) {W : Set (EuclideanSpace ℝ (Fin d))}
    (hW : IsOpen W) (hUW : closure U ⊆ W) (hμ : HolderMassBounds μ W βp βm)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Λ : ℕ → Ω → Set (EuclideanSpace ℝ (Fin d)))
    (hΛ : ∀ m : ℕ, IsPoissonPointProcess P (fun ω => Λ m ω ∩ W) ((m : ℝ≥0∞) • μ.restrict W)) :
    ∀ᵐ ω ∂P, ∀ᶠ m in atTop, ∀ s ∈ Λ m ω, (cell (Λ m ω) s ∩ U).Nonempty →
      ball s ((m : ℝ) ^ (-8 / βm)) ⊆ cell (Λ m ω) s ∧
        cell (Λ m ω) s ⊆ ball s ((m : ℝ) ^ (-1 / (3 * βp))) := by
  sorry

end SpherePackingsAudit
