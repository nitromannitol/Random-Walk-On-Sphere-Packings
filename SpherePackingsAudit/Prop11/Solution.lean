import SpherePackings.MainTheorems

/-!
# Solution: Proposition 1.1 (`prop:min-max-edge-length`), cell bounds

Proves the challenge statement from the repository's main theorem.  The vocabulary constants are
the repository's own declarations, of which the challenge's vocabulary modules are verbatim copies.
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
        cell (Λ m ω) s ⊆ ball s ((m : ℝ) ^ (-1 / (3 * βp))) :=
  SpherePackings.prop_1_1 hd hUb hβp hβm hW hUW hμ P Λ hΛ

end SpherePackingsAudit
