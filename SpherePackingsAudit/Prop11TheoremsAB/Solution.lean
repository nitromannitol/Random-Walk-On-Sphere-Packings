module

public import SpherePackings.MainTheorems

@[expose] public section

/-!
# Solution: Proposition 1.1 (`prop:min-max-edge-length`), Theorems A and B for Poisson–Voronoi tilings

Proves the challenge statement from the repository's main theorem.  The vocabulary constants are
the repository's own declarations, of which the challenge's vocabulary modules are verbatim copies.
-/

namespace SpherePackingsAudit

open MeasureTheory Metric Filter Set BouRabeeGwynne SpherePackings SpherePackings.Voronoi
open scoped ENNReal NNReal Topology

/-- Proposition 1.1 (`prop:min-max-edge-length`), Theorems A and B for Poisson–Voronoi tilings. -/
theorem prop_1_1_theorems_A_B {d : ℕ} (hd : 1 ≤ d) {U : Set (Euc d)} (hU : IsDomain U)
    (hUb : Bornology.IsBounded U) {μ : Measure (Euc d)} {βp βm : ℝ} (hβp : 0 < βp)
    (hβm : 0 < βm) {W : Set (Euc d)} (hW : IsOpen W) (hUW : closure U ⊆ W)
    (hμ : HolderMassBounds μ W βp βm)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Λ : ℕ → Ω → Set (Euc d))
    (hΛ : ∀ m : ℕ, IsPoissonPointProcess P (fun ω => Λ m ω ∩ W) ((m : ℝ≥0∞) • μ.restrict W))
    (hlf : ∀ m ω (B : Set (Euc d)), Bornology.IsBounded B → (Λ m ω ∩ B).Finite) :
    ∀ᵐ ω ∂P, ∃ G : TilingSequence d, HasAmbientCollar U G.domain ∧
      (∀ᶠ m in atTop, IsVoronoiTilingOf (G.tiling m) (Λ m ω) G.domain) ∧
      -- Theorem B(a)
      (∀ hC : Euc d → ℝ, HarmonicNearClosure hC U →
        DirichletApproximationTarget G U hC (fun n v => hC ((G.tiling n).pos v))) ∧
      -- Theorem B(b)
      (IsLipschitzDomain U → ∀ hC : Euc d → ℝ, IsHarmonicOn hC U → ContinuousOnClosure hC U →
        Nonempty (NearestClosureBoundaryChoices G U) ∧
        ∀ S : NearestClosureBoundaryChoices G U,
          (∀ n v, S.point n v ∈ frontier U) ∧
          (∀ᶠ n in atTop, ∀ v : (G.tiling n).boundaryVertices U,
            dist ((G.tiling n).pos v) (S.point n v) ≤ 2 * (G.tiling n).mesh.toReal) ∧
          DirichletApproximationTarget G U hC (S.boundaryData hC)) ∧
      -- Theorem A
      (IsLipschitzDomain U → ∀ N : NearestVertexData G,
        ∃ ν : Measure (BrownianPath d),
          IsStandardBrownianLaw ν ∧
          (∀ z ∈ U,
            AEMeasurable (stoppedBrownianCurve U z) ν ∧
            (∀ᵐ ω ∂ν, continuousExitTime U z ω ≠ ∞) ∧
            IsProbabilityMeasure (stoppedBrownianLaw U z ν)) ∧
          ∃ walkLaw : ℕ → Euc d → Measure (CurveSpace d),
            (∀ᶠ n in atTop, ∀ z ∈ U,
              IsStoppedTilingWalkLaw (G.tiling n) U (N.vertex n z) (walkLaw n z)) ∧
            ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ z ∈ U,
              levyProkhorovEDist (walkLaw n z) (stoppedBrownianLaw U z ν) ≤
                ENNReal.ofReal η) :=
  SpherePackings.prop_1_1_theorems_A_B hd hU hUb hβp hβm hW hUW hμ P Λ hΛ hlf

end SpherePackingsAudit
