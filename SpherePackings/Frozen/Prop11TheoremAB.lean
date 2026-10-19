/-
Proposition 1.1 of rw-spheres.tex, "in particular" clause, frozen.

Paper statement, `rw-spheres.tex:378-380`: the conclusions of Theorem B and, if `U` is Lipschitz,
of Theorem A hold for the graphs `G_Vor(Λ_m)` as `m → ∞`, almost surely.

Formalized: almost surely there is a sequence of orthogonal tilings of a neighbourhood `D` of
`closure U` that eventually is the Voronoi tiling of `Λ_m` (its vertices the points of `Λ_m` whose
cells meet `D`), with the conclusions of Theorem B(a), of Theorem B(b) and of Theorem A for it.
Same correction of (1.4) as in the first part, and only the points in `W` are assumed to form a
Poisson point process, of intensity `m μ|_W`; in addition `Λ_m` has finitely many points in every
bounded set.  Both follow from `Λ_m` being a Poisson point process of intensity `m μ`.
-/
import SpherePackings.Support.Voronoi.PoissonLocal

open MeasureTheory Metric Filter Set SpherePackings SpherePackings.Voronoi BouRabeeGwynne
open scoped ENNReal NNReal Topology

-- FROZEN-STATEMENT-BEGIN
theorem SpherePackings.Frozen.prop11_theoremAB {d : ℕ} (hd : 1 ≤ d) {U : Set (Euc d)} (hU : IsDomain U)
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
                ENNReal.ofReal η)
-- FROZEN-STATEMENT-END
:= SpherePackings.voronoi_tilings_theoremAB_local hd hU hUb hβp hβm hW hUW hμ P Λ hΛ hlf
