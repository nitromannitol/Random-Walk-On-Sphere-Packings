/- Nonvacuity examples written by the independent reviewer (Claude Haiku 5.5) of audit batch 14;
   see `AUDIT.md`. They show that the hypothesis bundles named below can hold together. -/
import SpherePackings.Support.Section4.AssumptionD
import SpherePackings.Support.Section4.Theorem41
import SpherePackings.Support.Section4.Prop42
import SpherePackings.Support.Guards.LatticeTilings
import SpherePackings.Support.Guards.LipschitzBall
import BouRabeeGwynne.EuclideanWienerLaw

-- The reviewer's examples, kept as written.
set_option linter.unusedVariables false
set_option linter.deprecated false

namespace SpherePackings.Audit.Nonvacuity14
open BouRabeeGwynne

open MeasureTheory Filter Metric
open BouRabeeGwynne SpherePackings

-- Example 1: the Assumption D bundle is jointly satisfiable with (1.3) and PaperRegularity.
example {d : ℕ} (hd : 1 ≤ d) : ∃ (G : TilingSequence d) (N : NearestVertexData G),
    N.ApproximationCondition ∧ PaperRegularity G ∧ TilingAssumptionD G := by
  obtain ⟨G, -, ⟨N⟩, hN, hII⟩ := exists_lattice_tilingSequence hd
  exact ⟨G, N, hN N, Or.inr (Or.inl hII),
    tilingAssumptionD_of_paperRegularity hd G N (hN N) (Or.inr (Or.inl hII))⟩

-- Example 2: the full hypothesis bundle of Theorem 4.1 on the unit ball is satisfiable, and
-- Theorem 4.1 applied to it produces a standard Brownian law and eventual stopped walk laws.
example {d : ℕ} (hd : 1 ≤ d) : ∃ (G : TilingSequence d) (N : NearestVertexData G),
    ∃ μ : Measure (BrownianPath d), IsStandardBrownianLaw μ ∧
    ∃ walkLaw : ℕ → Euc d → Measure (CurveSpace d),
      ∀ᶠ n in atTop, ∀ z ∈ Metric.ball (0 : Euc d) 1,
        IsStoppedTilingWalkLaw (G.tiling n) (Metric.ball (0 : Euc d) 1) (N.vertex n z)
          (walkLaw n z) := by
  obtain ⟨G, hcol, ⟨N⟩, hN, hII⟩ := exists_lattice_tilingSequence hd
  obtain ⟨μ, hμ, -, walkLaw, hwalk, -⟩ :=
    theorem41_tiling hd G N (Metric.ball (0 : Euc d) 1) (isLipschitzDomain_ball hd)
      Metric.isBounded_ball hcol (hN N)
      (tilingAssumptionD_of_paperRegularity hd G N (hN N) (Or.inr (Or.inl hII)))
  exact ⟨G, N, μ, hμ, walkLaw, hwalk⟩

-- Example 3: the hypotheses of Proposition 4.2 on the unit ball are satisfiable; the statement
-- instantiates with the standard Brownian law `euclideanWienerLaw d`.
example {d : ℕ} (hd : 1 ≤ d) : ∃ (G : TilingSequence d) (N : NearestVertexData G),
    ∃ (μ : Measure (BrownianPath d)) (hμ : IsStandardBrownianLaw μ),
    (∀ K : Set (Euc d), IsCompact K → K ⊆ Metric.ball (0 : Euc d) 1 → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop,
        ∃ hg : (G.tiling n).HasFiniteAccessibleRegion (Metric.ball (0 : Euc d) 1),
          ∀ v : (G.tiling n).V, ∀ hv : v ∈ (G.tiling n).interiorVertices (Metric.ball (0 : Euc d) 1),
            (G.tiling n).pos v ∈ K →
            levyProkhorovDist
              ((G.tiling n).spatialExitProbability (Metric.ball (0 : Euc d) 1) hg v
                ((G.tiling n).interiorVertices_subset_closedVertices _ hv) : Measure (Euc d))
              (brownianSpatialHarmonicMeasure (Metric.ball (0 : Euc d) 1) Metric.isOpen_ball μ hμ
                ((G.tiling n).pos v) : Measure (Euc d)) < ε) := by
  obtain ⟨G, hcol, ⟨N⟩, hN, hII⟩ := exists_lattice_tilingSequence hd
  have hAD := tilingAssumptionD_of_paperRegularity hd G N (hN N) (Or.inr (Or.inl hII))
  have hμ := isStandardBrownianLaw_euclideanWienerLaw d
  exact ⟨G, N, _, hμ, fun K hK hKU ε hε =>
    (prop42_assumptionD hd G N 0 one_pos hcol (hN N) hAD hμ).2 K hK hKU ε hε⟩

end SpherePackings.Audit.Nonvacuity14
