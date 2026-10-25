module

/-
Theorem A of rw-spheres.tex, frozen.

Paper statement, `rw-spheres.tex:259-277` (label `theorem:convergence-of-rw-trace`): for a bounded
Lipschitz domain `U` with `closure U ⊆ D`, orthogonal tilings `G_n` of `D` with (1.3) and one of
(I), (II), (III), the walk started at the nearest vertex `z^n` and stopped on leaving `U` converges in
law to Brownian motion from `z` stopped on leaving `U`, for curves modulo time parametrization (1.2),
uniformly in `z`.

Statement of leobon12 (`BouRabeeGwynne.TheoremAStatement`), with one correction and one reading of
a definition.  The correction is the ambient collar `closure U ⊆ interior D`: the printed
`closure U ⊆ D`, with `D` any set covered by the tiles, is refuted by the square grid of a closed
rectangle that contains two sides of `U`.  The reading is that every codimension-one contact of two
cells is an edge, with orthogonality across it, as in the paper's proof of Lemma 2.2.  Under the
stricter reading, in which `P_v ∩ P_w` must be a whole facet of both cells, rows of squares
staggered by `1/2` would be an orthogonal tiling on which the walk moves only horizontally.  The
conclusion also asserts that the Brownian law and the walk laws exist.
-/
public import BouRabeeGwynne.TheoremAProved

@[expose] public section

open scoped ENNReal Topology
open MeasureTheory BouRabeeGwynne

-- FROZEN-STATEMENT-BEGIN
theorem SpherePackings.Frozen.theoremA :
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
            ENNReal.ofReal η
-- FROZEN-STATEMENT-END
:= BouRabeeGwynne.theoremA_proved
