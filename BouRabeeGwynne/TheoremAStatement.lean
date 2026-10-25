module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/TheoremAStatement.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.Approximation
public import BouRabeeGwynne.LipschitzDomain
public import BouRabeeGwynne.StoppedCurveLaws

@[expose] public section

/-!
# Theorem A: the actual mathematical target

This is a proposition to be proved, not a theorem certificate. It states the
paper's random-walk convergence result with the approved ambient-collar repair
`closure U ⊆ interior D`. All measures below are tied to the processes through
their defining laws. There are no free error sequences or assumed convergence
transfers. See `STATEMENT_SPEC.md` for the explicitly approved corrections.
-/

open scoped ENNReal Topology
open MeasureTheory

namespace BouRabeeGwynne

/-- Bou-Rabee--Gwynne Theorem A, with the approved statement repairs.

For orthogonal tilings satisfying (1.3) and one of the geometric alternatives
I/II/III, the actual stopped polygonal conductance-walk laws converge to the
actual stopped standard Brownian laws in the Fréchet curve metric, uniformly
over all starting points in `U`. The conclusion also asserts existence of the
Brownian law, the eventually defined walk laws, finite exit and measurability.

The nearest-vertex selection may be any minimizer; this includes the paper's
lexicographic convention. The discrete curve runs through the first exit vertex
and is constant when its chosen initial vertex is already outside `U`.
-/
def TheoremAStatement : Prop :=
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

end BouRabeeGwynne
