module

-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/TheoremAProved.lean` at commit cf73d6e), with the regularity hypothesis
-- `PaperRegularity G` replaced by the localized Assumption D `TilingAssumptionD G`.
public import BouRabeeGwynne.TheoremAStatement
public import BouRabeeGwynne.TheoremAProcessLaws
public import SpherePackings.Support.Section4.UniformStoppedWalkConvergence

@[expose] public section

/-! Theorem 4.1 of rw-spheres.tex for the conductance-weighted walk on orthogonal tilings: under
(1.3) and the localized Assumption D, the stopped walks converge to stopped Brownian motion
uniformly over the starting points.  Theorem A is the case where Assumption D comes from
(I), (II) or (III) through Theorem B(a). -/

open MeasureTheory BouRabeeGwynne
open scoped ENNReal Topology

namespace SpherePackings

theorem theorem41_tiling {d : ℕ} (hd : 1 ≤ d) (G : TilingSequence d) (N : NearestVertexData G)
    (U : Set (Euc d)) (hU : IsLipschitzDomain U) (hUb : Bornology.IsBounded U)
    (hUD : HasAmbientCollar U G.domain) (happrox : N.ApproximationCondition)
    (hAD : TilingAssumptionD G) :
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
  obtain ⟨μ, hμ, hBrownian⟩ :=
    exists_standardBrownianLaw_with_stopped_laws hd hU.isDomain.1 hUb
  obtain ⟨walkLaw, hwalk⟩ := N.exists_eventually_stoppedWalkLaws hd U hUb hUD happrox
  refine ⟨μ, hμ, hBrownian, walkLaw, ?_, ?_⟩
  · filter_upwards [hwalk] with n hn
    intro z _
    exact hn z
  · intro η hη
    filter_upwards [hwalk, AssumptionD.eventually_stoppedWalkLaw_levyProkhorov_le hd N
      hU.isDomain.1 hU.hasLipschitzBoundary hUb hUD happrox hAD hμ hη] with n hn hconv
    intro z hz
    exact hconv z hz (walkLaw n z) (hn z)

/-- Theorem A from Theorem 4.1 (rw-spheres.tex lines 1490–1493). -/
theorem theoremA_of_theorem41 : TheoremAStatement := by
  intro d hd G N U hU hUb hUD happrox hreg
  exact theorem41_tiling hd G N U hU hUb hUD happrox
    (tilingAssumptionD_of_paperRegularity hd G N happrox hreg)

end SpherePackings
