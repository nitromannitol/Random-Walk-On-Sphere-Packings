module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/Section4BrownianBallHarmonicMeasure.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.Section4BallHarmonicMeasure
public import BouRabeeGwynne.HarmonicNearClosureBrownianExit

@[expose] public section

/-! The actual Brownian endpoint measure and its harmonic boundary approximation. -/

open MeasureTheory ProbabilityTheory
open scoped Topology Classical

namespace BouRabeeGwynne

/-- The actual stopped Brownian endpoint law, as a probability measure. -/
noncomputable def brownianSpatialHarmonicMeasure {d : ℕ}
    (U : Set (Euc d)) (hU : IsOpen U) (μ : Measure (BrownianPath d))
    (hμ : IsStandardBrownianLaw μ) (z : Euc d) : ProbabilityMeasure (Euc d) := by
  letI : IsProbabilityMeasure μ := hμ.1
  letI : IsProbabilityMeasure (stoppedBrownianLaw U z μ) :=
    stoppedBrownianLaw_isProbabilityMeasure hU z μ
  exact ⟨(stoppedBrownianLaw U z μ).map CurveSpace.endPoint,
    (Measure.isProbabilityMeasure_map_iff
      CurveSpace.continuous_endPoint.measurable.aemeasurable).mpr inferInstance⟩

/-- This measure is carried by the actual continuum boundary. -/
theorem brownianSpatialHarmonicMeasure_ae_mem_frontier {d : ℕ} (hd : 1 ≤ d)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {U : Set (Euc d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {z : Euc d} (hz : z ∈ U) :
    ∀ᵐ x ∂(brownianSpatialHarmonicMeasure U hU μ hμ z : Measure (Euc d)),
      x ∈ frontier U :=
  standardBrownianLaw_stopped_endPoint_ae_mem_frontier hd hμ hU hUb hz

/-- An actual harmonic boundary approximant controls the Brownian exit
expectation by its value at the starting point, uniformly in that point. -/
theorem abs_integral_brownianSpatialHarmonicMeasure_sub_le {d : ℕ} (hd : 1 ≤ d)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {U : Set (Euc d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {f h : Euc d → ℝ} (hf : Continuous f) (hcont : Continuous h)
    (hh : HarmonicNearClosure h U) {η : ℝ}
    (hboundary : ∀ x ∈ frontier U, |f x - h x| ≤ η)
    {z : Euc d} (hz : z ∈ U) :
    |(∫ x, f x ∂(brownianSpatialHarmonicMeasure U hU μ hμ z : Measure (Euc d))) -
      h z| ≤ η := by
  have hcompact : IsCompact (frontier U) :=
    hUb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hbound := abs_integral_sub_integral_le_of_ae_mem_compact hcompact
    (brownianSpatialHarmonicMeasure_ae_mem_frontier hd hμ hU hUb hz)
    hf hcont hboundary
  have hrep : (∫ x, h x
      ∂(brownianSpatialHarmonicMeasure U hU μ hμ z : Measure (Euc d))) = h z :=
    standardBrownianLaw_integral_stopped_endPoint_harmonicNearClosure hd hμ hU hUb hh hz
  rwa [hrep] at hbound

end BouRabeeGwynne
