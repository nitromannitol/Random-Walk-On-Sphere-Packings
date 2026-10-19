-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/HarmonicNearClosureBrownianExit.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.BrownianHarmonicExit
import BouRabeeGwynne.HarmonicCutoff

/-! Brownian harmonic measure represents the original functions harmonic near
the domain closure, with no global smoothness or compact-support hypothesis. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal

namespace BouRabeeGwynne

/-- The actual stopped-curve endpoint law is carried by the domain boundary. -/
theorem standardBrownianLaw_stopped_endPoint_ae_mem_frontier {d : ℕ} (hd : 1 ≤ d)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {U : Set (Euc d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {z : Euc d} (hz : z ∈ U) :
    ∀ᵐ x ∂((stoppedBrownianLaw U z μ).map CurveSpace.endPoint), x ∈ frontier U := by
  rw [stoppedBrownianLaw, Measure.map_map CurveSpace.continuous_endPoint.measurable
    (measurable_stoppedBrownianCurve hU z)]
  apply (ae_map_iff (CurveSpace.continuous_endPoint.measurable.comp
    (measurable_stoppedBrownianCurve hU z)).aemeasurable
    isClosed_frontier.measurableSet).mpr
  filter_upwards [standardBrownianLaw_eval_zero_ae hμ,
    standardBrownianLaw_ae_finiteExit hd hμ hUb z] with ω hzero hfinite
  apply stoppedBrownianCurve_endPoint_mem_frontier hU _ hfinite
  simpa only [hzero, add_zero] using hz

/-- Harmonic exit representation for the exact local harmonicity assumption
used in the paper. The cutoff agrees on an open neighborhood of the closure. -/
theorem standardBrownianLaw_integral_stopped_endPoint_harmonicNearClosure
    {d : ℕ} (hd : 1 ≤ d) {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {U : Set (Euc d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {h : Euc d → ℝ} (hh : HarmonicNearClosure h U) {z : Euc d} (hz : z ∈ U) :
    (∫ x, h x ∂((stoppedBrownianLaw U z μ).map CurveSpace.endPoint)) = h z := by
  obtain ⟨W, hW, hUW, hhW⟩ := hh
  obtain ⟨g, V, _, hUV, _, hg, hgc, _, heq, hgharm⟩ :=
    hhW.exists_compactSupport_eq_near_compact hUb.isCompact_closure hW hUW
  have hUsub : U ⊆ V := subset_closure.trans hUV
  have hgharmU : IsHarmonicOn g U :=
    ⟨hg.contDiffOn, fun x hx => hgharm.laplacian_eq_zero (hUsub hx)⟩
  have heqae : h =ᵐ[((stoppedBrownianLaw U z μ).map CurveSpace.endPoint)] g := by
    filter_upwards [standardBrownianLaw_stopped_endPoint_ae_mem_frontier hd hμ hU hUb hz]
      with x hx
    exact (heq (hUV (frontier_subset_closure hx))).symm
  calc
    _ = ∫ x, g x ∂((stoppedBrownianLaw U z μ).map CurveSpace.endPoint) :=
      integral_congr_ae heqae
    _ = g z := standardBrownianLaw_integral_stopped_endPoint_harmonic_compactSupport
      hd hμ hU hUb hg hgc hgharmU z
    _ = h z := heq (hUsub hz)

end BouRabeeGwynne
