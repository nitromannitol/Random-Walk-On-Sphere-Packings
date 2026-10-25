module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/BrownianStoppingEvent.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.BrownianStoppingHistory

@[expose] public section

/-! A uniform bound for fresh Brownian futures transfers to the original
path at its actual stopping time, with the entire observed history retained. -/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace BouRabeeGwynne

theorem standardBrownianLaw_stopping_event_le {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {τ : BrownianPath d → ℝ≥0∞}
    (hτ : IsStoppingTime (brownianNaturalFiltration d) τ)
    (hfinite : ∀ᵐ ω ∂μ, τ ω ≠ ∞)
    {H : Type*} [MeasurableSpace H] {history : BrownianPath d → H}
    (hhistory : Measurable[hτ.measurableSpace] history)
    {A : Set (H × BrownianPath d)} (hA : MeasurableSet A) (ε : ℝ≥0∞)
    (hbound : ∀ᵐ ω ∂μ, μ (Prod.mk (history ω) ⁻¹' A) ≤ ε) :
    μ {ω | (history ω, shiftedBrownianPath (τ ω).toNNReal ω) ∈ A} ≤ ε := by
  letI : IsProbabilityMeasure μ := hμ.1
  have hmH : Measurable history := hhistory.mono hτ.measurableSpace_le le_rfl
  have hmF : Measurable (fun ω => shiftedBrownianPath (τ ω).toNNReal ω) :=
    measurable_variable_shiftedBrownianPath
      (ENNReal.measurable_toNNReal.comp hτ.measurable')
  have hsection : MeasurableSet {x : H | μ (Prod.mk x ⁻¹' A) ≤ ε} :=
    measurableSet_le (measurable_measure_prodMk_left hA) measurable_const
  have hmapbound : ∀ᵐ x ∂μ.map history, μ (Prod.mk x ⁻¹' A) ≤ ε :=
    (ae_map_iff hmH.aemeasurable hsection).mpr hbound
  calc
    _ = (μ.map (fun ω => (history ω, shiftedBrownianPath (τ ω).toNNReal ω))) A :=
      (Measure.map_apply (hmH.prodMk hmF) hA).symm
    _ = ((μ.map history).prod μ) A := by
      rw [standardBrownianLaw_stopping_history_joint hμ hτ hfinite hhistory]
    _ = ∫⁻ x, μ (Prod.mk x ⁻¹' A) ∂μ.map history := Measure.prod_apply hA
    _ ≤ ∫⁻ _ : H, ε ∂μ.map history := lintegral_mono_ae hmapbound
    _ = ε := by rw [lintegral_const, measure_univ, mul_one]

end BouRabeeGwynne
