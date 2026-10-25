module

/- Nonvacuity examples written by the independent reviewer (Claude Haiku 5.5) of audit batch 13;
   see `AUDIT.md`. They show that the hypothesis bundles named below can hold together. -/
public import BouRabeeGwynne.Upstream.BrownianMotion.Continuity.KolmogorovChentsovInequality
public import BouRabeeGwynne.Upstream.BrownianMotion.Continuity.LimitModification
public import BouRabeeGwynne.EuclideanWienerLaw

@[expose] public section

-- The reviewer's examples, kept as written.
set_option linter.unusedVariables false
set_option linter.deprecated false

namespace SpherePackings.Audit.Nonvacuity13
open BouRabeeGwynne

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal

/-! Nonvacuity examples for batch 13 (audit nonvacuity examples). -/

/-- `[0,1]` has bounded covering number with constant `2` and exponent `1`. -/
theorem nv_covering_Icc : HasBoundedCoveringNumber (Set.Icc (0 : ℝ) 1) 2 1 := by
  refine ⟨by rw [Real.ediam_Icc]; exact ENNReal.ofReal_lt_top, fun ε hε => ?_⟩
  rcases eq_or_ne ε 0 with rfl | hε0
  · rw [ENNReal.coe_zero, ENNReal.inv_zero, ENNReal.top_rpow_of_pos one_pos,
      ENNReal.mul_top two_ne_zero]
    exact le_top
  · have h1 : ε ≤ 1 := by
      have h := hε
      rw [Real.ediam_Icc, sub_zero, ENNReal.ofReal_one] at h
      exact_mod_cast h
    calc (coveringNumber ε (Set.Icc (0 : ℝ) 1) : ℝ≥0∞)
        ≤ 1 / ε := coveringNumber_Icc_zero_one_le_one_div h1
      _ = 1 * (ε : ℝ≥0∞)⁻¹ := by rw [one_div, one_mul]
      _ ≤ 2 * ((ε : ℝ≥0∞)⁻¹ ^ (1 : ℝ)) := by
        rw [ENNReal.rpow_one]
        exact mul_le_mul' (by norm_num) le_rfl

/-- The identity process on `ℝ` over the one-point probability space satisfies the
Kolmogorov condition with `p = q = 2` and `M = 1`. -/
theorem nv_kolmogorov_identity :
    IsKolmogorovProcess (fun (t : ℝ) (_ : Unit) => t) (Measure.dirac ()) 2 2 1 := by
  refine ⟨fun s t => measurable_const, fun s t => ?_, by norm_num, by norm_num⟩
  simp

/-- A countable subset of `[0,1]`. -/
abbrev nvSet : Set ℝ := Set.Icc (0 : ℝ) 1 ∩ Set.range ((↑) : ℚ → ℝ)

/-- The Kolmogorov-Chentsov Hölder finiteness applies to the identity process on `[0,1]`
along the countable set `nvSet`. -/
theorem nv_kc_hypotheses_hold : ∀ᵐ ω ∂(Measure.dirac ()),
    ⨆ (s : ↥nvSet) (t : ↥nvSet),
      edist ((fun (u : ℝ) (_ : Unit) => u) s ω) ((fun (u : ℝ) (_ : Unit) => u) t ω) ^ (2 : ℝ)
        / edist (s : ℝ) (t : ℝ) ^ (((1 / 4 : ℝ≥0) : ℝ) * (2 : ℝ)) < ∞ := by
  have hT' : nvSet.Countable := (Set.countable_range _).mono Set.inter_subset_right
  exact IsKolmogorovProcess.ae_iSup_rpow_edist_div_lt_top nv_covering_Icc nv_kolmogorov_identity
    (by simp) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hT' Set.inter_subset_left

/-- The identity process is a limit of its own indicator process on all of `ℝ` (`A = univ`). -/
theorem nv_limit_of_indicator :
    IsLimitOfIndicator (fun (t : ℝ) (_ : Unit) => t) (fun (t : ℝ) (_ : Unit) => t)
      (Measure.dirac ()) Set.univ := by
  refine ⟨Set.univ, MeasurableSet.univ, Filter.Eventually.of_forall (fun _ => Set.mem_univ _),
    fun t _ ω _ => ⟨t, ?_⟩, fun t _ ω => ?_, fun t ht => absurd (Set.mem_univ t) ht⟩
  · exact tendsto_comap
  · have ht : Tendsto (fun t' : denseCountable ℝ => indicatorProcess
        (fun (u : ℝ) (_ : Unit) => u) Set.univ t' ω) (comap Subtype.val (𝓝 t)) (𝓝 t) := by
      simp only [indicatorProcess_apply, Set.mem_univ, ite_true]
      exact tendsto_comap
    rw [dense_denseCountable.extend_eq_of_tendsto ht, edist_self]

/-- A standard Brownian law on `C([0,∞), ℝ¹)` exists (`BouRabeeGwynne.EuclideanWienerLaw`). -/
example : ∃ μ : Measure (BouRabeeGwynne.BrownianPath 1), BouRabeeGwynne.IsStandardBrownianLaw μ :=
  ⟨_, BouRabeeGwynne.isStandardBrownianLaw_euclideanWienerLaw 1⟩

end SpherePackings.Audit.Nonvacuity13
