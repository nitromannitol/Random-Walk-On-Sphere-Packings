module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/Section3ColumnEstimate.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.Section3ColumnEdgeIndex

@[expose] public section

/-! The complete column-measure estimate in facet form, including zero energy. -/

open scoped Classical BigOperators MeasureTheory ENNReal
open MeasureTheory

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

noncomputable def incidentEnergy (R : Set T.V) [Fintype R] (A : Set R)
    (f : T.V → ℝ) : ℝ :=
  ∑ p ∈ T.toTilingData.orientedInteriorEdges R A,
    T.conductanceReal p.1 p.2 * (f p.2 - f p.1) ^ 2

noncomputable def incidentMass (R : Set T.V) [Fintype R] (A : Set R) : ℝ :=
  ∑ p ∈ T.toTilingData.orientedInteriorEdges R A,
    (T.facetVolume p.1 p.2).toReal * ‖T.pos p.2 - T.pos p.1‖

def columnBadSet (R : Set T.V) (A : Set R) (e : Euc d) (he : e ≠ 0)
    (f : T.V → ℝ) (τ : ℝ) : Set (Euc d) :=
  {y | ∃ v : R, v ∈ A ∧ y ∈ (T.cell v).projectedBase e he ∧ τ < |f v|}

lemma columnVariation_nonneg (e : Euc d) (E : Finset (T.V × T.V))
    (f : T.V → ℝ) (y : Euc d) : 0 ≤ T.columnVariation e E f y := by
  apply Finset.sum_nonneg
  intro p _
  simp only [Set.indicator_apply]
  split_ifs
  · exact abs_nonneg _
  · exact le_rfl

lemma ae_abs_le_columnVariation (hd : 1 ≤ d) (e : Euc d) (he : e ≠ 0)
    (R : Set T.V) [Fintype R] (A : Set R)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    (hcellD : ∀ v ∈ A, (T.cell v).carrier ⊆ interior T.domain)
    (f : T.V → ℝ) (hzero : ∀ v : R, v ∉ A → f v = 0) :
    ∀ᵐ y ∂μHE[d - 1], ∀ v : R,
      v ∈ A ∧ y ∈ (T.cell v).projectedBase e he →
      |f v| ≤ T.columnVariation e (T.toTilingData.orientedInteriorEdges R A) f y := by
  filter_upwards [T.toTilingData.ae_abs_le_column_graph_variation hd e he R A
    hneighbors hcellD f hzero] with y hy
  intro v hv
  exact (hy v hv).trans_eq (T.column_graph_variation_eq R A e y f)

/-- The Chebyshev form of Lemma 3.1, on the entire projection hyperplane. -/
theorem column_bad_measure_le (hd : 1 ≤ d) (e : Euc d) (he : e ≠ 0)
    (R : Set T.V) [Fintype R] (A : Set R)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    (hcellD : ∀ v ∈ A, (T.cell v).carrier ⊆ interior T.domain)
    (f : T.V → ℝ) (hzero : ∀ v : R, v ∉ A → f v = 0)
    {τ : ℝ} (hτ : 0 < τ) :
    μHE[d - 1] (T.columnBadSet R A e he f τ) ≤
      ENNReal.ofReal (Real.sqrt (T.incidentEnergy R A f) *
        Real.sqrt (T.incidentMass R A) / τ) := by
  let E := T.toTilingData.orientedInteriorEdges R A
  let F := T.columnVariation e E f
  have hE : ∀ p ∈ E, T.adj p.1 p.2 := T.toTilingData.orientedInteriorEdges_adj R A
  have hF := T.columnVariation_integrable e E hE f
  have hnonneg : 0 ≤ᵐ[μHE[d - 1]] F :=
    Filter.Eventually.of_forall (T.columnVariation_nonneg e E f)
  have hmark : μHE[d - 1] {y | τ < F y} ≤
      ENNReal.ofReal ((∫ y, F y ∂μHE[d - 1]) / τ) := by
    have h := (hF.div_const τ).measure_le_integral
      (hnonneg.mono (fun y hy => div_nonneg hy hτ.le))
      (s := {y | τ < F y}) (fun y hy =>
        (le_div_iff₀ hτ).mpr (by simpa only [one_mul] using hy.le))
    simpa only [integral_div] using h
  have hsubset : ∀ᵐ y ∂μHE[d - 1],
      y ∈ T.columnBadSet R A e he f τ → y ∈ {y | τ < F y} := by
    filter_upwards [T.ae_abs_le_columnVariation hd e he R A hneighbors hcellD f hzero]
      with y hy
    rintro ⟨v, hvA, hyv, hlarge⟩
    exact hlarge.trans_le (hy v ⟨hvA, hyv⟩)
  apply (measure_mono_ae hsubset).trans (hmark.trans _)
  apply ENNReal.ofReal_le_ofReal
  exact div_le_div_of_nonneg_right (T.integral_columnVariation_le_energy e E hE f) hτ.le

/-- Lemma 3.1 with its stated `1/k` bound, including the zero-energy case. -/
theorem column_poincare_measure_bound (hd : 1 ≤ d) (e : Euc d) (he : e ≠ 0)
    (R : Set T.V) [Fintype R] (A : Set R)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    (hcellD : ∀ v ∈ A, (T.cell v).carrier ⊆ interior T.domain)
    (f : T.V → ℝ) (hzero : ∀ v : R, v ∉ A → f v = 0)
    {k : ℝ} (hk : 0 < k) :
    μHE[d - 1] (T.columnBadSet R A e he f
      (k * (Real.sqrt (T.incidentEnergy R A f) * Real.sqrt (T.incidentMass R A)))) ≤
      ENNReal.ofReal (1 / k) := by
  let B := Real.sqrt (T.incidentEnergy R A f) * Real.sqrt (T.incidentMass R A)
  have hBnonneg : 0 ≤ B := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  by_cases hB : 0 < B
  · have h := T.column_bad_measure_le hd e he R A hneighbors hcellD f hzero (mul_pos hk hB)
    have heq : B / (k * B) = 1 / k := by field_simp [hB.ne', hk.ne']
    simpa only [← heq] using h
  · have hBzero : B = 0 := le_antisymm (le_of_not_gt hB) hBnonneg
    let E := T.toTilingData.orientedInteriorEdges R A
    let F := T.columnVariation e E f
    have hE : ∀ p ∈ E, T.adj p.1 p.2 := T.toTilingData.orientedInteriorEdges_adj R A
    have hF := T.columnVariation_integrable e E hE f
    have hnonneg : 0 ≤ᵐ[μHE[d - 1]] F :=
      Filter.Eventually.of_forall (T.columnVariation_nonneg e E f)
    have hint : (∫ y, F y ∂μHE[d - 1]) = 0 := by
      apply le_antisymm _ (integral_nonneg_of_ae hnonneg)
      exact (T.integral_columnVariation_le_energy e E hE f).trans_eq hBzero
    have hzeroF := (integral_eq_zero_iff_of_nonneg_ae hnonneg hF).mp hint
    have hnull : μHE[d - 1] (T.columnBadSet R A e he f (k * B)) = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [T.ae_abs_le_columnVariation hd e he R A hneighbors hcellD f hzero,
        hzeroF] with y hy hFy
      rintro ⟨v, hvA, hyv, hlarge⟩
      have hle := hy v ⟨hvA, hyv⟩
      change |f v| ≤ F y at hle
      change F y = 0 at hFy
      rw [hFy] at hle
      rw [hBzero, mul_zero] at hlarge
      exact (not_lt_of_ge hle) hlarge
    rw [hnull]
    exact zero_le

lemma incidentEnergy_nonneg (R : Set T.V) [Fintype R] (A : Set R)
    (f : T.V → ℝ) : 0 ≤ T.incidentEnergy R A f := by
  apply Finset.sum_nonneg
  intro p _
  exact mul_nonneg (T.conductanceReal_nonneg p.1 p.2) (sq_nonneg _)

lemma incidentMass_nonneg (R : Set T.V) [Fintype R] (A : Set R) :
    0 ≤ T.incidentMass R A := by
  apply Finset.sum_nonneg
  intro p _
  exact mul_nonneg ENNReal.toReal_nonneg (norm_nonneg _)

lemma columnBadSet_mono_threshold (R : Set T.V) (A : Set R)
    (e : Euc d) (he : e ≠ 0) (f : T.V → ℝ) {τ σ : ℝ} (h : τ ≤ σ) :
    T.columnBadSet R A e he f σ ⊆ T.columnBadSet R A e he f τ := by
  rintro y ⟨v, hvA, hyv, hv⟩
  exact ⟨v, hvA, hyv, h.trans_lt hv⟩

/-- The energy-to-columns step of Proposition 3.2. The quantitative energy
estimate is the explicit upstream Proposition 2.6 input. -/
theorem column_poincare_of_energy_bound (hd : 1 ≤ d) (e : Euc d) (he : e ≠ 0)
    (R : Set T.V) [Fintype R] (A : Set R)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    (hcellD : ∀ v ∈ A, (T.cell v).carrier ⊆ interior T.domain)
    (f : T.V → ℝ) (hzero : ∀ v : R, v ∉ A → f v = 0)
    {C k : ℝ} (hC : 0 ≤ C) (hk : 0 < k)
    (henergy : T.incidentEnergy R A f ≤ C ^ 2 * T.incidentMass R A) :
    μHE[d - 1] (T.columnBadSet R A e he f (k * C * T.incidentMass R A)) ≤
      ENNReal.ofReal (1 / k) := by
  have hm := T.incidentMass_nonneg R A
  have hsq : T.incidentEnergy R A f * T.incidentMass R A ≤
      (C * T.incidentMass R A) ^ 2 := by
    calc
      _ ≤ (C ^ 2 * T.incidentMass R A) * T.incidentMass R A :=
        mul_le_mul_of_nonneg_right henergy hm
      _ = _ := by ring
  have hsqrt := Real.sqrt_le_iff.mpr ⟨mul_nonneg hC hm, hsq⟩
  rw [Real.sqrt_mul (T.incidentEnergy_nonneg R A f)] at hsqrt
  have hthreshold : k * (Real.sqrt (T.incidentEnergy R A f) *
      Real.sqrt (T.incidentMass R A)) ≤ k * C * T.incidentMass R A := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsqrt hk.le
  exact (measure_mono (T.columnBadSet_mono_threshold R A e he f hthreshold)).trans
    (T.column_poincare_measure_bound hd e he R A hneighbors hcellD f hzero hk)

end BouRabeeGwynne.OrthogonalTiling
