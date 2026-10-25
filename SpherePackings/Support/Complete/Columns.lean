module

-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (files `BouRabeeGwynne/Section3ColumnTraversal.lean`, `Section3ColumnPaths.lean` and
-- `Section3ColumnEstimate.lean` at commit cf73d6e): the column lemmas, for complete cells.
public import SpherePackings.Support.Complete.Basic
public import SpherePackings.Support.Complete.Fibers
public import BouRabeeGwynne.Section3ColumnEstimate
public import BouRabeeGwynne.FacetNormals
public import BouRabeeGwynne.Section3ParallelFacetProjection

@[expose] public section

/-!
# Columns through complete cells (Lemma 3.1)

leobon12's column lemmas (`BouRabeeGwynne/Section3ColumnTraversal.lean`, `Section3ColumnPaths.lean`,
`Section3ColumnEstimate.lean`) for cells in the interior of the ambient set, re-proved for complete
cells (`CompleteCell`).  Along almost every line, the line leaves a complete cell through the contact
with a neighbour whose segment on the line extends farther (`ae_exists_upper_neighbor`); this gives
the boundary paths of the columns (`rw-spheres-corrected.tex`, Correction 9).
-/

namespace SpherePackings

open BouRabeeGwynne BouRabeeGwynne.OrthogonalTiling MeasureTheory

open scoped Classical

variable {d : ℕ}

/-- Two points of the line `y + ℝ e` differ by a multiple of `e`. -/
private lemma inner_line_sub_eq (n e y : Euc d) (a b : ℝ) :
    inner ℝ n ((y + a • e) - (y + b • e)) = (a - b) * inner ℝ n e := by
  rw [show (y + a • e) - (y + b • e) = (a - b) • e by module, real_inner_smul_right]

/-- Almost every line through a complete cell leaves it through the contact with a neighbour whose
segment on the line extends strictly farther. -/
theorem ae_exists_upper_neighbor (hd : 1 ≤ d) (T : OrthogonalTiling d) {e : Euc d} (he : e ≠ 0)
    {v : T.V} (hv : CompleteCell T v) :
    ∀ᵐ y ∂μHE[d - 1], y ∈ (T.cell v).projectedBase e he →
      ∃ w, T.adj v w ∧ (T.cell v).upperEndpoint e he y ∈ T.facet v w ∧
        y ∈ (T.cell w).projectedBase e he ∧
        (T.cell v).upperFiber e he y < (T.cell w).upperFiber e he y := by
  have hfin := hv.1
  have hfr := hv.frontier_eq
  have ha : ∀ᵐ y ∂μHE[d - 1], y ∈ (T.cell v).projectedBase e he →
      (T.cell v).lowerFiber e he y < (T.cell v).upperFiber e he y :=
    ae_lowerFiber_lt_upperFiber (T.cell v) he
  have hb : ∀ᵐ y ∂μHE[d - 1], ∀ w ∈ T.neighbors v,
      y ∈ (T.cell w).projectedBase e he →
        (T.cell w).lowerFiber e he y < (T.cell w).upperFiber e he y :=
    (Filter.eventually_all_finite hfin).mpr fun w _ => ae_lowerFiber_lt_upperFiber (T.cell w) he
  have hc : ∀ᵐ y ∂μHE[d - 1], ∀ w ∈ T.neighbors v,
      y ∈ hyperplaneProjection e '' T.facet v w → inner ℝ (T.pos w - T.pos v) e ≠ 0 := by
    refine (Filter.eventually_all_finite hfin).mpr fun w hw => ?_
    have hadj : T.adj v w := hw
    by_cases hn : inner ℝ (T.pos w - T.pos v) e = 0
    · have hz := T.projected_parallel_facet_measure_zero e he hadj (by rwa [real_inner_comm])
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with y hy
      exact fun h => (hy h).elim
    · exact Filter.Eventually.of_forall fun _ _ => hn
  filter_upwards [ha, hb, hc] with y hya hyb hyc hy
  have hz : (T.cell v).upperEndpoint e he y ∈ frontier (T.cell v).carrier :=
    (T.cell v).upperEndpoint_mem_frontier he hy
  rw [hfr] at hz
  obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.mp hz
  have hadj : T.adj v w := hw
  have hyv : y ∈ hyperplaneProjection e '' T.facet v w :=
    ⟨_, hzw, (T.cell v).project_upperEndpoint he hy⟩
  have hcne := hyc w hw hyv
  have hwP : y ∈ (T.cell w).projectedBase e he := by
    rw [(T.cell w).projectedBase_eq_image he]
    exact ⟨_, hzw.2, (T.cell v).project_upperEndpoint he hy⟩
  have hbw := hyb w hw hwP
  have hsep := T.facet_normal_separation hd hadj hzw
  have hup : (T.cell v).upperEndpoint e he y = y + (T.cell v).upperFiber e he y • e := rfl
  have hqv : y + (T.cell v).lowerFiber e he y • e ∈ (T.cell v).carrier :=
    ((T.cell v).mem_line_iff he y _).mpr ⟨hy.2.1, le_rfl, hy.2.2⟩
  have hqw : y + (T.cell w).lowerFiber e he y • e ∈ (T.cell w).carrier :=
    ((T.cell w).mem_line_iff he y _).mpr ⟨hwP.2.1, le_rfl, hwP.2.2⟩
  have h1 := hsep.1 _ hqv
  have h2 := hsep.2.1 _ hqw
  rw [hup, inner_line_sub_eq] at h1 h2
  have hlv := hya hy
  have hc0 : 0 ≤ inner ℝ (T.pos w - T.pos v) e := by nlinarith
  have hcpos : 0 < inner ℝ (T.pos w - T.pos v) e := lt_of_le_of_ne hc0 hcne.symm
  have hls : (T.cell v).upperFiber e he y ≤ (T.cell w).lowerFiber e he y := by nlinarith
  exact ⟨w, hadj, hzw, hwP, lt_of_le_of_lt hls hbw⟩

theorem ae_column_boundary_path_of_complete (hd : 1 ≤ d) (T : OrthogonalTiling d) (e : Euc d)
    (he : e ≠ 0) (R : Set T.V) [Fintype R] (A : Set R)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    (hcomplete : ∀ v ∈ A, CompleteCell T v) :
    ∀ᵐ y ∂μHE[d - 1], ∀ v : R,
      v ∈ A ∧ y ∈ (T.cell v).projectedBase e he →
      ∃ w : R, ¬ (w ∈ A ∧ y ∈ (T.cell w).projectedBase e he) ∧
        (T.toTilingData.columnGraph R A e y).Reachable v w := by
  have heach (v : A) := ae_exists_upper_neighbor hd T he (hcomplete v.val v.property)
  filter_upwards [ae_all_iff.mpr heach] with y hy
  apply boundary_path_of_increasing_neighbor (T.toTilingData.columnGraph R A e y)
    {v | v ∈ A ∧ y ∈ (T.cell v).projectedBase e he}
    (fun v => (T.cell v).upperFiber e he y)
  intro v hv
  obtain ⟨w, hvw, hcontact, -, hscore⟩ := hy ⟨v, hv.1⟩ hv.2
  have hproj : y ∈ hyperplaneProjection e '' T.facet v w :=
    ⟨_, hcontact, (T.cell v).project_upperEndpoint he hv.2⟩
  exact ⟨⟨w, hneighbors v hv.1 w hvw⟩, ⟨hvw, Or.inl hv.1, hproj⟩, hscore⟩

/-- The pointwise telescoping part of Lemma 3.1 on almost every column through complete cells. -/
private theorem ae_abs_le_column_graph_variation_of_complete (hd : 1 ≤ d) (T : OrthogonalTiling d)
    (e : Euc d) (he : e ≠ 0) (R : Set T.V) [Fintype R] (A : Set R)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    (hcomplete : ∀ v ∈ A, CompleteCell T v)
    (f : T.V → ℝ) (hzero : ∀ v : R, v ∉ A → f v = 0) :
    ∀ᵐ y ∂μHE[d - 1], ∀ v : R,
      v ∈ A ∧ y ∈ (T.cell v).projectedBase e he →
      |f v| ≤ ∑ a ∈ (T.toTilingData.columnGraph R A e y).edgeFinset,
        unorderedEdgeVariation (fun w : R => f w) a := by
  filter_upwards [ae_column_boundary_path_of_complete hd T e he R A hneighbors hcomplete] with y hy
  intro v hv
  have hzero' : ∀ w : R,
      ¬ (w ∈ A ∧ y ∈ (T.cell w).projectedBase e he) →
      T.toTilingData.columnFunction R e he y f w = 0 := by
    intro w hw
    by_cases hproj : y ∈ (T.cell w).projectedBase e he
    · have hwA : w ∉ A := fun h => hw ⟨h, hproj⟩
      simp only [BouRabeeGwynne.TilingData.columnFunction, hproj, ↓reduceIte, hzero w hwA]
    · simp only [BouRabeeGwynne.TilingData.columnFunction, hproj, ↓reduceIte]
  have h := abs_le_graph_variation_of_boundary_path (T.toTilingData.columnGraph R A e y)
    {w | w ∈ A ∧ y ∈ (T.cell w).projectedBase e he}
    (T.toTilingData.columnFunction R e he y f) hzero' (hy v hv)
  have hsum : (∑ a ∈ (T.toTilingData.columnGraph R A e y).edgeFinset,
      unorderedEdgeVariation (T.toTilingData.columnFunction R e he y f) a) =
      ∑ a ∈ (T.toTilingData.columnGraph R A e y).edgeFinset,
        unorderedEdgeVariation (fun w : R => f w) a := by
    apply Finset.sum_congr rfl
    exact T.toTilingData.columnFunction_variation R A e he y f
  have hfv : T.toTilingData.columnFunction R e he y f v = f v := by
    simp only [BouRabeeGwynne.TilingData.columnFunction, hv.2, ↓reduceIte]
  rw [hsum, hfv] at h
  exact h

theorem ae_abs_le_columnVariation_of_complete (hd : 1 ≤ d) (T : OrthogonalTiling d) (e : Euc d)
    (he : e ≠ 0) (R : Set T.V) [Fintype R] (A : Set R)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    (hcomplete : ∀ v ∈ A, CompleteCell T v)
    (f : T.V → ℝ) (hzero : ∀ v : R, v ∉ A → f v = 0) :
    ∀ᵐ y ∂μHE[d - 1], ∀ v : R,
      v ∈ A ∧ y ∈ (T.cell v).projectedBase e he →
      |f v| ≤ T.columnVariation e (T.toTilingData.orientedInteriorEdges R A) f y := by
  filter_upwards [ae_abs_le_column_graph_variation_of_complete hd T e he R A hneighbors hcomplete
    f hzero] with y hy
  intro v hv
  exact (hy v hv).trans_eq (T.column_graph_variation_eq R A e y f)

theorem column_bad_measure_le_of_complete (hd : 1 ≤ d) (T : OrthogonalTiling d) (e : Euc d)
    (he : e ≠ 0) (R : Set T.V) [Fintype R] (A : Set R)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    (hcomplete : ∀ v ∈ A, CompleteCell T v)
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
    filter_upwards [ae_abs_le_columnVariation_of_complete hd T e he R A hneighbors hcomplete f
      hzero] with y hy
    rintro ⟨v, hvA, hyv, hlarge⟩
    exact hlarge.trans_le (hy v ⟨hvA, hyv⟩)
  apply (measure_mono_ae hsubset).trans (hmark.trans _)
  apply ENNReal.ofReal_le_ofReal
  exact div_le_div_of_nonneg_right (T.integral_columnVariation_le_energy e E hE f) hτ.le

/-- **Lemma 3.1** (`lemma:ptype-inequality`) for complete cells (`rw-spheres-corrected.tex`,
Corrections 4 and 9): columns in any direction `e ≠ 0`, the bad set through projected cells. -/
theorem column_poincare_measure_bound_of_complete (hd : 1 ≤ d) (T : OrthogonalTiling d)
    (e : Euc d) (he : e ≠ 0) (R : Set T.V) [Fintype R] (A : Set R)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    (hcomplete : ∀ v ∈ A, CompleteCell T v)
    (f : T.V → ℝ) (hzero : ∀ v : R, v ∉ A → f v = 0)
    {k : ℝ} (hk : 0 < k) :
    μHE[d - 1] (T.columnBadSet R A e he f
      (k * (Real.sqrt (T.incidentEnergy R A f) * Real.sqrt (T.incidentMass R A)))) ≤
      ENNReal.ofReal (1 / k) := by
  let B := Real.sqrt (T.incidentEnergy R A f) * Real.sqrt (T.incidentMass R A)
  have hBnonneg : 0 ≤ B := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  by_cases hB : 0 < B
  · have h := column_bad_measure_le_of_complete hd T e he R A hneighbors hcomplete f hzero
      (mul_pos hk hB)
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
      filter_upwards [ae_abs_le_columnVariation_of_complete hd T e he R A hneighbors hcomplete f
        hzero, hzeroF] with y hy hFy
      rintro ⟨v, hvA, hyv, hlarge⟩
      have hle := hy v ⟨hvA, hyv⟩
      change |f v| ≤ F y at hle
      change F y = 0 at hFy
      rw [hFy] at hle
      rw [hBzero, mul_zero] at hlarge
      exact (not_lt_of_ge hle) hlarge
    rw [hnull]
    exact zero_le

/-- The energy-to-columns step of Proposition 3.2, for complete cells. -/
theorem column_poincare_of_energy_bound_of_complete (hd : 1 ≤ d) (T : OrthogonalTiling d)
    (e : Euc d) (he : e ≠ 0) (R : Set T.V) [Fintype R] (A : Set R)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    (hcomplete : ∀ v ∈ A, CompleteCell T v)
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
    (column_poincare_measure_bound_of_complete hd T e he R A hneighbors hcomplete f hzero hk)

end SpherePackings
