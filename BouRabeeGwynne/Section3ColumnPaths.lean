module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/Section3ColumnPaths.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.Section3ColumnTraversal
public import BouRabeeGwynne.Section3Projection
public import BouRabeeGwynne.Section3GraphPaths
public import BouRabeeGwynne.FacetNull

@[expose] public section

/-! Almost every column has actual adjacent boundary paths and a telescoping bound. -/

open scoped MeasureTheory ENNReal Classical BigOperators
open MeasureTheory

namespace BouRabeeGwynne.TilingData

variable {d : ℕ} (T : TilingData d)

lemma ae_projected_contact_adj (hd : 1 ≤ d) (e : Euc d) (v : T.V)
    (hvD : (T.cell v).carrier ⊆ T.domain) :
    ∀ᵐ y ∂μHE[d - 1], ∀ w, v ≠ w →
      y ∈ hyperplaneProjection e '' T.facet v w → T.adj v w := by
  letI : Fintype (T.touchingCells v) := (T.touchingCells_finite v hvD).fintype
  have heach (w : T.touchingCells v) :
      ∀ᵐ y ∂μHE[d - 1], y ∈ hyperplaneProjection e '' T.facet v w → T.adj v w := by
    by_cases h : T.adj v w
    · exact Filter.Eventually.of_forall (fun _ _ => h)
    · have hnull : μHE[d - 1] (hyperplaneProjection e '' T.facet v w) = 0 := by
        apply le_antisymm _ zero_le
        calc
          _ ≤ μHE[d - 1] (T.facet v w) :=
            lipschitzOne_euclideanHausdorffMeasure_image_le
              (hyperplaneProjection_lipschitz e) _
          _ = 0 := T.facetVolume_eq_zero_of_not_adj hd w.property.1.symm h
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with y hy
      exact fun hmem => False.elim (hy hmem)
  filter_upwards [ae_all_iff.mpr heach] with y hy
  intro w hvw hproj
  obtain ⟨x, hx, hxy⟩ := hproj
  exact hy ⟨w, hvw.symm, ⟨x, hx⟩⟩ ⟨x, hx, hxy⟩

noncomputable def columnGraph (R : Set T.V) (A : Set R) (e y : Euc d) : SimpleGraph R where
  Adj v w := T.adj v w ∧ (v ∈ A ∨ w ∈ A) ∧ y ∈ hyperplaneProjection e '' T.facet v w
  symm := ⟨fun v w h => ⟨T.adj_symm h.1, h.2.1.symm, by simpa only [T.facet_symm w v] using h.2.2⟩⟩
  loopless := ⟨fun v h => h.1.1 rfl⟩

theorem ae_column_boundary_path (hd : 1 ≤ d) (e : Euc d) (he : e ≠ 0)
    (R : Set T.V) [Fintype R] (A : Set R)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    (hcellD : ∀ v ∈ A, (T.cell v).carrier ⊆ interior T.domain) :
    ∀ᵐ y ∂μHE[d - 1], ∀ v : R,
      v ∈ A ∧ y ∈ (T.cell v).projectedBase e he →
      ∃ w : R, ¬ (w ∈ A ∧ y ∈ (T.cell w).projectedBase e he) ∧
        (T.columnGraph R A e y).Reachable v w := by
  have heach (v : A) := T.ae_projected_contact_adj hd e v.val.val
    ((hcellD v.val v.property).trans interior_subset)
  filter_upwards [ae_all_iff.mpr heach] with y hy
  apply boundary_path_of_increasing_neighbor (T.columnGraph R A e y)
    {v | v ∈ A ∧ y ∈ (T.cell v).projectedBase e he}
    (fun v => (T.cell v).upperFiber e he y)
  intro v hv
  have hzv : (T.cell v).upperEndpoint e he y ∈ (T.cell v).carrier :=
    ((T.cell v).mem_line_iff he y _).mpr ⟨hv.2.2.1, hv.2.2.2, le_rfl⟩
  obtain ⟨w, hwv, hcontact, hyw, hscore⟩ :=
    T.exists_touching_upperFiber_gt e he v hv.2 (hcellD v hv.1 hzv)
  have hproj : y ∈ hyperplaneProjection e '' T.facet v w :=
    ⟨_, hcontact, (T.cell v).project_upperEndpoint he hv.2⟩
  have hvw := hy ⟨v, hv.1⟩ w hwv.symm hproj
  exact ⟨⟨w, hneighbors v hv.1 w hvw⟩, ⟨hvw, Or.inl hv.1, hproj⟩, hscore⟩

noncomputable def columnFunction (R : Set T.V) (e : Euc d) (he : e ≠ 0)
    (y : Euc d) (f : T.V → ℝ) : R → ℝ :=
  fun v => if y ∈ (T.cell v).projectedBase e he then f v else 0

lemma columnFunction_variation (R : Set T.V) [Fintype R] (A : Set R)
    (e : Euc d) (he : e ≠ 0) (y : Euc d) (f : T.V → ℝ)
    (a : Sym2 R) (ha : a ∈ (T.columnGraph R A e y).edgeFinset) :
    unorderedEdgeVariation (T.columnFunction R e he y f) a =
      unorderedEdgeVariation (fun v : R => f v) a := by
  induction a using Sym2.inductionOn with
  | hf v w =>
    have hadj := ((T.columnGraph R A e y).mem_edgeSet).mp
      (SimpleGraph.mem_edgeFinset.mp ha)
    obtain ⟨x, hx, hxy⟩ := hadj.2.2
    have hv : y ∈ (T.cell v).projectedBase e he := by
      rw [(T.cell v).projectedBase_eq_image he]
      exact ⟨x, hx.1, hxy⟩
    have hw : y ∈ (T.cell w).projectedBase e he := by
      rw [(T.cell w).projectedBase_eq_image he]
      exact ⟨x, hx.2, hxy⟩
    simp only [unorderedEdgeVariation_mk, columnFunction, hv, hw, ite_true]

/-- The pointwise telescoping part of Lemma 3.1 on almost every actual column.
Each graph edge is counted once, and the function is zero at external vertices. -/
theorem ae_abs_le_column_graph_variation (hd : 1 ≤ d)
    (e : Euc d) (he : e ≠ 0) (R : Set T.V) [Fintype R] (A : Set R)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    (hcellD : ∀ v ∈ A, (T.cell v).carrier ⊆ interior T.domain)
    (f : T.V → ℝ) (hzero : ∀ v : R, v ∉ A → f v = 0) :
    ∀ᵐ y ∂μHE[d - 1], ∀ v : R,
      v ∈ A ∧ y ∈ (T.cell v).projectedBase e he →
      |f v| ≤ ∑ a ∈ (T.columnGraph R A e y).edgeFinset,
        unorderedEdgeVariation (fun w : R => f w) a := by
  filter_upwards [T.ae_column_boundary_path hd e he R A hneighbors hcellD] with y hy
  intro v hv
  have hzero' : ∀ w : R,
      ¬ (w ∈ A ∧ y ∈ (T.cell w).projectedBase e he) →
      T.columnFunction R e he y f w = 0 := by
    intro w hw
    by_cases hproj : y ∈ (T.cell w).projectedBase e he
    · have hwA : w ∉ A := fun h => hw ⟨h, hproj⟩
      simp only [columnFunction, hproj, ite_true, hzero w hwA]
    · simp only [columnFunction, hproj, ite_false]
  have h := abs_le_graph_variation_of_boundary_path (T.columnGraph R A e y)
    {w | w ∈ A ∧ y ∈ (T.cell w).projectedBase e he}
    (T.columnFunction R e he y f) hzero' (hy v hv)
  have hsum : (∑ a ∈ (T.columnGraph R A e y).edgeFinset,
      unorderedEdgeVariation (T.columnFunction R e he y f) a) =
      ∑ a ∈ (T.columnGraph R A e y).edgeFinset,
        unorderedEdgeVariation (fun w : R => f w) a := by
    apply Finset.sum_congr rfl
    exact T.columnFunction_variation R A e he y f
  simpa only [columnFunction, hv.2, ite_true, hsum] using h

end BouRabeeGwynne.TilingData
