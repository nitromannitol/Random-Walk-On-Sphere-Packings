module

-- Built on Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne (commit cf73d6e).
public import BouRabeeGwynne.DualCoverage
public import BouRabeeGwynne.DualNull
public import BouRabeeGwynne.LocalRegion
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section

/-!
# Lemma 2.5: dual polytopes cover the cells

`rw-spheres.tex:769-804` (label `lemma:easy-global-qe-bounds`).  Corrected: the printed lower
inclusion `U ⊆ ⋃_{e ∈ E[Ū]} Q_e` fails (a small ball inside one square of the unit square grid
contains no vertex, so the union is empty; at a cell with an unshared facet the dual polytopes do not
cover the cell).  What holds is the coverage of the cells of `V[U]`, when they lie in the interior of
the ambient set, by `⋃_{e ∈ E[Ū]} Q_e` (`dual_coverage_natural`).  By leobon12's decomposition
(`cell_eq_insert_iUnion_cellPyramids`) a cell is covered by its vertex and the pyramids
`conv(v, P_v ∩ P_w)` over all its contacts; the vertex and the pyramids over contacts of dimension
less than `d - 1` are Lebesgue-null, and the pyramids over the facets are finitely many compact sets,
so their union is closed and contains the dense rest of the cell.  The upper inclusion
`⋃_{e ∈ E[Ū]} Q_e ⊆ Ĝ_U` holds as printed.
-/

namespace SpherePackings

open BouRabeeGwynne MeasureTheory

/-- Lemma 2.5 with the cells covered by their vertices and the pyramids over all their contacts. -/
theorem dual_coverage {d : ℕ} (T : OrthogonalTiling d) (U : Set (Euc d))
    (hcellD : ∀ v ∈ T.interiorVertices U, (T.cell v).carrier ⊆ interior T.domain) :
    (⋃ v ∈ T.interiorVertices U, (T.cell v).carrier) ⊆
      T.pos '' T.interiorVertices U ∪
        ⋃ v ∈ T.interiorVertices U, ⋃ w ∈ T.toTilingData.touchingCells v,
          T.toTilingData.cellPyramid v w ∧
    (⋃ v ∈ T.interiorVertices U, ⋃ w ∈ T.neighbors v, T.toTilingData.dualPolytope v w) ⊆
      ⋃ v ∈ T.closedVertices U, (T.cell v).carrier := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨v, hv, hxv⟩ := Set.mem_iUnion₂.mp hx
    rw [T.toTilingData.cell_eq_insert_iUnion_cellPyramids v (hcellD v hv)] at hxv
    rcases Set.mem_insert_iff.mp hxv with rfl | hxv
    · exact Or.inl ⟨v, hv, rfl⟩
    · obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hxv
      exact Or.inr (Set.mem_iUnion₂.mpr ⟨v, hv, Set.mem_iUnion₂.mpr ⟨w, hw, hxw⟩⟩)
  · obtain ⟨v, hv, hx⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨w, hw, hx⟩ := Set.mem_iUnion₂.mp hx
    rcases hx with hx | hx
    · exact Set.mem_iUnion₂.mpr ⟨v, T.interiorVertices_subset_closedVertices U hv,
        T.toTilingData.cellPyramid_subset_cell v w hx⟩
    · exact Set.mem_iUnion₂.mpr ⟨w, T.neighbor_mem_closedVertices hv hw,
        T.toTilingData.cellPyramid_subset_cell w v hx⟩

/-- A convex body with nonempty interior, covered by a closed set together with a Lebesgue-null set,
lies in the closed set: the interior is dense in the body, and an open subset of the interior missing
the closed set is null. -/
private lemma subset_of_subset_union_null {d : ℕ} {K C N : Set (Euc d)} (hconv : Convex ℝ K)
    (hint : (interior K).Nonempty) (hC : IsClosed C) (hN : volume N = 0) (hcov : K ⊆ C ∪ N) :
    K ⊆ C := by
  have hdense : interior K ⊆ closure C := by
    intro x hx
    rw [Metric.mem_closure_iff]
    intro ε hε
    by_contra hcon
    have hcon' : ∀ y ∈ C, ε ≤ dist x y := fun y hy => not_lt.mp (fun h => hcon ⟨y, hy, h⟩)
    have hOopen : IsOpen (Metric.ball x ε ∩ interior K) :=
      Metric.isOpen_ball.inter isOpen_interior
    have hOne : (Metric.ball x ε ∩ interior K).Nonempty :=
      ⟨x, Metric.mem_ball_self hε, hx⟩
    have hpos : 0 < volume (Metric.ball x ε ∩ interior K) :=
      IsOpen.measure_pos volume hOopen hOne
    have hOsub : Metric.ball x ε ∩ interior K ⊆ N := by
      rintro y ⟨hyb, hyi⟩
      rcases hcov (interior_subset hyi) with hyC | hyN
      · have hxy : dist x y < ε := by
          rw [dist_comm]
          exact hyb
        exact absurd (hcon' y hyC) (not_le.mpr hxy)
      · exact hyN
    exact hpos.ne' (measure_mono_null hOsub hN)
  have hint' : interior K ⊆ C := by
    rw [← hC.closure_eq]
    exact hdense
  calc K ⊆ closure K := subset_closure
    _ = closure (interior K) := (hconv.closure_interior_eq_closure_of_nonempty_interior hint).symm
    _ ⊆ C := closure_minimal hint' hC

/-- The cell statement at the level of the underlying tiling data. -/
private lemma cell_subset_iUnion_dualPolytope_tilingData {d : ℕ} (hd : 1 ≤ d) (TD : TilingData d)
    (v : TD.V) (hvD : (TD.cell v).carrier ⊆ interior TD.domain) :
    (TD.cell v).carrier ⊆ ⋃ w ∈ {w | TD.adj v w}, TD.dualPolytope v w := by
  have hvD' : (TD.cell v).carrier ⊆ TD.domain := hvD.trans interior_subset
  have hfin : (TD.touchingCells v).Finite := TD.touchingCells_finite v hvD'
  have hm : (μHE[d] : Measure (Euc d)) = volume := by
    simpa using InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := Euc d)
  -- the contacts which are edges of the graph, their pyramids, and the remaining contacts
  set G : Set TD.V := {w | w ∈ TD.touchingCells v ∧ TD.adj v w} with hG
  set C : Set (Euc d) := ⋃ w ∈ G, TD.cellPyramid v w with hC
  set N : Set (Euc d) := {TD.pos v} ∪ ⋃ w ∈ TD.touchingCells v \ G, TD.cellPyramid v w with hN
  have hCclosed : IsClosed C :=
    (hfin.subset (fun w hw => hw.1)).isClosed_biUnion
      (fun w _ => (TD.cellPyramid_compact v w).isClosed)
  have hcov : (TD.cell v).carrier ⊆ C ∪ N := by
    intro x hx
    rw [TD.cell_eq_insert_iUnion_cellPyramids v hvD] at hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact Or.inr (Or.inl rfl)
    · obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx
      by_cases hadj : TD.adj v w
      · have hwG : w ∈ G := ⟨hw, hadj⟩
        exact Or.inl (Set.mem_iUnion₂.mpr ⟨w, hwG, hxw⟩)
      · have hwN : w ∈ TD.touchingCells v \ G := ⟨hw, fun h => hadj h.2⟩
        exact Or.inr (Or.inr (Set.mem_iUnion₂.mpr ⟨w, hwN, hxw⟩))
  have hsing : μHE[d] {TD.pos v} = 0 := by
    have : NeZero d := ⟨by omega⟩
    rw [hm]
    exact measure_singleton _
  have hbig : μHE[d] (⋃ w ∈ TD.touchingCells v \ G, TD.cellPyramid v w) = 0 := by
    rw [measure_biUnion_null_iff (hfin.subset Set.sdiff_subset).countable]
    intro w hw
    obtain ⟨⟨hwv, hne⟩, hnotG⟩ := hw
    have hnot : ¬ TD.adj v w := fun h => hnotG ⟨⟨hwv, hne⟩, h⟩
    exact TD.cellPyramid_measure_zero_of_nonadjacent_contact hd hwv.symm hne hnot
  have hN0 : volume N = 0 := by
    rw [← hm]
    exact measure_union_null hsing hbig
  have hK : (TD.cell v).carrier ⊆ C :=
    subset_of_subset_union_null (TD.cell v).convex (TD.cell v).interior_nonempty hCclosed hN0 hcov
  intro x hx
  obtain ⟨w, ⟨-, hadj⟩, hxw⟩ := Set.mem_iUnion₂.mp (hK hx)
  exact Set.mem_iUnion₂.mpr ⟨w, hadj, Or.inl hxw⟩

/-- A cell in the interior of the ambient set is covered by the dual polytopes of its edges. -/
theorem cell_subset_iUnion_dualPolytope {d : ℕ} (hd : 1 ≤ d) (T : OrthogonalTiling d) (v : T.V)
    (hvD : (T.cell v).carrier ⊆ interior T.domain) :
    (T.cell v).carrier ⊆ ⋃ w ∈ T.neighbors v, T.toTilingData.dualPolytope v w :=
  cell_subset_iUnion_dualPolytope_tilingData hd T.toTilingData v hvD

/-- **Lemma 2.5** (`lemma:easy-global-qe-bounds`), corrected: the cells of `V[U]`, when they lie in
the interior of the ambient set, are covered by `⋃_{e ∈ E[Ū]} Q_e`, which lies in `Ĝ_U`. -/
theorem dual_coverage_natural {d : ℕ} (hd : 1 ≤ d) (T : OrthogonalTiling d) (U : Set (Euc d))
    (hcellD : ∀ v ∈ T.interiorVertices U, (T.cell v).carrier ⊆ interior T.domain) :
    (⋃ v ∈ T.interiorVertices U, (T.cell v).carrier) ⊆
      ⋃ v ∈ T.interiorVertices U, ⋃ w ∈ T.neighbors v, T.toTilingData.dualPolytope v w ∧
    (⋃ v ∈ T.interiorVertices U, ⋃ w ∈ T.neighbors v, T.toTilingData.dualPolytope v w) ⊆
      ⋃ v ∈ T.closedVertices U, (T.cell v).carrier := by
  refine ⟨fun x hx => ?_, (SpherePackings.dual_coverage T U hcellD).2⟩
  obtain ⟨v, hv, hxv⟩ := Set.mem_iUnion₂.mp hx
  exact Set.mem_iUnion₂.mpr ⟨v, hv, cell_subset_iUnion_dualPolytope hd T v (hcellD v hv) hxv⟩

end SpherePackings
