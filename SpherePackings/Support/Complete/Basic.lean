module

-- Built on Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne (commit cf73d6e).
public import SpherePackings.Support.Section2.DualCoverage
public import BouRabeeGwynne.PolytopeBoundary
public import BouRabeeGwynne.RadialBoundary

@[expose] public section

/-!
# Complete cells

The corrected paper (`paper/rw-spheres-corrected.tex`, Correction 4) asks of the active cells that
they be *complete*: a cell `P_v` has finitely many neighbours and its boundary is the union of its
contacts with them, `∂P_v = ⋃_{w ∼ v} (P_v ∩ P_w)`.  This is the exact obstruction behind the
counterexamples at unshared facets, and it is weaker than `P_v ⊆ interior D`
(`CompleteCell.of_subset_interior`): a cell that meets the boundary of `D` only in a
lower-dimensional set can be complete.
-/

namespace SpherePackings

open BouRabeeGwynne

variable {d : ℕ}

/-- A complete cell: finitely many neighbours, and every boundary point of the cell lies in the
cell of a neighbour (`rw-spheres-corrected.tex`, Correction 4). -/
def CompleteCell (T : OrthogonalTiling d) (v : T.V) : Prop :=
  (T.neighbors v).Finite ∧ frontier (T.cell v).carrier ⊆ ⋃ w ∈ T.neighbors v, (T.cell w).carrier

namespace CompleteCell

variable {T : OrthogonalTiling d} {v : T.V}

/-- The boundary of a complete cell is the union of its contacts with its neighbours. -/
theorem frontier_eq (hv : CompleteCell T v) :
    frontier (T.cell v).carrier = ⋃ w ∈ T.neighbors v, T.toTilingData.facet v w := by
  ext x
  constructor
  · intro hx
    have hxv : x ∈ (T.cell v).carrier :=
      (T.cell v).compact.isClosed.frontier_subset hx
    obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp (hv.2 hx)
    exact Set.mem_iUnion₂.mpr ⟨w, hw, hxv, hxw⟩
  · intro hx
    obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx
    exact TilingData.facet_subset_frontier_left (T := T.toTilingData) hw.1 hxw

/-- A complete cell is covered by its marked point and the pyramids over its contacts with its
neighbours. -/
theorem cell_subset_insert_iUnion_cellPyramids (hv : CompleteCell T v) :
    (T.cell v).carrier ⊆
      insert (T.pos v) (⋃ w ∈ T.neighbors v, T.toTilingData.cellPyramid v w) := by
  intro x hx
  by_cases hxp : x = T.pos v
  · exact Set.mem_insert_iff.mpr (Or.inl hxp)
  · obtain ⟨b, hb, hxb⟩ := (T.cell v).exists_frontier_segment hx hxp
    rw [hv.frontier_eq] at hb
    obtain ⟨w, hw, hbw⟩ := Set.mem_iUnion₂.mp hb
    refine Set.mem_insert_iff.mpr (Or.inr (Set.mem_iUnion₂.mpr ⟨w, hw, ?_⟩))
    exact (T.toTilingData.cellPyramid_convex v w).segment_subset
      (T.toTilingData.pos_mem_cellPyramid v w) (T.toTilingData.facet_subset_cellPyramid v w hbw) hxb

/-- A point of a contact pyramid `conv(v, P_v ∩ P_w)` on the boundary of `P_v` lies in the
contact. -/
theorem mem_facet_of_mem_cellPyramid_frontier {w : T.V} (hvw : T.adj v w) {x : Euc d}
    (hx : x ∈ T.toTilingData.cellPyramid v w) (hxf : x ∈ frontier (T.cell v).carrier) :
    x ∈ T.toTilingData.facet v w := by
  have hne : (T.toTilingData.facet v w).Nonempty := hvw.2.1
  have hx' := hx
  unfold TilingData.cellPyramid at hx'
  rw [convexHull_insert_eq_segment_image (T.pos v) (T.toTilingData.facet_convex v w) hne] at hx'
  obtain ⟨⟨t, f⟩, ⟨ht, hf⟩, rfl⟩ := hx'
  rcases eq_or_lt_of_le ht.2 with h1 | h1
  · simp only at h1
    subst h1
    simpa using hf
  · exfalso
    have hint : (1 - t) • T.pos v + t • f ∈ interior (T.cell v).carrier :=
      (T.cell v).convex.combo_interior_closure_mem_interior (T.pos_mem_interior v)
        (subset_closure hf.1) (by linarith) ht.1 (by ring)
    exact (Set.disjoint_left.mp disjoint_interior_frontier) hint hxf

/-- A cell in the interior of the ambient set is complete. -/
theorem of_subset_interior (hd : 1 ≤ d) (hvD : (T.cell v).carrier ⊆ interior T.domain) :
    CompleteCell T v := by
  refine ⟨T.neighbors_finite v (hvD.trans interior_subset), fun x hx => ?_⟩
  have hxv : x ∈ (T.cell v).carrier := (T.cell v).compact.isClosed.frontier_subset hx
  obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp (cell_subset_iUnion_dualPolytope hd T v hvD hxv)
  refine Set.mem_iUnion₂.mpr ⟨w, hw, ?_⟩
  rcases hxw with hxw | hxw
  · exact (mem_facet_of_mem_cellPyramid_frontier hw hxw hx).2
  · exact T.toTilingData.cellPyramid_subset_cell w v hxw

/-- In dimension at least one a complete cell has a neighbour: otherwise its boundary is empty, and
the cell, compact and nonempty, would be the whole space. -/
theorem exists_neighbor (hd : 1 ≤ d) (hv : CompleteCell T v) : ∃ w, T.adj v w := by
  by_contra hno
  push Not at hno
  have hfr : frontier (T.cell v).carrier = ∅ := by
    rw [hv.frontier_eq]
    refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
    obtain ⟨w, hw, -⟩ := Set.mem_iUnion₂.mp hx
    exact hno w hw
  have hclopen : IsClopen (T.cell v).carrier :=
    isClopen_iff_frontier_eq_empty.mpr hfr
  have hne : (T.cell v).carrier.Nonempty := (T.cell v).interior_nonempty.mono interior_subset
  have huniv : (T.cell v).carrier = Set.univ := hclopen.eq_univ hne
  have : NeZero d := ⟨by omega⟩
  exact (NormedSpace.unbounded_univ ℝ (Euc d)) (huniv ▸ (T.cell v).compact.isBounded)

/-- A complete cell (in dimension at least one) is covered by the pyramids over its contacts with
its neighbours. -/
theorem cell_subset_iUnion_cellPyramids (hd : 1 ≤ d) (hv : CompleteCell T v) :
    (T.cell v).carrier ⊆ ⋃ w ∈ T.neighbors v, T.toTilingData.cellPyramid v w := by
  intro x hx
  rcases Set.mem_insert_iff.mp (hv.cell_subset_insert_iUnion_cellPyramids hx) with rfl | hx
  · obtain ⟨w, hw⟩ := hv.exists_neighbor hd
    exact Set.mem_iUnion₂.mpr ⟨w, hw, T.toTilingData.pos_mem_cellPyramid v w⟩
  · exact hx

/-- A complete cell (in dimension at least one) is covered by the dual polytopes of its edges. -/
theorem cell_subset_iUnion_dualPolytope (hd : 1 ≤ d) (hv : CompleteCell T v) :
    (T.cell v).carrier ⊆ ⋃ w ∈ T.neighbors v, T.toTilingData.dualPolytope v w := by
  intro x hx
  obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp (hv.cell_subset_iUnion_cellPyramids hd hx)
  exact Set.mem_iUnion₂.mpr ⟨w, hw, Or.inl hxw⟩

end CompleteCell

/-- **Lemma 2.5** (`lemma:easy-global-qe-bounds`), as in the corrected paper
(`rw-spheres-corrected.tex`, Correction 7): if the cells of `V[U]` are complete, they are covered
by `⋃_{e ∈ E[Ū]} Q_e`, which lies in `Ĝ_U`. -/
theorem dual_coverage_complete {d : ℕ} (hd : 1 ≤ d) (T : OrthogonalTiling d) (U : Set (Euc d))
    (hcomplete : ∀ v ∈ T.interiorVertices U, CompleteCell T v) :
    (⋃ v ∈ T.interiorVertices U, (T.cell v).carrier) ⊆
      ⋃ v ∈ T.interiorVertices U, ⋃ w ∈ T.neighbors v, T.toTilingData.dualPolytope v w ∧
    (⋃ v ∈ T.interiorVertices U, ⋃ w ∈ T.neighbors v, T.toTilingData.dualPolytope v w) ⊆
      ⋃ v ∈ T.closedVertices U, (T.cell v).carrier := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨v, hv, hxv⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨v, hv, (hcomplete v hv).cell_subset_iUnion_dualPolytope hd hxv⟩
  · obtain ⟨v, hv, hx⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨w, hw, hx⟩ := Set.mem_iUnion₂.mp hx
    rcases hx with hx | hx
    · exact Set.mem_iUnion₂.mpr ⟨v, T.interiorVertices_subset_closedVertices U hv,
        T.toTilingData.cellPyramid_subset_cell v w hx⟩
    · exact Set.mem_iUnion₂.mpr ⟨w, T.neighbor_mem_closedVertices hv hw,
        T.toTilingData.cellPyramid_subset_cell w v hx⟩

end SpherePackings
