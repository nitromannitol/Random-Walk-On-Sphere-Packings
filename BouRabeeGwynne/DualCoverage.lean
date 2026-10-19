-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/DualCoverage.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.DualCells
import BouRabeeGwynne.RadialBoundary
import BouRabeeGwynne.FacetPartition

open scoped Topology

namespace BouRabeeGwynne.TilingData

variable {d : ℕ} (T : TilingData d)

/-- Every non-apex point of a cell lies in a pyramid over one of its actual
contacts. The radial boundary witness and the local tiling cover supply that
contact; it need not be a whole supporting facet. -/
theorem exists_mem_cellPyramid {v : T.V}
    (hvD : (T.cell v).carrier ⊆ interior T.domain) {x : Euc d}
    (hx : x ∈ (T.cell v).carrier) (hxp : x ≠ T.pos v) :
    ∃ w ∈ T.touchingCells v, x ∈ T.cellPyramid v w := by
  obtain ⟨b, hb, hxb⟩ := (T.cell v).exists_frontier_segment hx hxp
  rw [T.frontier_eq_iUnion_contacts v hvD] at hb
  obtain ⟨w, hw, hb⟩ := Set.mem_iUnion₂.mp hb
  exact ⟨w, hw, (T.cellPyramid_convex v w).segment_subset
    (T.pos_mem_cellPyramid v w) (T.facet_subset_cellPyramid v w hb) hxb⟩

/-- Exact cell coverage by the contact pyramids, with the common apex explicit.
Lower-dimensional contacts are retained until their volume is shown to vanish. -/
theorem cell_eq_insert_iUnion_cellPyramids (v : T.V)
    (hvD : (T.cell v).carrier ⊆ interior T.domain) :
    (T.cell v).carrier = insert (T.pos v)
      (⋃ w ∈ T.touchingCells v, T.cellPyramid v w) := by
  ext x
  constructor
  · intro hx
    by_cases hxp : x = T.pos v
    · exact Set.mem_insert_iff.mpr (Or.inl hxp)
    · obtain ⟨w, hw, hxw⟩ := T.exists_mem_cellPyramid hvD hx hxp
      exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_iUnion₂.mpr ⟨w, hw, hxw⟩))
  · intro hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact interior_subset (T.pos_mem_interior v)
    · obtain ⟨w, _hw, hxw⟩ := Set.mem_iUnion₂.mp hx
      exact T.cellPyramid_subset_cell v w hxw

/-- The exact coverage is finite whenever the full cell lies in the covered
open region. This is the geometric cover used in the dual-volume argument. -/
theorem cell_eq_insert_iUnion_contactFinset_pyramids (v : T.V)
    (hvD : (T.cell v).carrier ⊆ interior T.domain) :
    (T.cell v).carrier = insert (T.pos v)
      (⋃ w ∈ T.contactFinset v (hvD.trans interior_subset), T.cellPyramid v w) := by
  simpa only [T.mem_contactFinset] using T.cell_eq_insert_iUnion_cellPyramids v hvD

/-- In particular, every non-apex cell point belongs to an actual dual cell. -/
theorem cell_subset_insert_iUnion_dualPolytopes (v : T.V)
    (hvD : (T.cell v).carrier ⊆ interior T.domain) :
    (T.cell v).carrier ⊆ insert (T.pos v)
      (⋃ w ∈ T.touchingCells v, T.dualPolytope v w) := by
  rw [T.cell_eq_insert_iUnion_cellPyramids v hvD]
  apply Set.insert_subset_insert
  intro x hx
  obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx
  exact Set.mem_iUnion₂.mpr ⟨w, hw, Or.inl hxw⟩

end BouRabeeGwynne.TilingData
