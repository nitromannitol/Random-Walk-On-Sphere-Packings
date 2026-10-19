-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/DualCells.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.FacetMeasure
import BouRabeeGwynne.LocalGeometry
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Convex.Topology

open scoped ENNReal MeasureTheory
open MeasureTheory

namespace BouRabeeGwynne

/-- A pyramid over a nonempty convex base has its actual segment parametrization. -/
theorem convexHull_insert_eq_segment_image {d : ℕ} (a : Euc d) {s : Set (Euc d)}
    (hs : Convex ℝ s) (hne : s.Nonempty) :
    convexHull ℝ (insert a s) =
      (fun q : ℝ × Euc d => (1 - q.1) • a + q.1 • q.2) ''
        (Set.Icc (0 : ℝ) 1 ×ˢ s) := by
  rw [convexHull_insert hne, hs.convexHull_eq, convexJoin_singleton_left]
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hz
    obtain ⟨hxs, hxz⟩ := Set.mem_iUnion.mp hx
    rw [segment_eq_image] at hxz
    obtain ⟨t, ht, htz⟩ := hxz
    exact ⟨(t, x), ⟨ht, hxs⟩, htz⟩
  · rintro ⟨⟨t, x⟩, ⟨ht, hxs⟩, htz⟩
    refine Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hxs, ?_⟩⟩
    rw [segment_eq_image]
    exact ⟨t, ht, htz⟩

/-- Compactness of a convex-base pyramid, including an empty base. -/
theorem isCompact_convexHull_insert_of_convex {d : ℕ} (a : Euc d)
    {s : Set (Euc d)} (hs : IsCompact s) (hconv : Convex ℝ s) :
    IsCompact (convexHull ℝ (insert a s)) := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simpa using (isCompact_singleton : IsCompact ({a} : Set (Euc d)))
  · rw [convexHull_insert_eq_segment_image a hconv hne]
    exact (isCompact_Icc.prod hs).image (by fun_prop)

namespace TilingData

variable {d : ℕ} (T : TilingData d)

/-- The part of an edge's dual cell lying in its first primal cell. -/
def cellPyramid (v w : T.V) : Set (Euc d) :=
  convexHull ℝ (insert (T.pos v) (T.facet v w))

/-- The actual dual polytope from Section 2: the two pyramids over the contact. -/
def dualPolytope (v w : T.V) : Set (Euc d) :=
  T.cellPyramid v w ∪ T.cellPyramid w v

/-- Full-dimensional Euclidean volume of the actual dual polytope. -/
noncomputable def dualVolume (v w : T.V) : ℝ≥0∞ :=
  μHE[d] (T.dualPolytope v w)

lemma cellPyramid_subset_cell (v w : T.V) :
    T.cellPyramid v w ⊆ (T.cell v).carrier := by
  apply convexHull_min _ (T.cell v).convex
  exact Set.insert_subset_iff.mpr
    ⟨interior_subset (T.pos_mem_interior v), Set.inter_subset_left⟩

lemma facet_subset_cellPyramid (v w : T.V) :
    T.facet v w ⊆ T.cellPyramid v w :=
  Set.Subset.trans (Set.subset_insert _ _) (subset_convexHull ℝ _)

lemma pos_mem_cellPyramid (v w : T.V) : T.pos v ∈ T.cellPyramid v w :=
  subset_convexHull ℝ _ (Set.mem_insert _ _)

lemma cellPyramid_compact (v w : T.V) : IsCompact (T.cellPyramid v w) :=
  isCompact_convexHull_insert_of_convex (T.pos v)
    (T.facet_compact v w) (T.facet_convex v w)

lemma cellPyramid_convex (v w : T.V) : Convex ℝ (T.cellPyramid v w) :=
  convex_convexHull ℝ _

lemma dualPolytope_symm (v w : T.V) : T.dualPolytope v w = T.dualPolytope w v :=
  Set.union_comm _ _

lemma dualPolytope_subset_cells (v w : T.V) :
    T.dualPolytope v w ⊆ (T.cell v).carrier ∪ (T.cell w).carrier :=
  Set.union_subset_union (T.cellPyramid_subset_cell v w) (T.cellPyramid_subset_cell w v)

lemma dualPolytope_compact (v w : T.V) : IsCompact (T.dualPolytope v w) :=
  (T.cellPyramid_compact v w).union (T.cellPyramid_compact w v)

lemma dualPolytope_measurableSet (v w : T.V) : MeasurableSet (T.dualPolytope v w) :=
  (T.dualPolytope_compact v w).isClosed.measurableSet

lemma dualVolume_symm (v w : T.V) : T.dualVolume v w = T.dualVolume w v := by
  unfold dualVolume
  rw [T.dualPolytope_symm]

lemma dualVolume_eq_volume (v w : T.V) :
    T.dualVolume v w = volume (T.dualPolytope v w) := by
  unfold dualVolume
  rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]

lemma dualVolume_lt_top (v w : T.V) : T.dualVolume v w < ∞ := by
  rw [T.dualVolume_eq_volume]
  exact (T.dualPolytope_compact v w).measure_lt_top

/-- Each half of the dual cell stays within one mesh of its marked apex. -/
lemma dist_pos_le_mesh_of_mem_cellPyramid {v w : T.V} {x : Euc d}
    (hx : x ∈ T.cellPyramid v w) (hmesh : T.mesh ≠ ∞) :
    dist x (T.pos v) ≤ T.mesh.toReal :=
  T.dist_pos_le_mesh (T.cellPyramid_subset_cell v w hx) hmesh

end TilingData
end BouRabeeGwynne
