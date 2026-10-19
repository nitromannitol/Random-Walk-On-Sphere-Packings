-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/DualNull.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.DualCells
import BouRabeeGwynne.FacetNull
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

open scoped ENNReal MeasureTheory
open MeasureTheory

namespace BouRabeeGwynne.TilingData

variable {d : ℕ} (T : TilingData d)

/-- Coning a contact from one marked point increases its affine rank by at most
one. The contact and pyramid here are the actual geometric sets. -/
lemma cellPyramid_finrank_le (v w : T.V) :
    Module.finrank ℝ (affineSpan ℝ (T.cellPyramid v w)).direction ≤
      Module.finrank ℝ (affineSpan ℝ (T.facet v w)).direction + 1 := by
  unfold cellPyramid
  rw [affineSpan_convexHull, direction_affineSpan, direction_affineSpan]
  exact finrank_vectorSpan_insert_le_set ℝ (T.facet v w) (T.pos v)

/-- A nonempty contact omitted from adjacency contributes zero full-dimensional
pyramid volume. The strict-rank argument also covers d=1 without using d−2. -/
lemma cellPyramid_measure_zero_of_nonadjacent_contact (hd : 1 ≤ d) {v w : T.V}
    (hvw : v ≠ w) (hne : (T.facet v w).Nonempty) (hnot : ¬ T.adj v w) :
    μHE[d] (T.cellPyramid v w) = 0 := by
  have hle := T.facet_finrank_le hd hvw
  have hneq : Module.finrank ℝ (affineSpan ℝ (T.facet v w)).direction ≠ d - 1 := by
    intro heq
    exact hnot ⟨hvw, hne, heq⟩
  have hcone := T.cellPyramid_finrank_le v w
  apply BouRabeeGwynne.euclideanHausdorffMeasure_eq_zero_of_affineSpan_rank_lt
    (T.cellPyramid_compact v w) (T.cellPyramid_convex v w)
    ⟨T.pos v, T.pos_mem_cellPyramid v w⟩
  omega

/-- Lower-dimensional contacts have zero actual dual-cell volume and may thus
be removed from the volume cover without adding a face-to-face assumption. -/
lemma dualVolume_eq_zero_of_nonadjacent_contact (hd : 1 ≤ d) {v w : T.V}
    (hvw : v ≠ w) (hne : (T.facet v w).Nonempty) (hnot : ¬ T.adj v w) :
    T.dualVolume v w = 0 := by
  have hne' : (T.facet w v).Nonempty := by simpa only [T.facet_symm w v] using hne
  have hnot' : ¬ T.adj w v := fun h => hnot (T.adj_symm h)
  exact measure_union_null
    (T.cellPyramid_measure_zero_of_nonadjacent_contact hd hvw hne hnot)
    (T.cellPyramid_measure_zero_of_nonadjacent_contact hd hvw.symm hne' hnot')

end BouRabeeGwynne.TilingData
