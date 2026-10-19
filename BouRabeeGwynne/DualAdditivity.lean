-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/DualAdditivity.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.DualCells
import BouRabeeGwynne.FacetNull

open scoped ENNReal MeasureTheory
open MeasureTheory

namespace BouRabeeGwynne.TilingData

variable {d : ℕ} (T : TilingData d)

/-- Distinct primal cells meet in a set of zero full-dimensional volume. -/
lemma facet_full_measure_zero (hd : 1 ≤ d) {v w : T.V} (hvw : v ≠ w) :
    μHE[d] (T.facet v w) = 0 := by
  rcases (T.facet v w).eq_empty_or_nonempty with hempty | hne
  · rw [hempty, measure_empty]
  · apply euclideanHausdorffMeasure_eq_zero_of_affineSpan_rank_lt
      (T.facet_compact v w) (T.facet_convex v w) hne
    have hdim := T.facet_finrank_le hd hvw
    omega

/-- The two halves of the actual dual polytope meet exactly in their common
contact, without requiring the marked edge to cross that contact. -/
lemma cellPyramid_inter_reverse (v w : T.V) :
    T.cellPyramid v w ∩ T.cellPyramid w v = T.facet v w := by
  apply Set.Subset.antisymm
  · intro x hx
    exact ⟨T.cellPyramid_subset_cell v w hx.1, T.cellPyramid_subset_cell w v hx.2⟩
  · intro x hx
    refine ⟨T.facet_subset_cellPyramid v w hx, ?_⟩
    apply T.facet_subset_cellPyramid w v
    rw [T.facet_symm w v]
    exact hx

/-- The volume of a dual polytope is the sum of the two pyramid volumes. -/
theorem dualVolume_eq_pyramid_add (hd : 1 ≤ d) {v w : T.V} (hvw : v ≠ w) :
    T.dualVolume v w = μHE[d] (T.cellPyramid v w) + μHE[d] (T.cellPyramid w v) := by
  apply measure_union₀ (T.cellPyramid_compact w v).isClosed.measurableSet.nullMeasurableSet
  change μHE[d] (T.cellPyramid v w ∩ T.cellPyramid w v) = 0
  rw [T.cellPyramid_inter_reverse]
  exact T.facet_full_measure_zero hd hvw

end BouRabeeGwynne.TilingData
