module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/CellVolumeBound.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.DualCoverage
public import BouRabeeGwynne.DualNull

@[expose] public section

open scoped ENNReal MeasureTheory BigOperators
open MeasureTheory

namespace BouRabeeGwynne.TilingData

variable {d : ℕ} (T : TilingData d)

/-- A finite incident-dual volume sum controls the volume of its primal cell.
Only contacts in the actual locally finite tiling enter the sum. -/
theorem cell_measure_le_sum_dualVolume (hd : 1 ≤ d) (v : T.V)
    (hvD : (T.cell v).carrier ⊆ interior T.domain) :
    μHE[d] (T.cell v).carrier ≤
      ∑ w ∈ T.contactFinset v (hvD.trans interior_subset), T.dualVolume v w := by
  classical
  let F := T.contactFinset v (hvD.trans interior_subset)
  have hcover : (T.cell v).carrier ⊆ insert (T.pos v)
      (⋃ w ∈ F, T.dualPolytope v w) := by
    simpa only [F, T.mem_contactFinset] using T.cell_subset_insert_iUnion_dualPolytopes v hvD
  have hapex : μHE[d] ({T.pos v} : Set (Euc d)) = 0 := by
    apply euclideanHausdorffMeasure_eq_zero_of_affineSpan_rank_lt
      isCompact_singleton (convex_singleton _) (Set.singleton_nonempty _)
    rw [direction_affineSpan, vectorSpan_singleton]
    simpa using (Nat.lt_of_lt_of_le Nat.zero_lt_one hd)
  calc
    μHE[d] (T.cell v).carrier ≤ μHE[d]
        (insert (T.pos v) (⋃ w ∈ F, T.dualPolytope v w)) := measure_mono hcover
    _ ≤ μHE[d] ({T.pos v} : Set (Euc d)) +
        μHE[d] (⋃ w ∈ F, T.dualPolytope v w) := measure_union_le _ _
    _ ≤ 0 + ∑ w ∈ F, T.dualVolume v w :=
      add_le_add hapex.le (measure_biUnion_finset_le F (T.dualPolytope v))
    _ = _ := zero_add _

/-- Nonadjacent lower-dimensional contacts may be removed from the finite
volume bound without any face-to-face assumption. -/
theorem cell_measure_le_sum_adjacent_dualVolume (hd : 1 ≤ d) (v : T.V)
    (hvD : (T.cell v).carrier ⊆ interior T.domain) :
    letI := Classical.propDecidable
    μHE[d] (T.cell v).carrier ≤
      ∑ w ∈ (T.contactFinset v (hvD.trans interior_subset)).filter (T.adj v),
        T.dualVolume v w := by
  classical
  have hsum :
      (∑ w ∈ T.contactFinset v (hvD.trans interior_subset), T.dualVolume v w) =
      ∑ w ∈ (T.contactFinset v (hvD.trans interior_subset)).filter (T.adj v),
        T.dualVolume v w := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro w hw
    by_cases hadj : T.adj v w
    · rw [if_pos hadj]
    · rw [if_neg hadj]
      have hcontact := (T.mem_contactFinset (hvD.trans interior_subset)).mp hw
      exact T.dualVolume_eq_zero_of_nonadjacent_contact hd hcontact.1.symm hcontact.2 hadj
  exact hsum ▸ T.cell_measure_le_sum_dualVolume hd v hvD

end BouRabeeGwynne.TilingData
