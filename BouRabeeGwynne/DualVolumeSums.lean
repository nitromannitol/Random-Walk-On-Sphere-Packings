-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/DualVolumeSums.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.PyramidOverlap
import BouRabeeGwynne.DualAdditivity

open scoped ENNReal MeasureTheory BigOperators
open MeasureTheory

namespace BouRabeeGwynne.TilingData

variable {d : ℕ} (T : TilingData d)

/-- Pyramids based in distinct primal cells have null overlap. -/
lemma cellPyramid_aedisjoint_of_apex_ne (hd : 1 ≤ d) {v w u z : T.V}
    (hvu : v ≠ u) :
    AEDisjoint (μHE[d]) (T.cellPyramid v w) (T.cellPyramid u z) := by
  apply measure_mono_null _ (T.facet_full_measure_zero hd hvu)
  exact Set.inter_subset_inter (T.cellPyramid_subset_cell v w)
    (T.cellPyramid_subset_cell u z)

/-- Distinct oriented incident pyramids have null overlap. -/
lemma cellPyramid_aedisjoint (hd : 1 ≤ d) {v w u z : T.V}
    (hvw : T.adj v w) (huz : T.adj u z) (hne : (v, w) ≠ (u, z)) :
    AEDisjoint (μHE[d]) (T.cellPyramid v w) (T.cellPyramid u z) := by
  by_cases h : v = u
  · subst u
    have hwz : w ≠ z := fun hwz => hne (Prod.ext rfl hwz)
    exact T.cellPyramid_inter_measure_zero hd hvw huz hwz
  · exact T.cellPyramid_aedisjoint_of_apex_ne hd h

/-- The two actual dual polytopes of distinct unordered edges have null overlap. -/
theorem dualPolytope_aedisjoint (hd : 1 ≤ d) {v w u z : T.V}
    (hvw : T.adj v w) (huz : T.adj u z)
    (hne : (v, w) ≠ (u, z)) (hrev : (v, w) ≠ (z, u)) :
    AEDisjoint (μHE[d]) (T.dualPolytope v w) (T.dualPolytope u z) := by
  have hne' : (w, v) ≠ (z, u) := by
    intro h
    exact hne (Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h))
  have hrev' : (w, v) ≠ (u, z) := by
    intro h
    exact hrev (Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h))
  simp only [dualPolytope, AEDisjoint.union_left_iff, AEDisjoint.union_right_iff]
  exact ⟨⟨T.cellPyramid_aedisjoint hd hvw huz hne,
      T.cellPyramid_aedisjoint hd (T.adj_symm hvw) huz hrev'⟩,
    ⟨T.cellPyramid_aedisjoint hd hvw (T.adj_symm huz) hrev,
      T.cellPyramid_aedisjoint hd (T.adj_symm hvw) (T.adj_symm huz) hne'⟩⟩

/-- A finite edge family with only one orientation per edge has exactly the
volume of its union of dual cells. -/
theorem sum_dualVolume_eq_measure_union (hd : 1 ≤ d) (E : Finset (T.V × T.V))
    (hE : ∀ e ∈ E, T.adj e.1 e.2)
    (hrev : ∀ e ∈ E, ∀ f ∈ E, e ≠ f → e ≠ f.swap) :
    ∑ e ∈ E, T.dualVolume e.1 e.2 =
      μHE[d] (⋃ e ∈ E, T.dualPolytope e.1 e.2) := by
  classical
  symm
  apply measure_biUnion_finset₀
  · intro e he f hf hef
    exact T.dualPolytope_aedisjoint hd (hE e he) (hE f hf) hef (hrev e he f hf hef)
  · intro e _
    exact (T.dualPolytope_measurableSet e.1 e.2).nullMeasurableSet

/-- The exact finite-volume bound used when all dual cells lie in a cylinder. -/
theorem sum_dualVolume_le_measure (hd : 1 ≤ d) (E : Finset (T.V × T.V))
    (hE : ∀ e ∈ E, T.adj e.1 e.2)
    (hrev : ∀ e ∈ E, ∀ f ∈ E, e ≠ f → e ≠ f.swap)
    {C : Set (Euc d)} (hC : ∀ e ∈ E, T.dualPolytope e.1 e.2 ⊆ C) :
    ∑ e ∈ E, T.dualVolume e.1 e.2 ≤ μHE[d] C := by
  rw [T.sum_dualVolume_eq_measure_union hd E hE hrev]
  exact measure_mono (Set.iUnion₂_subset hC)

end BouRabeeGwynne.TilingData
