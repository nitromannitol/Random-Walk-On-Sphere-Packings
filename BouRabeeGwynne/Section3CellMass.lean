-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/Section3CellMass.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.Section3EnergyNormalization
import BouRabeeGwynne.CellVolumeBound
import BouRabeeGwynne.DualVolume

/-! Each actual interior tile volume is bounded by total incident mass. -/

open scoped Classical BigOperators ENNReal MeasureTheory
open MeasureTheory

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

lemma cellVolume_ne_top (v : T.V) : (T.cell v).volume ≠ ∞ := by
  have hm : (μHE[d] : Measure (Euc d)) = volume := by
    simpa using InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := Euc d)
  change μHE[d] (T.cell v).carrier ≠ ∞
  rw [hm]
  exact (T.cell v).compact.measure_lt_top.ne

lemma minTileVolume_toReal_le_cellVolume (v : T.V) :
    T.minTileVolume.toReal ≤ (T.cell v).volume.toReal :=
  ENNReal.toReal_mono (T.cellVolume_ne_top v) (iInf_le _ v)

lemma cellVolume_le_adjacent_row (hd : 1 ≤ d)
    (R : Set T.V) [Fintype R] (A : Set R)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    {v : R} (hv : v ∈ A) (hvD : (T.cell v).carrier ⊆ interior T.domain) :
    (T.cell v).volume.toReal ≤ ∑ w : R,
      if T.adj v w then (T.facetVolume v w).toReal * ‖T.pos w - T.pos v‖ else 0 := by
  let E := (T.toTilingData.contactFinset v (hvD.trans interior_subset)).filter (T.adj v)
  let j : T.V → R := fun w => if hw : w ∈ R then ⟨w, hw⟩ else v
  have hER : ∀ w ∈ E, w ∈ R := fun w hw => hneighbors v hv w (Finset.mem_filter.mp hw).2
  have hj : ∀ w ∈ E, (j w : T.V) = w := by
    intro w hw
    simp only [j, hER w hw, dite_true]
  have hinj : Set.InjOn j E := by
    intro w hw z hz heq
    simpa only [hj w hw, hj z hz] using congrArg Subtype.val heq
  have hsum : (∑ w ∈ E, T.toTilingData.dualVolume v w) ≤
      ∑ w : R, if T.adj v w then T.toTilingData.dualVolume v w else 0 := by
    apply Finset.sum_le_sum_of_injOn j hinj (Finset.subset_univ _)
    · intro w hw
      rw [hj w hw, if_pos (Finset.mem_filter.mp hw).2]
    · intro w _ _
      exact zero_le
  have hmeasure : (T.cell v).volume ≤
      ∑ w : R, if T.adj v w then T.toTilingData.dualVolume v w else 0 :=
    (T.toTilingData.cell_measure_le_sum_adjacent_dualVolume hd v hvD).trans hsum
  have hfinite (w : R) :
      (if T.adj v w then T.toTilingData.dualVolume v w else 0) ≠ ∞ := by
    split_ifs
    · exact (T.toTilingData.dualVolume_lt_top v w).ne
    · exact ENNReal.zero_ne_top
  have hreal := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun w _ => hfinite w)) hmeasure
  rw [ENNReal.toReal_sum (fun w _ => hfinite w)] at hreal
  apply hreal.trans
  apply Finset.sum_le_sum
  intro w _
  by_cases ha : T.adj v w
  · rw [if_pos ha, if_pos ha, mul_comm,
      T.edgeLength_mul_facetVolume_eq_dim_mul_dualVolume hd ha]
    exact le_mul_of_one_le_left ENNReal.toReal_nonneg (by exact_mod_cast hd)
  · simp only [if_neg ha, ENNReal.toReal_zero, le_refl]

/-- A nonsharp factor two avoids any choice of orientation at a distinguished
vertex and is sufficient for the Hypothesis II termination argument. -/
theorem cellVolume_le_twice_incidentMass (hd : 1 ≤ d)
    (R : Set T.V) [Fintype R] (A : Set R)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    {v : R} (hv : v ∈ A) (hvD : (T.cell v).carrier ⊆ interior T.domain) :
    (T.cell v).volume.toReal ≤ 2 * T.incidentMass R A := by
  have hrow := T.cellVolume_le_adjacent_row hd R A hneighbors hv hvD
  let F : R → R → ℝ := fun u w =>
    if T.adj u w ∧ (u ∈ A ∨ w ∈ A) then
      (T.facetVolume u w).toReal * ‖T.pos w - T.pos u‖ else 0
  have hnonneg : ∀ u w, 0 ≤ F u w := by
    intro u w
    dsimp [F]
    split_ifs
    · exact mul_nonneg ENNReal.toReal_nonneg (norm_nonneg _)
    · exact le_rfl
  have hrow' : (T.cell v).volume.toReal ≤ ∑ w, F v w := by
    simpa only [F, hv, true_or, and_true] using hrow
  have hsingle : (∑ w, F v w) ≤ ∑ u, ∑ w, F u w :=
    Finset.single_le_sum (fun u _ => Finset.sum_nonneg (fun w _ => hnonneg u w))
      (Finset.mem_univ v)
  apply hrow'.trans (hsingle.trans_eq _)
  rw [T.incidentMass_eq_half_ordered]
  dsimp [F]
  ring

end BouRabeeGwynne.OrthogonalTiling
