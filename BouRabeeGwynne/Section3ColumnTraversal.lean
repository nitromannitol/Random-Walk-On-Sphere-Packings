-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/Section3ColumnTraversal.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.ProjectedBase
import BouRabeeGwynne.LocalFacetCoverage
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Section 3: moving forward through a column

At an upper fiber endpoint in the covered open region, a touching cell extends
strictly farther in the column direction. This follows from finite local
coverage and closedness, without assuming connectivity of an entire column.
-/

open scoped Topology
open Filter

namespace BouRabeeGwynne.TilingData

variable {d : ℕ} (T : TilingData d)

/-- A cell ending on a column is followed by a touching cell with a strictly
larger upper endpoint. The touching contact need not yet have positive area. -/
theorem exists_touching_upperFiber_gt (e : Euc d) (he : e ≠ 0)
    (v : T.V) {y : Euc d} (hy : y ∈ (T.cell v).projectedBase e he)
    (hzD : (T.cell v).upperEndpoint e he y ∈ interior T.domain) :
    ∃ w : T.V, w ≠ v ∧
      (T.cell v).upperEndpoint e he y ∈ T.facet v w ∧
      y ∈ (T.cell w).projectedBase e he ∧
      (T.cell v).upperFiber e he y < (T.cell w).upperFiber e he y := by
  let z := (T.cell v).upperEndpoint e he y
  let s := (T.cell v).upperFiber e he y
  obtain ⟨r, hr, hrD⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (isOpen_interior.mem_nhds hzD)
  let S : Set T.V := {w | ((T.cell w).carrier ∩ Metric.closedBall z r).Nonempty}
  have hS : S.Finite :=
    T.locallyFinite _ (isCompact_closedBall z r) (hrD.trans interior_subset)
  let J : Set T.V := {w | w ∈ S ∧ s < (T.cell w).upperFiber e he y}
  let C : Set (Euc d) := ⋃ w ∈ J, (T.cell w).carrier
  have hJ : J.Finite := hS.subset (fun _ hw => hw.1)
  have hC : IsClosed C := hJ.isClosed_biUnion
    (fun w _ => (T.cell w).compact.isClosed)
  have htend : Tendsto (fun t : ℝ => z + t • e) (𝓝[>] 0) (𝓝 z) := by
    have hc : Continuous (fun t : ℝ => z + t • e) :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa only [zero_smul, add_zero] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hnear : ∀ᶠ t : ℝ in 𝓝[>] 0, z + t • e ∈ Metric.ball z r :=
    htend (Metric.ball_mem_nhds z hr)
  have hforward : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  have hmem : ∀ᶠ t : ℝ in 𝓝[>] 0, z + t • e ∈ C := by
    filter_upwards [hnear, hforward] with t ht hpos
    obtain ⟨w, hw⟩ := T.exists_mem_cell
      (interior_subset (hrD (Metric.ball_subset_closedBall ht)))
    have hwS : w ∈ S := ⟨z + t • e, hw, Metric.ball_subset_closedBall ht⟩
    have hline : y + (s + t) • e ∈ (T.cell w).carrier := by
      simpa only [z, s, ConvexPolytope.upperEndpoint, add_smul, add_assoc] using hw
    have hbound := ((T.cell w).mem_line_iff he y (s + t)).mp hline
    have hwJ : w ∈ J := ⟨hwS, (lt_add_of_pos_right s hpos).trans_le hbound.2.2⟩
    exact Set.mem_iUnion₂.mpr ⟨w, hwJ, hw⟩
  obtain ⟨w, hwJ, hzw⟩ := Set.mem_iUnion₂.mp (hC.mem_of_tendsto htend hmem)
  have hscore : (T.cell v).upperFiber e he y < (T.cell w).upperFiber e he y := hwJ.2
  have hwv : w ≠ v := by
    intro h
    subst w
    exact (lt_irrefl _) hscore
  have hzv : z ∈ (T.cell v).carrier :=
    ((T.cell v).mem_line_iff he y _).mpr ⟨hy.2.1, hy.2.2, le_rfl⟩
  have hyw : y ∈ (T.cell w).projectedBase e he := by
    rw [(T.cell w).projectedBase_eq_image he]
    exact ⟨z, hzw, (T.cell v).project_upperEndpoint he hy⟩
  exact ⟨w, hwv, ⟨hzv, hzw⟩, hyw, hscore⟩

/-- A cell ending on a column is followed by a touching cell with a strictly
smaller lower endpoint. The touching contact need not yet have positive area. -/
theorem exists_touching_lowerFiber_lt (e : Euc d) (he : e ≠ 0)
    (v : T.V) {y : Euc d} (hy : y ∈ (T.cell v).projectedBase e he)
    (hzD : (T.cell v).lowerEndpoint e he y ∈ interior T.domain) :
    ∃ w : T.V, w ≠ v ∧
      (T.cell v).lowerEndpoint e he y ∈ T.facet v w ∧
      y ∈ (T.cell w).projectedBase e he ∧
      (T.cell w).lowerFiber e he y < (T.cell v).lowerFiber e he y := by
  let z := (T.cell v).lowerEndpoint e he y
  let s := (T.cell v).lowerFiber e he y
  obtain ⟨r, hr, hrD⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (isOpen_interior.mem_nhds hzD)
  let S : Set T.V := {w | ((T.cell w).carrier ∩ Metric.closedBall z r).Nonempty}
  have hS : S.Finite :=
    T.locallyFinite _ (isCompact_closedBall z r) (hrD.trans interior_subset)
  let J : Set T.V := {w | w ∈ S ∧ (T.cell w).lowerFiber e he y < s}
  let C : Set (Euc d) := ⋃ w ∈ J, (T.cell w).carrier
  have hJ : J.Finite := hS.subset (fun _ hw => hw.1)
  have hC : IsClosed C := hJ.isClosed_biUnion
    (fun w _ => (T.cell w).compact.isClosed)
  have htend : Tendsto (fun t : ℝ => z - t • e) (𝓝[>] 0) (𝓝 z) := by
    have hc : Continuous (fun t : ℝ => z - t • e) :=
      continuous_const.sub (continuous_id.smul continuous_const)
    simpa only [zero_smul, sub_zero] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hnear : ∀ᶠ t : ℝ in 𝓝[>] 0, z - t • e ∈ Metric.ball z r :=
    htend (Metric.ball_mem_nhds z hr)
  have hforward : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  have hmem : ∀ᶠ t : ℝ in 𝓝[>] 0, z - t • e ∈ C := by
    filter_upwards [hnear, hforward] with t ht hpos
    obtain ⟨w, hw⟩ := T.exists_mem_cell
      (interior_subset (hrD (Metric.ball_subset_closedBall ht)))
    have hwS : w ∈ S := ⟨z - t • e, hw, Metric.ball_subset_closedBall ht⟩
    have hline : y + (s - t) • e ∈ (T.cell w).carrier := by
      rw [sub_smul, ← add_sub_assoc]
      exact hw
    have hbound := ((T.cell w).mem_line_iff he y (s - t)).mp hline
    have hwJ : w ∈ J := ⟨hwS, hbound.2.1.trans_lt (sub_lt_self s hpos)⟩
    exact Set.mem_iUnion₂.mpr ⟨w, hwJ, hw⟩
  obtain ⟨w, hwJ, hzw⟩ := Set.mem_iUnion₂.mp (hC.mem_of_tendsto htend hmem)
  have hscore : (T.cell w).lowerFiber e he y < (T.cell v).lowerFiber e he y := hwJ.2
  have hwv : w ≠ v := by
    intro h
    subst w
    exact (lt_irrefl _) hscore
  have hzv : z ∈ (T.cell v).carrier :=
    ((T.cell v).mem_line_iff he y _).mpr ⟨hy.2.1, le_rfl, hy.2.2⟩
  have hyw : y ∈ (T.cell w).projectedBase e he := by
    rw [(T.cell w).projectedBase_eq_image he]
    exact ⟨z, hzw, (T.cell v).project_lowerEndpoint he hy⟩
  exact ⟨w, hwv, ⟨hzv, hzw⟩, hyw, hscore⟩

end BouRabeeGwynne.TilingData
