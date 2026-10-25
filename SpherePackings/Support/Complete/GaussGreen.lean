module

-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (files `BouRabeeGwynne/ProjectedContactPartition.lean` and `BouRabeeGwynne/PolytopeGaussGreen.lean` at
-- commit cf73d6e): the contact partition and the Gauss--Green identity, for complete cells.
public import SpherePackings.Support.Complete.Basic
public import SpherePackings.Support.Complete.Fibers
public import BouRabeeGwynne.PolytopeGaussGreen

@[expose] public section

/-!
# Gauss–Green on a complete cell

leobon12's polytope Gauss–Green identity (`BouRabeeGwynne/PolytopeGaussGreen.lean`) for a cell in the
interior of the ambient set, re-proved for a complete cell (`CompleteCell`): almost every line in a
direction `e` meets the cell in a nondegenerate segment (`ae_lowerFiber_lt_upperFiber`), whose upper
endpoint lies on the boundary, hence in the contact with a neighbour, and the separation of the two
cells by that contact makes the neighbour an upper one.
-/

namespace SpherePackings

open BouRabeeGwynne BouRabeeGwynne.OrthogonalTiling MeasureTheory

open scoped Laplacian

variable {d : ℕ}

/-- The neighbours of `v` on the positive side in the direction `e`. -/
noncomputable def upperNeighborFinset (T : OrthogonalTiling d) (e : Euc d) (v : T.V)
    (hv : (T.neighbors v).Finite) : Finset T.V := by
  classical
  exact (T.neighborFinset v hv).filter (fun w => 0 < inner ℝ (T.pos w - T.pos v) e)

/-- The neighbours of `v` on the negative side in the direction `e`. -/
noncomputable def lowerNeighborFinset (T : OrthogonalTiling d) (e : Euc d) (v : T.V)
    (hv : (T.neighbors v).Finite) : Finset T.V := by
  classical
  exact (T.neighborFinset v hv).filter (fun w => inner ℝ (T.pos w - T.pos v) e < 0)

private lemma upperNeighborFinset_eq_filter (T : OrthogonalTiling d) (e : Euc d) (v : T.V)
    (hv : (T.neighbors v).Finite) :
    upperNeighborFinset T e v hv =
      (T.neighborFinset v hv).filter (fun w => 0 < inner ℝ (T.pos w - T.pos v) e) :=
  rfl

private lemma lowerNeighborFinset_eq_filter (T : OrthogonalTiling d) (e : Euc d) (v : T.V)
    (hv : (T.neighbors v).Finite) :
    lowerNeighborFinset T e v hv =
      (T.neighborFinset v hv).filter (fun w => inner ℝ (T.pos w - T.pos v) e < 0) :=
  rfl

/-- Almost every point of the projected base avoids the parallel neighbours of a complete cell:
if `y` lies in the projection of a contact with a neighbour, that contact is transverse to `e`. -/
private lemma ae_neighborFinset_transverse {e : Euc d} (he : e ≠ 0) (T : OrthogonalTiling d)
    {v : T.V} (hv : CompleteCell T v) :
    ∀ᵐ y ∂(μHE[d - 1] : Measure (Euc d)), ∀ w ∈ T.neighborFinset v hv.1,
      y ∈ hyperplaneProjection e '' T.facet v w → inner ℝ (T.pos w - T.pos v) e ≠ 0 := by
  apply (Filter.eventually_all_finset _).mpr
  intro w hw
  have hadj := (T.mem_neighborFinset hv.1).mp hw
  by_cases hn : inner ℝ (T.pos w - T.pos v) e = 0
  · have hz := T.projected_parallel_facet_measure_zero e he hadj (by rwa [real_inner_comm])
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with y hy
    exact fun h => (hy h).elim
  · exact Filter.Eventually.of_forall fun _ _ => hn

/-- Almost every line through a complete cell leaves it through the contact with an upper
neighbour. -/
theorem projectedBase_ae_eq_iUnion_upperNeighbors (hd : 1 ≤ d) (T : OrthogonalTiling d)
    {e : Euc d} (he : e ≠ 0) {v : T.V} (hv : CompleteCell T v) :
    (T.cell v).projectedBase e he =ᵐ[μHE[d - 1]]
      ⋃ w ∈ upperNeighborFinset T e v hv.1, hyperplaneProjection e '' T.facet v w := by
  filter_upwards [ae_lowerFiber_lt_upperFiber (T.cell v) he,
    ae_neighborFinset_transverse he T hv] with y hlt hgood
  apply propext
  constructor
  · intro hy
    have hz : (T.cell v).upperEndpoint e he y ∈ frontier (T.cell v).carrier :=
      (T.cell v).upperEndpoint_mem_frontier he hy
    rw [hv.frontier_eq] at hz
    obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.mp hz
    have hwN : w ∈ T.neighborFinset v hv.1 := (T.mem_neighborFinset hv.1).mpr hw
    have hyp : y ∈ hyperplaneProjection e '' T.facet v w :=
      ⟨_, hzw, (T.cell v).project_upperEndpoint he hy⟩
    have hne := hgood w hwN hyp
    have hadj := (T.mem_neighborFinset hv.1).mp hwN
    have hzlow : (T.cell v).lowerEndpoint e he y ∈ (T.cell v).carrier :=
      ((T.cell v).mem_line_iff he y _).mpr ⟨hy.2.1, le_rfl, hy.2.2⟩
    have hn := (T.facet_normal_separation hd hadj hzw).1 _ hzlow
    have hdiff : (T.cell v).lowerEndpoint e he y - (T.cell v).upperEndpoint e he y =
        ((T.cell v).lowerFiber e he y - (T.cell v).upperFiber e he y) • e := by
      simp only [ConvexPolytope.lowerEndpoint, ConvexPolytope.upperEndpoint, sub_smul]
      abel
    rw [hdiff, inner_smul_right] at hn
    have hnonneg : 0 ≤ inner ℝ (T.pos w - T.pos v) e := by
      by_contra hneg
      have := mul_pos_of_neg_of_neg (sub_neg.mpr (hlt hy)) (not_le.mp hneg)
      linarith
    have hpos := lt_of_le_of_ne hnonneg hne.symm
    exact Set.mem_iUnion₂.mpr ⟨w, Finset.mem_filter.mpr ⟨hwN, hpos⟩, hyp⟩
  · intro hy
    obtain ⟨w, -, hy⟩ := Set.mem_iUnion₂.mp hy
    exact T.project_facet_subset_projectedBase he v w hy

/-- Almost every line through a complete cell enters it through the contact with a lower
neighbour. -/
theorem projectedBase_ae_eq_iUnion_lowerNeighbors (hd : 1 ≤ d) (T : OrthogonalTiling d)
    {e : Euc d} (he : e ≠ 0) {v : T.V} (hv : CompleteCell T v) :
    (T.cell v).projectedBase e he =ᵐ[μHE[d - 1]]
      ⋃ w ∈ lowerNeighborFinset T e v hv.1, hyperplaneProjection e '' T.facet v w := by
  filter_upwards [ae_lowerFiber_lt_upperFiber (T.cell v) he,
    ae_neighborFinset_transverse he T hv] with y hlt hgood
  apply propext
  constructor
  · intro hy
    have hz : (T.cell v).lowerEndpoint e he y ∈ frontier (T.cell v).carrier :=
      (T.cell v).lowerEndpoint_mem_frontier he hy
    rw [hv.frontier_eq] at hz
    obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.mp hz
    have hwN : w ∈ T.neighborFinset v hv.1 := (T.mem_neighborFinset hv.1).mpr hw
    have hyp : y ∈ hyperplaneProjection e '' T.facet v w :=
      ⟨_, hzw, (T.cell v).project_lowerEndpoint he hy⟩
    have hne := hgood w hwN hyp
    have hadj := (T.mem_neighborFinset hv.1).mp hwN
    have hzup : (T.cell v).upperEndpoint e he y ∈ (T.cell v).carrier :=
      ((T.cell v).mem_line_iff he y _).mpr ⟨hy.2.1, hy.2.2, le_rfl⟩
    have hn := (T.facet_normal_separation hd hadj hzw).1 _ hzup
    have hdiff : (T.cell v).upperEndpoint e he y - (T.cell v).lowerEndpoint e he y =
        ((T.cell v).upperFiber e he y - (T.cell v).lowerFiber e he y) • e := by
      simp only [ConvexPolytope.lowerEndpoint, ConvexPolytope.upperEndpoint, sub_smul]
      abel
    rw [hdiff, inner_smul_right] at hn
    have hnonpos : inner ℝ (T.pos w - T.pos v) e ≤ 0 := by
      by_contra hpos
      have := mul_pos (sub_pos.mpr (hlt hy)) (not_le.mp hpos)
      linarith
    have hneg := lt_of_le_of_ne hnonpos hne
    exact Set.mem_iUnion₂.mpr ⟨w, Finset.mem_filter.mpr ⟨hwN, hneg⟩, hyp⟩
  · intro hy
    obtain ⟨w, -, hy⟩ := Set.mem_iUnion₂.mp hy
    exact T.project_facet_subset_projectedBase he v w hy

/-- The projections of two distinct upper neighbour contacts of a complete cell overlap in a null
set. -/
private lemma upper_neighbor_projections_aedisjoint (hd : 1 ≤ d) (T : OrthogonalTiling d)
    {e : Euc d} (he : e ≠ 0) {v : T.V} (hv : CompleteCell T v) :
    Pairwise (fun w u : upperNeighborFinset T e v hv.1 => AEDisjoint (μHE[d - 1])
      (hyperplaneProjection e '' T.facet v w)
      (hyperplaneProjection e '' T.facet v u)) := by
  classical
  intro w u hwu
  have hw := Finset.mem_filter.mp w.property
  have hu := Finset.mem_filter.mp u.property
  have hadjw := (T.mem_neighborFinset hv.1).mp hw.1
  have hadju := (T.mem_neighborFinset hv.1).mp hu.1
  change μHE[d - 1] ((hyperplaneProjection e '' T.facet v w) ∩
    (hyperplaneProjection e '' T.facet v u)) = 0
  rw [T.project_facet_inter_of_pos hd he hadjw hadju hw.2 hu.2]
  apply le_antisymm _ zero_le
  calc
    μHE[d - 1] (hyperplaneProjection e '' (T.facet v w ∩ T.facet v u)) ≤
        μHE[d - 1] (T.facet v w ∩ T.facet v u) :=
      lipschitzOne_euclideanHausdorffMeasure_image_le (hyperplaneProjection_lipschitz e) _
    _ = 0 := T.toTilingData.facet_inter_facet_measure_zero hd hadjw.1 hadju.1
      (fun h => hwu (Subtype.ext h))

private lemma lower_neighbor_projections_aedisjoint (hd : 1 ≤ d) (T : OrthogonalTiling d)
    {e : Euc d} (he : e ≠ 0) {v : T.V} (hv : CompleteCell T v) :
    Pairwise (fun w u : lowerNeighborFinset T e v hv.1 => AEDisjoint (μHE[d - 1])
      (hyperplaneProjection e '' T.facet v w)
      (hyperplaneProjection e '' T.facet v u)) := by
  classical
  intro w u hwu
  have hw := Finset.mem_filter.mp w.property
  have hu := Finset.mem_filter.mp u.property
  have hadjw := (T.mem_neighborFinset hv.1).mp hw.1
  have hadju := (T.mem_neighborFinset hv.1).mp hu.1
  change μHE[d - 1] ((hyperplaneProjection e '' T.facet v w) ∩
    (hyperplaneProjection e '' T.facet v u)) = 0
  rw [T.project_facet_inter_of_neg hd he hadjw hadju hw.2 hu.2]
  apply le_antisymm _ zero_le
  calc
    μHE[d - 1] (hyperplaneProjection e '' (T.facet v w ∩ T.facet v u)) ≤
        μHE[d - 1] (T.facet v w ∩ T.facet v u) :=
      lipschitzOne_euclideanHausdorffMeasure_image_le (hyperplaneProjection_lipschitz e) _
    _ = 0 := T.toTilingData.facet_inter_facet_measure_zero hd hadjw.1 hadju.1
      (fun h => hwu (Subtype.ext h))

private lemma projectedBase_restrict_eq_sum_upperNeighbors (hd : 1 ≤ d) (T : OrthogonalTiling d)
    {e : Euc d} (he : e ≠ 0) {v : T.V} (hv : CompleteCell T v) :
    (μHE[d - 1]).restrict ((T.cell v).projectedBase e he) =
      ∑ w ∈ upperNeighborFinset T e v hv.1,
        (μHE[d - 1]).restrict (hyperplaneProjection e '' T.facet v w) := by
  classical
  let F := upperNeighborFinset T e v hv.1
  have hrep : (⋃ w ∈ F, hyperplaneProjection e '' T.facet v w) =
      ⋃ w : F, hyperplaneProjection e '' T.facet v w := by
    ext y
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨w, hw, hy⟩
      exact ⟨⟨w, hw⟩, hy⟩
    · rintro ⟨w, hy⟩
      exact ⟨w.val, w.property, hy⟩
  rw [Measure.restrict_congr_set
    (projectedBase_ae_eq_iUnion_upperNeighbors hd T he hv), hrep,
    Measure.restrict_iUnion_ae (upper_neighbor_projections_aedisjoint hd T he hv)]
  · exact Measure.sum_coe_finset F
      (fun w => (μHE[d - 1]).restrict (hyperplaneProjection e '' T.facet v w))
  · intro w
    exact (T.projected_facet_compact e v w).isClosed.measurableSet.nullMeasurableSet

private lemma projectedBase_restrict_eq_sum_lowerNeighbors (hd : 1 ≤ d) (T : OrthogonalTiling d)
    {e : Euc d} (he : e ≠ 0) {v : T.V} (hv : CompleteCell T v) :
    (μHE[d - 1]).restrict ((T.cell v).projectedBase e he) =
      ∑ w ∈ lowerNeighborFinset T e v hv.1,
        (μHE[d - 1]).restrict (hyperplaneProjection e '' T.facet v w) := by
  classical
  let F := lowerNeighborFinset T e v hv.1
  have hrep : (⋃ w ∈ F, hyperplaneProjection e '' T.facet v w) =
      ⋃ w : F, hyperplaneProjection e '' T.facet v w := by
    ext y
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨w, hw, hy⟩
      exact ⟨⟨w, hw⟩, hy⟩
    · rintro ⟨w, hy⟩
      exact ⟨w.val, w.property, hy⟩
  rw [Measure.restrict_congr_set
    (projectedBase_ae_eq_iUnion_lowerNeighbors hd T he hv), hrep,
    Measure.restrict_iUnion_ae (lower_neighbor_projections_aedisjoint hd T he hv)]
  · exact Measure.sum_coe_finset F
      (fun w => (μHE[d - 1]).restrict (hyperplaneProjection e '' T.facet v w))
  · intro w
    exact (T.projected_facet_compact e v w).isClosed.measurableSet.nullMeasurableSet

theorem integral_projectedBase_eq_sum_upperNeighbors (hd : 1 ≤ d) (T : OrthogonalTiling d)
    {e : Euc d} (he : e ≠ 0) {v : T.V} (hv : CompleteCell T v) {f : Euc d → ℝ}
    (hf : IntegrableOn f ((T.cell v).projectedBase e he) (μHE[d - 1])) :
    (∫ y in (T.cell v).projectedBase e he, f y ∂μHE[d - 1]) =
      ∑ w ∈ upperNeighborFinset T e v hv.1,
        ∫ y in hyperplaneProjection e '' T.facet v w, f y ∂μHE[d - 1] := by
  rw [projectedBase_restrict_eq_sum_upperNeighbors hd T he hv]
  apply integral_finsetSum_measure
  intro w _
  exact hf.mono_set (T.project_facet_subset_projectedBase he v w)

theorem integral_projectedBase_eq_sum_lowerNeighbors (hd : 1 ≤ d) (T : OrthogonalTiling d)
    {e : Euc d} (he : e ≠ 0) {v : T.V} (hv : CompleteCell T v) {f : Euc d → ℝ}
    (hf : IntegrableOn f ((T.cell v).projectedBase e he) (μHE[d - 1])) :
    (∫ y in (T.cell v).projectedBase e he, f y ∂μHE[d - 1]) =
      ∑ w ∈ lowerNeighborFinset T e v hv.1,
        ∫ y in hyperplaneProjection e '' T.facet v w, f y ∂μHE[d - 1] := by
  rw [projectedBase_restrict_eq_sum_lowerNeighbors hd T he hv]
  apply integral_finsetSum_measure
  intro w _
  exact hf.mono_set (T.project_facet_subset_projectedBase he v w)

/-- The coordinate flux identity for a complete cell in dimension `n + 1`: the analogue of
`sum_coordinate_contact_integral_eq_integral_fderiv` with the neighbour contacts in place of the
actual cell contacts. -/
private lemma sum_coordinate_neighbor_integral_eq_integral_fderiv {n : ℕ}
    (T : OrthogonalTiling (n + 1)) (i : Fin (n + 1)) (v : T.V) (hv : CompleteCell T v)
    {W : Set (Euc (n + 1))} (hW : IsOpen W) (hPW : (T.cell v).carrier ⊆ W)
    {f : Euc (n + 1) → ℝ} (hf : ContDiffOn ℝ 1 f W) :
    (∑ w ∈ T.neighborFinset v hv.1,
      ∫ x in T.facet v w, ((T.pos w - T.pos v) i / ‖T.pos w - T.pos v‖) * f x ∂μHE[n]) =
        ∫ x in (T.cell v).carrier, (fderiv ℝ f x) (coordinateAxis i) ∂volume := by
  classical
  let e := coordinateAxis i
  let he := coordinateAxis_ne_zero i
  let P := T.cell v
  let N := T.neighborFinset v hv.1
  let U : T.V → ℝ := fun w => ∫ y in hyperplaneProjection e '' T.facet v w,
    f (P.upperEndpoint e he y) ∂μHE[n]
  let L : T.V → ℝ := fun w => ∫ y in hyperplaneProjection e '' T.facet v w,
    f (P.lowerEndpoint e he y) ∂μHE[n]
  have hterm (w : T.V) (hw : w ∈ N) :
      (∫ x in T.facet v w, ((T.pos w - T.pos v) i / ‖T.pos w - T.pos v‖) * f x ∂μHE[n]) =
        (if 0 < (T.pos w - T.pos v) i then U w else 0) -
          (if (T.pos w - T.pos v) i < 0 then L w else 0) := by
    have hadj := (T.mem_neighborFinset hv.1).mp hw
    rcases lt_trichotomy 0 ((T.pos w - T.pos v) i) with hp | hz | hn
    · simp only [hp, not_lt_of_ge hp.le, ↓reduceIte, sub_zero]
      exact T.integral_upper_contact_eq_projection i hadj hp f
    · simp only [← hz, div_eq_mul_inv, zero_mul, integral_zero, lt_self_iff_false,
        ↓reduceIte, sub_zero]
    · simp only [hn, not_lt_of_ge hn.le, ↓reduceIte, zero_sub]
      exact T.integral_lower_contact_eq_projection i hadj hn f
  have hupper := integral_projectedBase_eq_sum_upperNeighbors (by omega) T he hv
    (T.integrableOn_upperEndpoint i v (hf.continuousOn.mono hPW))
  have hlower := integral_projectedBase_eq_sum_lowerNeighbors (by omega) T he hv
    (T.integrableOn_lowerEndpoint i v (hf.continuousOn.mono hPW))
  rw [upperNeighborFinset_eq_filter T e v hv.1, Finset.sum_filter] at hupper
  rw [lowerNeighborFinset_eq_filter T e v hv.1, Finset.sum_filter] at hlower
  simp only [e, inner_coordinateAxis_right] at hupper hlower
  calc
    _ = ∑ w ∈ N, ((if 0 < (T.pos w - T.pos v) i then U w else 0) -
        (if (T.pos w - T.pos v) i < 0 then L w else 0)) := Finset.sum_congr rfl hterm
    _ = (∫ y in P.projectedBase e he, f (P.upperEndpoint e he y) ∂μHE[n]) -
        (∫ y in P.projectedBase e he, f (P.lowerEndpoint e he y) ∂μHE[n]) := by
      rw [Finset.sum_sub_distrib]
      exact congrArg₂ (· - ·) hupper.symm hlower.symm
    _ = ∫ y in P.projectedBase e he,
        f (P.upperEndpoint e he y) - f (P.lowerEndpoint e he y) ∂μHE[n] :=
      (integral_sub (T.integrableOn_upperEndpoint i v (hf.continuousOn.mono hPW))
        (T.integrableOn_lowerEndpoint i v (hf.continuousOn.mono hPW))).symm
    _ = _ := (P.integral_coordinate_fderiv_eq_endpoint_integral i hW hPW hf).symm

/-- Gauss–Green for a complete cell in dimension `n + 1`: the analogue of
`sum_surfaceFlux_eq_integral_laplacian_succ`. -/
private lemma sum_surfaceFlux_eq_integral_laplacian_succ_of_complete {n : ℕ}
    (T : OrthogonalTiling (n + 1)) (v : T.V) (hv : CompleteCell T v) {W : Set (Euc (n + 1))}
    (hW : IsOpen W) (hPW : (T.cell v).carrier ⊆ W)
    {h : Euc (n + 1) → ℝ} (hh : ContDiffOn ℝ 2 h W) :
    (∑ w ∈ T.neighborFinset v hv.1, T.surfaceFlux h v w) =
      ∫ x in (T.cell v).carrier, Δ h x ∂volume := by
  have hD (i : Fin (n + 1)) : ContDiffOn ℝ 1
      (fun y => (fderiv ℝ h y) (coordinateAxis i)) W :=
    contDiffOn_directional_fderiv hW hh _
  have hint (i : Fin (n + 1)) : IntegrableOn
      (fun x => (fderiv ℝ (fun y => (fderiv ℝ h y) (coordinateAxis i)) x)
        (coordinateAxis i)) (T.cell v).carrier :=
    ((((hD i).continuousOn_fderiv_of_isOpen hW le_rfl).clm_apply
      continuousOn_const).mono hPW).integrableOn_compact (T.cell v).compact
  calc
    _ = ∑ w ∈ T.neighborFinset v hv.1, ∑ i : Fin (n + 1),
        ∫ x in T.facet v w, ((T.pos w - T.pos v) i / ‖T.pos w - T.pos v‖) *
          (fderiv ℝ h x) (coordinateAxis i) ∂μHE[n] := by
      apply Finset.sum_congr rfl
      intro w hw
      exact T.surfaceFlux_eq_sum_coordinate_contact_integral h
        ((T.mem_neighborFinset hv.1).mp hw) hW hh (fun x hx => hPW hx.1)
    _ = ∑ i : Fin (n + 1), ∑ w ∈ T.neighborFinset v hv.1,
        ∫ x in T.facet v w, ((T.pos w - T.pos v) i / ‖T.pos w - T.pos v‖) *
          (fderiv ℝ h x) (coordinateAxis i) ∂μHE[n] := Finset.sum_comm
    _ = ∑ i : Fin (n + 1), ∫ x in (T.cell v).carrier,
        (fderiv ℝ (fun y => (fderiv ℝ h y) (coordinateAxis i)) x)
          (coordinateAxis i) ∂volume := by
      apply Finset.sum_congr rfl
      intro i _
      exact sum_coordinate_neighbor_integral_eq_integral_fderiv T i v hv hW hPW (hD i)
    _ = ∫ x in (T.cell v).carrier, ∑ i : Fin (n + 1),
        (fderiv ℝ (fun y => (fderiv ℝ h y) (coordinateAxis i)) x)
          (coordinateAxis i) ∂volume := (integral_finsetSum _ (fun i _ => hint i)).symm
    _ = _ := by
      apply setIntegral_congr_fun (T.cell v).compact.measurableSet
      intro x hx
      exact (laplacian_eq_sum_coordinate_second hW hh (hPW hx)).symm

/-- Gauss–Green for a complete cell, with its contacts and mathlib's Laplacian. -/
theorem sum_surfaceFlux_eq_integral_laplacian_of_complete (hd : 1 ≤ d) (T : OrthogonalTiling d)
    {v : T.V} (hv : CompleteCell T v) {W : Set (Euc d)} (hW : IsOpen W)
    (hPW : (T.cell v).carrier ⊆ W) {h : Euc d → ℝ} (hh : ContDiffOn ℝ 2 h W) :
    (∑ w ∈ T.neighborFinset v hv.1, T.surfaceFlux h v w) =
      ∫ x in (T.cell v).carrier, Δ h x ∂volume := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  exact sum_surfaceFlux_eq_integral_laplacian_succ_of_complete T v hv hW hPW hh

/-- The contact fluxes of a function `C²` near a complete cell and harmonic on it sum to zero. -/
theorem sum_surfaceFlux_eq_zero_of_complete (hd : 1 ≤ d) (T : OrthogonalTiling d)
    {v : T.V} (hv : CompleteCell T v) {W : Set (Euc d)} (hW : IsOpen W)
    (hPW : (T.cell v).carrier ⊆ W) {h : Euc d → ℝ} (hh : ContDiffOn ℝ 2 h W)
    (hharm : ∀ x ∈ (T.cell v).carrier, Δ h x = 0) :
    (∑ w ∈ T.neighborFinset v hv.1, T.surfaceFlux h v w) = 0 := by
  rw [sum_surfaceFlux_eq_integral_laplacian_of_complete hd T hv hW hPW hh]
  exact setIntegral_eq_zero_of_forall_eq_zero hharm

end SpherePackings
