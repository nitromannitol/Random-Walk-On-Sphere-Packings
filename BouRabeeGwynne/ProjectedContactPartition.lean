-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/ProjectedContactPartition.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.FacetProjection
import BouRabeeGwynne.FacetPartition
import BouRabeeGwynne.Section3Projection
import BouRabeeGwynne.Section3ParallelFacetProjection
import BouRabeeGwynne.Section3ColumnTraversal

open scoped BigOperators ENNReal MeasureTheory
open MeasureTheory Filter

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

noncomputable def upperContactFinset (e : Euc d) (v : T.V)
    (hvD : (T.cell v).carrier ⊆ T.domain) : Finset T.V := by
  classical
  exact (T.toTilingData.contactFinset v hvD).filter
    (fun w => T.adj v w ∧ 0 < inner ℝ (T.pos w - T.pos v) e)

noncomputable def lowerContactFinset (e : Euc d) (v : T.V)
    (hvD : (T.cell v).carrier ⊆ T.domain) : Finset T.V := by
  classical
  exact (T.toTilingData.contactFinset v hvD).filter
    (fun w => T.adj v w ∧ inner ℝ (T.pos w - T.pos v) e < 0)

lemma ae_projected_contacts_transverse (hd : 1 ≤ d) (e : Euc d) (he : e ≠ 0)
    (v : T.V) (hvD : (T.cell v).carrier ⊆ T.domain) :
    ∀ᵐ y ∂μHE[d - 1], ∀ w ∈ T.toTilingData.contactFinset v hvD,
      y ∈ hyperplaneProjection e '' T.facet v w →
        T.adj v w ∧ inner ℝ (T.pos w - T.pos v) e ≠ 0 := by
  apply (Filter.eventually_all_finset _).mpr
  intro w hw
  by_cases hadj : T.adj v w
  · by_cases hn : inner ℝ (T.pos w - T.pos v) e = 0
    · have hz := T.projected_parallel_facet_measure_zero e he hadj
        (by rwa [real_inner_comm])
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with y hy
      exact fun h => (hy h).elim
    · exact Eventually.of_forall fun _ _ => ⟨hadj, hn⟩
  · have hne := ((T.toTilingData.mem_contactFinset hvD).mp hw).1.symm
    have hz : μHE[d - 1] (hyperplaneProjection e '' T.facet v w) = 0 := by
      apply le_antisymm _ zero_le
      calc
        μHE[d - 1] (hyperplaneProjection e '' T.facet v w) ≤ T.facetVolume v w :=
          T.projected_facet_measure_le e v w
        _ = 0 := T.toTilingData.facetVolume_eq_zero_of_not_adj hd hne hadj
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with y hy
    exact fun h => (hy h).elim

/-- Almost every line through a cell ends on a positive transverse actual contact. -/
theorem projectedBase_ae_eq_iUnion_upperContacts (hd : 1 ≤ d) {e : Euc d}
    (he : e ≠ 0) (v : T.V) (hvD : (T.cell v).carrier ⊆ interior T.domain) :
    (T.cell v).projectedBase e he =ᵐ[μHE[d - 1]]
      ⋃ w ∈ T.upperContactFinset e v (hvD.trans interior_subset),
        hyperplaneProjection e '' T.facet v w := by
  classical
  filter_upwards [T.ae_projected_contacts_transverse hd e he v (hvD.trans interior_subset)]
    with y hgood
  apply propext
  constructor
  · intro hy
    have hzv : (T.cell v).upperEndpoint e he y ∈ (T.cell v).carrier :=
      ((T.cell v).mem_line_iff he y _).mpr ⟨hy.2.1, hy.2.2, le_rfl⟩
    obtain ⟨w, hwv, hz, hyw, hgreater⟩ :=
      T.toTilingData.exists_touching_upperFiber_gt e he v hy (hvD hzv)
    have hw : w ∈ T.toTilingData.contactFinset v (hvD.trans interior_subset) :=
      (T.toTilingData.mem_contactFinset _).mpr ⟨hwv, ⟨_, hz⟩⟩
    have hyp : y ∈ hyperplaneProjection e '' T.facet v w :=
      ⟨_, hz, (T.cell v).project_upperEndpoint he hy⟩
    obtain ⟨hadj, hne⟩ := hgood w hw hyp
    have huzw : (T.cell w).upperEndpoint e he y ∈ (T.cell w).carrier :=
      ((T.cell w).mem_line_iff he y _).mpr ⟨hyw.2.1, hyw.2.2, le_rfl⟩
    have hn := (T.facet_normal_separation hd hadj hz).2.1 _ huzw
    have hdiff : (T.cell w).upperEndpoint e he y - (T.cell v).upperEndpoint e he y =
        ((T.cell w).upperFiber e he y - (T.cell v).upperFiber e he y) • e := by
      simp only [ConvexPolytope.upperEndpoint, sub_smul]
      abel
    rw [hdiff, inner_smul_right] at hn
    have hnonneg := (mul_nonneg_iff_of_pos_left (sub_pos.mpr hgreater)).mp hn
    have hpos := lt_of_le_of_ne hnonneg hne.symm
    exact Set.mem_iUnion₂.mpr ⟨w, Finset.mem_filter.mpr ⟨hw, hadj, hpos⟩, hyp⟩
  · intro hy
    obtain ⟨w, hw, hy⟩ := Set.mem_iUnion₂.mp hy
    exact T.project_facet_subset_projectedBase he v w hy

lemma upper_contact_projections_aedisjoint (hd : 1 ≤ d) {e : Euc d}
    (he : e ≠ 0) (v : T.V) (hvD : (T.cell v).carrier ⊆ T.domain) :
    Pairwise (fun w u : T.upperContactFinset e v hvD => AEDisjoint (μHE[d - 1])
      (hyperplaneProjection e '' T.facet v w)
      (hyperplaneProjection e '' T.facet v u)) := by
  classical
  intro w u hwu
  have hw := (Finset.mem_filter.mp w.property).2
  have hu := (Finset.mem_filter.mp u.property).2
  change μHE[d - 1] ((hyperplaneProjection e '' T.facet v w) ∩
    (hyperplaneProjection e '' T.facet v u)) = 0
  rw [T.project_facet_inter_of_pos hd he hw.1 hu.1 hw.2 hu.2]
  apply le_antisymm _ zero_le
  calc
    μHE[d - 1] (hyperplaneProjection e '' (T.facet v w ∩ T.facet v u)) ≤
        μHE[d - 1] (T.facet v w ∩ T.facet v u) :=
      lipschitzOne_euclideanHausdorffMeasure_image_le (hyperplaneProjection_lipschitz e) _
    _ = 0 := T.toTilingData.facet_inter_facet_measure_zero hd hw.1.1 hu.1.1
      (fun h => hwu (Subtype.ext h))

theorem projectedBase_restrict_eq_sum_upperContacts (hd : 1 ≤ d) {e : Euc d}
    (he : e ≠ 0) (v : T.V) (hvD : (T.cell v).carrier ⊆ interior T.domain) :
    (μHE[d - 1]).restrict ((T.cell v).projectedBase e he) =
      ∑ w ∈ T.upperContactFinset e v (hvD.trans interior_subset),
        (μHE[d - 1]).restrict (hyperplaneProjection e '' T.facet v w) := by
  classical
  let F := T.upperContactFinset e v (hvD.trans interior_subset)
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
    (T.projectedBase_ae_eq_iUnion_upperContacts hd he v hvD), hrep,
    Measure.restrict_iUnion_ae
      (T.upper_contact_projections_aedisjoint hd he v (hvD.trans interior_subset))]
  · exact Measure.sum_coe_finset F
      (fun w => (μHE[d - 1]).restrict (hyperplaneProjection e '' T.facet v w))
  · intro w
    exact (T.projected_facet_compact e v w).isClosed.measurableSet.nullMeasurableSet

/-- The corresponding lower endpoint is covered by a negative transverse contact. -/
theorem projectedBase_ae_eq_iUnion_lowerContacts (hd : 1 ≤ d) {e : Euc d}
    (he : e ≠ 0) (v : T.V) (hvD : (T.cell v).carrier ⊆ interior T.domain) :
    (T.cell v).projectedBase e he =ᵐ[μHE[d - 1]]
      ⋃ w ∈ T.lowerContactFinset e v (hvD.trans interior_subset),
        hyperplaneProjection e '' T.facet v w := by
  classical
  filter_upwards [T.ae_projected_contacts_transverse hd e he v (hvD.trans interior_subset)]
    with y hgood
  apply propext
  constructor
  · intro hy
    have hzv : (T.cell v).lowerEndpoint e he y ∈ (T.cell v).carrier :=
      ((T.cell v).mem_line_iff he y _).mpr ⟨hy.2.1, le_rfl, hy.2.2⟩
    obtain ⟨w, hwv, hz, hyw, hless⟩ :=
      T.toTilingData.exists_touching_lowerFiber_lt e he v hy (hvD hzv)
    have hw : w ∈ T.toTilingData.contactFinset v (hvD.trans interior_subset) :=
      (T.toTilingData.mem_contactFinset _).mpr ⟨hwv, ⟨_, hz⟩⟩
    have hyp : y ∈ hyperplaneProjection e '' T.facet v w :=
      ⟨_, hz, (T.cell v).project_lowerEndpoint he hy⟩
    obtain ⟨hadj, hne⟩ := hgood w hw hyp
    have hlzw : (T.cell w).lowerEndpoint e he y ∈ (T.cell w).carrier :=
      ((T.cell w).mem_line_iff he y _).mpr ⟨hyw.2.1, le_rfl, hyw.2.2⟩
    have hn := (T.facet_normal_separation hd hadj hz).2.1 _ hlzw
    have hdiff : (T.cell w).lowerEndpoint e he y - (T.cell v).lowerEndpoint e he y =
        ((T.cell w).lowerFiber e he y - (T.cell v).lowerFiber e he y) • e := by
      simp only [ConvexPolytope.lowerEndpoint, sub_smul]
      abel
    rw [hdiff, inner_smul_right] at hn
    have hnonpos : inner ℝ (T.pos w - T.pos v) e ≤ 0 := by
      by_contra h
      exact (not_lt_of_ge hn) (mul_neg_of_neg_of_pos (sub_neg.mpr hless) (lt_of_not_ge h))
    have hneg := lt_of_le_of_ne hnonpos hne
    exact Set.mem_iUnion₂.mpr ⟨w, Finset.mem_filter.mpr ⟨hw, hadj, hneg⟩, hyp⟩
  · intro hy
    obtain ⟨w, hw, hy⟩ := Set.mem_iUnion₂.mp hy
    exact T.project_facet_subset_projectedBase he v w hy

lemma lower_contact_projections_aedisjoint (hd : 1 ≤ d) {e : Euc d}
    (he : e ≠ 0) (v : T.V) (hvD : (T.cell v).carrier ⊆ T.domain) :
    Pairwise (fun w u : T.lowerContactFinset e v hvD => AEDisjoint (μHE[d - 1])
      (hyperplaneProjection e '' T.facet v w)
      (hyperplaneProjection e '' T.facet v u)) := by
  classical
  intro w u hwu
  have hw := (Finset.mem_filter.mp w.property).2
  have hu := (Finset.mem_filter.mp u.property).2
  change μHE[d - 1] ((hyperplaneProjection e '' T.facet v w) ∩
    (hyperplaneProjection e '' T.facet v u)) = 0
  rw [T.project_facet_inter_of_neg hd he hw.1 hu.1 hw.2 hu.2]
  apply le_antisymm _ zero_le
  calc
    μHE[d - 1] (hyperplaneProjection e '' (T.facet v w ∩ T.facet v u)) ≤
        μHE[d - 1] (T.facet v w ∩ T.facet v u) :=
      lipschitzOne_euclideanHausdorffMeasure_image_le (hyperplaneProjection_lipschitz e) _
    _ = 0 := T.toTilingData.facet_inter_facet_measure_zero hd hw.1.1 hu.1.1
      (fun h => hwu (Subtype.ext h))

theorem projectedBase_restrict_eq_sum_lowerContacts (hd : 1 ≤ d) {e : Euc d}
    (he : e ≠ 0) (v : T.V) (hvD : (T.cell v).carrier ⊆ interior T.domain) :
    (μHE[d - 1]).restrict ((T.cell v).projectedBase e he) =
      ∑ w ∈ T.lowerContactFinset e v (hvD.trans interior_subset),
        (μHE[d - 1]).restrict (hyperplaneProjection e '' T.facet v w) := by
  classical
  let F := T.lowerContactFinset e v (hvD.trans interior_subset)
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
    (T.projectedBase_ae_eq_iUnion_lowerContacts hd he v hvD), hrep,
    Measure.restrict_iUnion_ae
      (T.lower_contact_projections_aedisjoint hd he v (hvD.trans interior_subset))]
  · exact Measure.sum_coe_finset F
      (fun w => (μHE[d - 1]).restrict (hyperplaneProjection e '' T.facet v w))
  · intro w
    exact (T.projected_facet_compact e v w).isClosed.measurableSet.nullMeasurableSet

theorem integral_projectedBase_eq_sum_upperContacts (hd : 1 ≤ d) {e : Euc d}
    (he : e ≠ 0) (v : T.V) (hvD : (T.cell v).carrier ⊆ interior T.domain)
    {f : Euc d → ℝ} (hf : IntegrableOn f ((T.cell v).projectedBase e he) (μHE[d - 1])) :
    (∫ y in (T.cell v).projectedBase e he, f y ∂μHE[d - 1]) =
      ∑ w ∈ T.upperContactFinset e v (hvD.trans interior_subset),
        ∫ y in hyperplaneProjection e '' T.facet v w, f y ∂μHE[d - 1] := by
  rw [T.projectedBase_restrict_eq_sum_upperContacts hd he v hvD]
  apply integral_finsetSum_measure
  intro w _
  exact hf.mono_set (T.project_facet_subset_projectedBase he v w)

theorem integral_projectedBase_eq_sum_lowerContacts (hd : 1 ≤ d) {e : Euc d}
    (he : e ≠ 0) (v : T.V) (hvD : (T.cell v).carrier ⊆ interior T.domain)
    {f : Euc d → ℝ} (hf : IntegrableOn f ((T.cell v).projectedBase e he) (μHE[d - 1])) :
    (∫ y in (T.cell v).projectedBase e he, f y ∂μHE[d - 1]) =
      ∑ w ∈ T.lowerContactFinset e v (hvD.trans interior_subset),
        ∫ y in hyperplaneProjection e '' T.facet v w, f y ∂μHE[d - 1] := by
  rw [T.projectedBase_restrict_eq_sum_lowerContacts hd he v hvD]
  apply integral_finsetSum_measure
  intro w _
  exact hf.mono_set (T.project_facet_subset_projectedBase he v w)

end BouRabeeGwynne.OrthogonalTiling
