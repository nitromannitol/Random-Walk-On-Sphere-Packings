module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/PyramidOverlap.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.DualNull
public import BouRabeeGwynne.TripleContact

@[expose] public section

open scoped ENNReal MeasureTheory
open MeasureTheory

namespace BouRabeeGwynne.TilingData

variable {d : ℕ} (T : TilingData d)

/-- Two contact pyramids in the same primal cell overlap only in the pyramid
over the intersection of their bases. Strict separation at the marked point
forces the two radial parameters to agree. -/
theorem cellPyramid_inter_subset_cone_contact_inter {v w u : T.V}
    (hvw : T.adj v w) (hvu : T.adj v u) :
    T.cellPyramid v w ∩ T.cellPyramid v u ⊆
      convexHull ℝ (insert (T.pos v) (T.facet v w ∩ T.facet v u)) := by
  intro x hx
  have hxw := hx.1
  have hxu := hx.2
  rw [cellPyramid, convexHull_insert_eq_segment_image (T.pos v)
    (T.facet_convex v w) hvw.2.1] at hxw
  rw [cellPyramid, convexHull_insert_eq_segment_image (T.pos v)
    (T.facet_convex v u) hvu.2.1] at hxu
  obtain ⟨⟨t, b⟩, ⟨ht, hb⟩, htx⟩ := hxw
  obtain ⟨⟨s, c⟩, ⟨hs, hc⟩, hsx⟩ := hxu
  have hrepr : (1 - t) • T.pos v + t • b = (1 - s) • T.pos v + s • c :=
    htx.trans hsx.symm
  obtain ⟨f, af, hfV, hfW, hfv, _⟩ := T.exists_cell_separator hvw.1
  obtain ⟨g, ag, hgV, hgU, hgv, _⟩ := T.exists_cell_separator hvu.1
  have hfb : f b = af := le_antisymm (hfV b hb.1) (hfW b hb.2)
  have hfc : f c ≤ af := hfV c hc.1
  have hgc : g c = ag := le_antisymm (hgV c hc.1) (hgU c hc.2)
  have hgb : g b ≤ ag := hgV b hb.1
  have hfEq := congrArg f hrepr
  have hgEq := congrArg g hrepr
  simp only [map_add, map_smul, smul_eq_mul, hfb] at hfEq
  simp only [map_add, map_smul, smul_eq_mul, hgc] at hgEq
  have hts : t ≤ s := by
    by_contra hnot
    have hpos := mul_pos (sub_pos.mpr (lt_of_not_ge hnot)) (sub_pos.mpr hfv)
    have hn := mul_nonneg hs.1 (sub_nonneg.mpr hfc)
    nlinarith
  have hst : s ≤ t := by
    by_contra hnot
    have hpos := mul_pos (sub_pos.mpr (lt_of_not_ge hnot)) (sub_pos.mpr hgv)
    have hn := mul_nonneg ht.1 (sub_nonneg.mpr hgb)
    nlinarith
  have htsEq := le_antisymm hts hst
  subst s
  by_cases ht0 : t = 0
  · have hxpos : x = T.pos v := by simpa [ht0] using htx.symm
    rw [hxpos]
    exact subset_convexHull ℝ _ (Set.mem_insert _ _)
  · have hbc : b = c := (smul_right_injective _ ht0) (add_left_cancel hrepr)
    have hbBoth : b ∈ T.facet v w ∩ T.facet v u := ⟨hb, by rw [hbc]; exact hc⟩
    apply (convex_convexHull ℝ _).segment_subset
      (subset_convexHull ℝ _ (Set.mem_insert _ _))
      (subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hbBoth))
    rw [segment_eq_image]
    exact ⟨t, ht, htx⟩

/-- Distinct incident dual halves overlap in zero full-dimensional volume.
This is the local no-double-counting fact for sums of dual volumes. -/
theorem cellPyramid_inter_measure_zero (hd : 1 ≤ d) {v w u : T.V}
    (hvw : T.adj v w) (hvu : T.adj v u) (hwu : w ≠ u) :
    μHE[d] (T.cellPyramid v w ∩ T.cellPyramid v u) = 0 := by
  let S := T.facet v w ∩ T.facet v u
  have hS : IsCompact S := (T.facet_compact v w).inter_right (T.facet_compact v u).isClosed
  have hconv : Convex ℝ S := (T.facet_convex v w).inter (T.facet_convex v u)
  have hnull : μHE[d] (convexHull ℝ (insert (T.pos v) S)) = 0 := by
    rcases S.eq_empty_or_nonempty with hempty | hne
    · rw [hempty]
      rw [insert_empty_eq, convexHull_singleton]
      apply euclideanHausdorffMeasure_eq_zero_of_affineSpan_rank_lt
        isCompact_singleton (convex_singleton _) (Set.singleton_nonempty _)
      rw [direction_affineSpan, vectorSpan_singleton]
      simpa using (Nat.lt_of_lt_of_le Nat.zero_lt_one hd)
    · have hset : S = T.facet v w ∩ (T.cell u).carrier := by
        ext x
        simp only [S, facet, Set.mem_inter_iff]
        tauto
      have hrank : Module.finrank ℝ (affineSpan ℝ S).direction < d - 1 := by
        rw [hset] at hne ⊢
        exact T.triple_contact_rank_lt hd hvw.1 hvu.1 hwu hne
      have hcone : Module.finrank ℝ
          (affineSpan ℝ (convexHull ℝ (insert (T.pos v) S))).direction ≤
          Module.finrank ℝ (affineSpan ℝ S).direction + 1 := by
        rw [affineSpan_convexHull, direction_affineSpan, direction_affineSpan]
        exact finrank_vectorSpan_insert_le_set ℝ S (T.pos v)
      apply euclideanHausdorffMeasure_eq_zero_of_affineSpan_rank_lt
        (isCompact_convexHull_insert_of_convex (T.pos v) hS hconv)
        (convex_convexHull ℝ _)
        ⟨T.pos v, subset_convexHull ℝ _ (Set.mem_insert _ _)⟩
      omega
  exact measure_mono_null (T.cellPyramid_inter_subset_cone_contact_inter hvw hvu) hnull

end BouRabeeGwynne.TilingData
