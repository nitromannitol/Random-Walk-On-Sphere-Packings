module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/FacetProjection.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.SupportFaceProjection
public import BouRabeeGwynne.FacetNormals
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# Projecting actual cell contacts along a transverse direction

Every point of an outward-facing contact is the upper endpoint of its cell's
fiber. These statements use all codimension-one contacts, including partial
facets; no common halfspace presentation or face-to-face property is required.
-/

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

lemma project_facet_subset_projectedBase {e : Euc d} (he : e ≠ 0) (v w : T.V) :
    hyperplaneProjection e '' T.facet v w ⊆ (T.cell v).projectedBase e he := by
  rw [(T.cell v).projectedBase_eq_image he]
  exact Set.image_mono Set.inter_subset_left

lemma upperFiber_eq_lineParameter_of_mem_facet (hd : 1 ≤ d)
    {e : Euc d} (he : e ≠ 0) {v w : T.V} (hvw : T.adj v w)
    (hn : 0 < inner ℝ (T.pos w - T.pos v) e)
    {x : Euc d} (hx : x ∈ T.facet v w) :
    (T.cell v).upperFiber e he (hyperplaneProjection e x) =
      inner ℝ e x / inner ℝ e e := by
  let r := inner ℝ e x / inner ℝ e e
  let y := hyperplaneProjection e x
  have hline := ((T.cell v).mem_line_iff he y r).mp
    (by simpa only [r, y, hyperplaneProjection_decomposition] using hx.1)
  have hy : y ∈ (T.cell v).projectedBase e he :=
    T.project_facet_subset_projectedBase he v w ⟨x, hx, rfl⟩
  have hu : y + (T.cell v).upperFiber e he y • e ∈ (T.cell v).carrier :=
    ((T.cell v).mem_line_iff he y _).mpr ⟨hy.2.1, hy.2.2, le_rfl⟩
  have hsep := (T.facet_normal_separation hd hvw hx).1 _ hu
  have hdiff : y + (T.cell v).upperFiber e he y • e - x =
      ((T.cell v).upperFiber e he y - r) • e := by
    have hx' : y + r • e = x := hyperplaneProjection_decomposition e x
    rw [← hx', sub_smul]
    abel
  rw [hdiff, inner_smul_right] at hsep
  have hupper : (T.cell v).upperFiber e he y ≤ r := by
    by_contra h
    exact (not_lt_of_ge hsep) (mul_pos (sub_pos.mpr (lt_of_not_ge h)) hn)
  exact le_antisymm hupper hline.2.2

lemma lowerFiber_eq_lineParameter_of_mem_facet (hd : 1 ≤ d)
    {e : Euc d} (he : e ≠ 0) {v w : T.V} (hvw : T.adj v w)
    (hn : inner ℝ (T.pos w - T.pos v) e < 0)
    {x : Euc d} (hx : x ∈ T.facet v w) :
    (T.cell v).lowerFiber e he (hyperplaneProjection e x) =
      inner ℝ e x / inner ℝ e e := by
  let r := inner ℝ e x / inner ℝ e e
  let y := hyperplaneProjection e x
  have hline := ((T.cell v).mem_line_iff he y r).mp
    (by simpa only [r, y, hyperplaneProjection_decomposition] using hx.1)
  have hy : y ∈ (T.cell v).projectedBase e he :=
    T.project_facet_subset_projectedBase he v w ⟨x, hx, rfl⟩
  have hl : y + (T.cell v).lowerFiber e he y • e ∈ (T.cell v).carrier :=
    ((T.cell v).mem_line_iff he y _).mpr ⟨hy.2.1, le_rfl, hy.2.2⟩
  have hsep := (T.facet_normal_separation hd hvw hx).1 _ hl
  have hdiff : y + (T.cell v).lowerFiber e he y • e - x =
      ((T.cell v).lowerFiber e he y - r) • e := by
    have hx' : y + r • e = x := hyperplaneProjection_decomposition e x
    rw [← hx', sub_smul]
    abel
  rw [hdiff, inner_smul_right] at hsep
  have hlower : r ≤ (T.cell v).lowerFiber e he y := by
    by_contra h
    exact (not_lt_of_ge hsep)
      (mul_pos_of_neg_of_neg (sub_neg.mpr (lt_of_not_ge h)) hn)
  exact le_antisymm hline.2.1 hlower

theorem upperEndpoint_projection_of_mem_facet (hd : 1 ≤ d)
    {e : Euc d} (he : e ≠ 0) {v w : T.V} (hvw : T.adj v w)
    (hn : 0 < inner ℝ (T.pos w - T.pos v) e)
    {x : Euc d} (hx : x ∈ T.facet v w) :
    (T.cell v).upperEndpoint e he (hyperplaneProjection e x) = x := by
  rw [ConvexPolytope.upperEndpoint,
    T.upperFiber_eq_lineParameter_of_mem_facet hd he hvw hn hx,
    hyperplaneProjection_decomposition]

theorem lowerEndpoint_projection_of_mem_facet (hd : 1 ≤ d)
    {e : Euc d} (he : e ≠ 0) {v w : T.V} (hvw : T.adj v w)
    (hn : inner ℝ (T.pos w - T.pos v) e < 0)
    {x : Euc d} (hx : x ∈ T.facet v w) :
    (T.cell v).lowerEndpoint e he (hyperplaneProjection e x) = x := by
  rw [ConvexPolytope.lowerEndpoint,
    T.lowerFiber_eq_lineParameter_of_mem_facet hd he hvw hn hx,
    hyperplaneProjection_decomposition]

/-- The overlap of two outward contact projections is exactly the projection
of their actual overlap. Triple-contact nullity therefore survives projection. -/
theorem project_facet_inter_of_pos (hd : 1 ≤ d) {e : Euc d} (he : e ≠ 0)
    {v w u : T.V} (hvw : T.adj v w) (hvu : T.adj v u)
    (hw : 0 < inner ℝ (T.pos w - T.pos v) e)
    (hu : 0 < inner ℝ (T.pos u - T.pos v) e) :
    (hyperplaneProjection e '' T.facet v w) ∩
      (hyperplaneProjection e '' T.facet v u) =
        hyperplaneProjection e '' (T.facet v w ∩ T.facet v u) := by
  apply Set.Subset.antisymm
  · rintro y ⟨⟨x, hx, hxy⟩, ⟨z, hz, hzy⟩⟩
    have hxz : x = z := by
      rw [← T.upperEndpoint_projection_of_mem_facet hd he hvw hw hx,
        ← T.upperEndpoint_projection_of_mem_facet hd he hvu hu hz, hxy, hzy]
    exact ⟨x, ⟨hx, hxz.symm ▸ hz⟩, hxy⟩
  · exact Set.image_inter_subset _ _ _

theorem project_facet_inter_of_neg (hd : 1 ≤ d) {e : Euc d} (he : e ≠ 0)
    {v w u : T.V} (hvw : T.adj v w) (hvu : T.adj v u)
    (hw : inner ℝ (T.pos w - T.pos v) e < 0)
    (hu : inner ℝ (T.pos u - T.pos v) e < 0) :
    (hyperplaneProjection e '' T.facet v w) ∩
      (hyperplaneProjection e '' T.facet v u) =
        hyperplaneProjection e '' (T.facet v w ∩ T.facet v u) := by
  apply Set.Subset.antisymm
  · rintro y ⟨⟨x, hx, hxy⟩, ⟨z, hz, hzy⟩⟩
    have hxz : x = z := by
      rw [← T.lowerEndpoint_projection_of_mem_facet hd he hvw hw hx,
        ← T.lowerEndpoint_projection_of_mem_facet hd he hvu hu hz, hxy, hzy]
    exact ⟨x, ⟨hx, hxz.symm ▸ hz⟩, hxy⟩
  · exact Set.image_inter_subset _ _ _

end BouRabeeGwynne.OrthogonalTiling
