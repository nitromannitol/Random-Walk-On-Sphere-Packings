module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/TripleContact.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.FacetNull

@[expose] public section

open scoped ENNReal MeasureTheory Pointwise
open MeasureTheory

namespace BouRabeeGwynne

private lemma separator_ne_zero {d : ℕ} (f : Euc d →L[ℝ] ℝ)
    {x y : Euc d} (h : f x < f y) : f.toLinearMap ≠ 0 := by
  intro hf
  have hx := congrArg (fun g : Euc d →ₗ[ℝ] ℝ => g x) hf
  have hy := congrArg (fun g : Euc d →ₗ[ℝ] ℝ => g y) hf
  change f x = 0 at hx
  change f y = 0 at hy
  linarith

private lemma direction_eq_kernel_of_rank {d : ℕ} {s : Set (Euc d)}
    (hdim : Module.finrank ℝ (affineSpan ℝ s).direction = d - 1)
    (f : Euc d →L[ℝ] ℝ) (hf : f.toLinearMap ≠ 0) (a : ℝ)
    (hconst : ∀ x ∈ s, f x = a) :
    (affineSpan ℝ s).direction = LinearMap.ker f.toLinearMap := by
  have hle : (affineSpan ℝ s).direction ≤ LinearMap.ker f.toLinearMap := by
    rw [direction_affineSpan, vectorSpan_def]
    apply Submodule.span_le.mpr
    rintro z ⟨x, hx, y, hy, rfl⟩
    change f (x - y) = 0
    rw [map_sub, hconst x hx, hconst y hy, sub_self]
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hker := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  have hamb : Module.finrank ℝ (Euc d) = d := finrank_euclideanSpace_fin
  omega

private lemma functional_cross_identity {d : ℕ} (f g : Euc d →L[ℝ] ℝ)
    (hker : LinearMap.ker f.toLinearMap ≤ LinearMap.ker g.toLinearMap)
    (y z : Euc d) : f y * g z = g y * f z := by
  have hz : (f y) • z - (f z) • y ∈ LinearMap.ker f.toLinearMap := by
    change f ((f y) • z - (f z) • y) = 0
    simp only [map_sub, map_smul, smul_eq_mul]
    ring
  have hg := hker hz
  change g ((f y) • z - (f z) • y) = 0 at hg
  simp only [map_sub, map_smul, smul_eq_mul] at hg
  nlinarith

namespace TilingData

variable {d : ℕ} (T : TilingData d)

/-- Three cells with pairwise disjoint interiors cannot share a contact of
codimension one. Three strict separators would otherwise have the same kernel,
forcing three marked points to lie on pairwise opposite sides of one hyperplane. -/
theorem triple_contact_rank_lt (hd : 1 ≤ d) {v w u : T.V}
    (hvw : v ≠ w) (hvu : v ≠ u) (hwu : w ≠ u)
    (hne : (T.facet v w ∩ (T.cell u).carrier).Nonempty) :
    Module.finrank ℝ (affineSpan ℝ (T.facet v w ∩ (T.cell u).carrier)).direction < d - 1 := by
  let S := T.facet v w ∩ (T.cell u).carrier
  have hle : Module.finrank ℝ (affineSpan ℝ S).direction ≤ d - 1 := by
    have hsub : affineSpan ℝ S ≤ affineSpan ℝ (T.facet v w) :=
      affineSpan_mono ℝ Set.inter_subset_left
    exact (Submodule.finrank_mono (AffineSubspace.direction_le hsub)).trans
      (T.facet_finrank_le hd hvw)
  have hneq : Module.finrank ℝ (affineSpan ℝ S).direction ≠ d - 1 := by
    intro hdim
    obtain ⟨x, hx⟩ := hne
    obtain ⟨f, a, hfV, hfW, hfv, hfw⟩ := T.exists_cell_separator hvw
    obtain ⟨g, b, hgW, hgU, hgw, hgu⟩ := T.exists_cell_separator hwu
    obtain ⟨h, c, hhV, hhU, hhv, hhu⟩ := T.exists_cell_separator hvu
    have hfconst : ∀ z ∈ S, f z = a := fun z hz =>
      le_antisymm (hfV z hz.1.1) (hfW z hz.1.2)
    have hgconst : ∀ z ∈ S, g z = b := fun z hz =>
      le_antisymm (hgW z hz.1.2) (hgU z hz.2)
    have hhconst : ∀ z ∈ S, h z = c := fun z hz =>
      le_antisymm (hhV z hz.1.1) (hhU z hz.2)
    have hfker := direction_eq_kernel_of_rank hdim f
      (separator_ne_zero f (hfv.trans hfw)) a hfconst
    have hgker := direction_eq_kernel_of_rank hdim g
      (separator_ne_zero g (hgw.trans hgu)) b hgconst
    have hhker := direction_eq_kernel_of_rank hdim h
      (separator_ne_zero h (hhv.trans hhu)) c hhconst
    have hfg : LinearMap.ker f.toLinearMap ≤ LinearMap.ker g.toLinearMap := by
      rw [← hfker, ← hgker]
    have hfh : LinearMap.ker f.toLinearMap ≤ LinearMap.ker h.toLinearMap := by
      rw [← hfker, ← hhker]
    have hfx : f x = a := hfconst x hx
    have hgx : g x = b := hgconst x hx
    have hhx : h x = c := hhconst x hx
    have hf_v : f (T.pos v - x) < 0 := by
      rw [map_sub, hfx]
      exact sub_neg.mpr hfv
    have hf_w : 0 < f (T.pos w - x) := by
      rw [map_sub, hfx]
      exact sub_pos.mpr hfw
    have hg_w : g (T.pos w - x) < 0 := by
      rw [map_sub, hgx]
      exact sub_neg.mpr hgw
    have hg_u : 0 < g (T.pos u - x) := by
      rw [map_sub, hgx]
      exact sub_pos.mpr hgu
    have hh_v : h (T.pos v - x) < 0 := by
      rw [map_sub, hhx]
      exact sub_neg.mpr hhv
    have hh_u : 0 < h (T.pos u - x) := by
      rw [map_sub, hhx]
      exact sub_pos.mpr hhu
    have hfgid := functional_cross_identity f g hfg (T.pos w - x) (T.pos u - x)
    have hf_u : f (T.pos u - x) < 0 := by
      by_contra hnot
      have hn := mul_nonpos_of_nonpos_of_nonneg hg_w.le (le_of_not_gt hnot)
      rw [← hfgid] at hn
      exact (not_lt_of_ge hn) (mul_pos hf_w hg_u)
    have hfhid := functional_cross_identity f h hfh (T.pos v - x) (T.pos u - x)
    have hneg := mul_neg_of_neg_of_pos hf_v hh_u
    rw [hfhid] at hneg
    exact (not_lt_of_ge (mul_pos_of_neg_of_neg hh_v hf_u).le) hneg
  exact lt_of_le_of_ne hle hneq

/-- Overlaps between distinct cell contacts have zero codimension-one measure.
Consequently partial facets can be summed without counting shared boundaries twice. -/
theorem facet_inter_facet_measure_zero (hd : 1 ≤ d) {v w u : T.V}
    (hvw : v ≠ w) (hvu : v ≠ u) (hwu : w ≠ u) :
    μHE[d - 1] (T.facet v w ∩ T.facet v u) = 0 := by
  have hset : T.facet v w ∩ T.facet v u = T.facet v w ∩ (T.cell u).carrier := by
    ext x
    simp only [facet, Set.mem_inter_iff]
    tauto
  rw [hset]
  by_cases hne : (T.facet v w ∩ (T.cell u).carrier).Nonempty
  · apply euclideanHausdorffMeasure_eq_zero_of_affineSpan_rank_lt
      ((T.facet_compact v w).inter_right (T.cell u).compact.isClosed)
      ((T.facet_convex v w).inter (T.cell u).convex) hne
    exact T.triple_contact_rank_lt hd hvw hvu hwu hne
  · simp only [Set.not_nonempty_iff_eq_empty.mp hne, measure_empty]

end TilingData
end BouRabeeGwynne
