-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/FacetNull.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.FacetMeasure
import BouRabeeGwynne.FacetNormals

open scoped ENNReal MeasureTheory Pointwise
open MeasureTheory

namespace BouRabeeGwynne

/-- A compact convex set is null in every dimension above its affine rank. -/
lemma euclideanHausdorffMeasure_eq_zero_of_affineSpan_rank_lt {d k : ℕ}
    {s : Set (Euc d)} (hs : IsCompact s) (hconv : Convex ℝ s) (hne : s.Nonempty)
    (hrank : Module.finrank ℝ (affineSpan ℝ s).direction < k) :
    μHE[k] s = 0 := by
  have hfinite := (euclideanHausdorffMeasure_affineSpan_pos_lt_top hs hconv hne).2
  exact (Measure.euclideanHausdorffMeasure_zero_or_top hrank s).resolve_right hfinite.ne

namespace TilingData

variable {d : ℕ} (T : TilingData d)

/-- A contact between distinct full-dimensional cells has codimension at least one. -/
lemma facet_finrank_le (hd : 1 ≤ d) {v w : T.V} (hvw : v ≠ w) :
    Module.finrank ℝ (affineSpan ℝ (T.facet v w)).direction ≤ d - 1 := by
  obtain ⟨f, a, hPv, hPw, hpv, hpw⟩ := T.exists_cell_separator hvw
  have hf : f.toLinearMap ≠ 0 := by
    intro hzero
    have hv := congrArg (fun g : Euc d →ₗ[ℝ] ℝ => g (T.pos v)) hzero
    have hw := congrArg (fun g : Euc d →ₗ[ℝ] ℝ => g (T.pos w)) hzero
    change f (T.pos v) = 0 at hv
    change f (T.pos w) = 0 at hw
    linarith
  have hconst : ∀ z ∈ T.facet v w, f z = a := by
    intro z hz
    exact le_antisymm (hPv z hz.1) (hPw z hz.2)
  have hle : (affineSpan ℝ (T.facet v w)).direction ≤ LinearMap.ker f.toLinearMap := by
    rw [direction_affineSpan, vectorSpan_def]
    apply Submodule.span_le.mpr
    rintro z ⟨x, hx, y, hy, rfl⟩
    change f (x - y) = 0
    rw [map_sub, hconst x hx, hconst y hy, sub_self]
  have hdim := Submodule.finrank_mono hle
  have hker := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  have hamb : Module.finrank ℝ (Euc d) = d := finrank_euclideanSpace_fin
  omega

/-- Distinct contacts omitted from adjacency carry no codimension-one area. -/
lemma facetVolume_eq_zero_of_not_adj (hd : 1 ≤ d) {v w : T.V}
    (hvw : v ≠ w) (hnot : ¬ T.adj v w) : T.facetVolume v w = 0 := by
  by_cases hne : (T.facet v w).Nonempty
  · have hle := T.facet_finrank_le hd hvw
    have hdim : Module.finrank ℝ (affineSpan ℝ (T.facet v w)).direction ≠ d - 1 := by
      intro hdim
      exact hnot ⟨hvw, hne, hdim⟩
    have hlt : Module.finrank ℝ (affineSpan ℝ (T.facet v w)).direction < d - 1 := by
      omega
    exact euclideanHausdorffMeasure_eq_zero_of_affineSpan_rank_lt
      (T.facet_compact v w) (T.facet_convex v w) hne hlt
  · simp only [facetVolume, Set.not_nonempty_iff_eq_empty.mp hne, measure_empty]

end TilingData

end BouRabeeGwynne
