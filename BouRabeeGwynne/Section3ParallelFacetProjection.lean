module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/Section3ParallelFacetProjection.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.ProjectedBase
public import BouRabeeGwynne.FacetNull

@[expose] public section

/-!
# Section 3: columns parallel to a contact form a null set

A contact whose normal is perpendicular to the column direction projects into
two independent affine hyperplanes. Its projection therefore has affine rank
strictly less than `d - 1` and zero surface measure. No lower bound on `d` is
needed: the hypotheses themselves exclude the degenerate cases.
-/

open scoped MeasureTheory ENNReal
open MeasureTheory

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

theorem projected_parallel_facet_measure_zero (e : Euc d) (he : e ≠ 0)
    {v w : T.V} (hvw : T.adj v w)
    (hparallel : inner ℝ e (T.pos w - T.pos v) = 0) :
    μHE[d - 1] (hyperplaneProjection e '' T.facet v w) = 0 := by
  let n := T.pos w - T.pos v
  let S := hyperplaneProjection e '' T.facet v w
  have hn : n ≠ 0 := by
    intro hn
    exact hvw.1 (T.toTilingData.pos_injective (sub_eq_zero.mp hn).symm)
  have hne : inner ℝ n e = 0 := by
    rw [real_inner_comm]
    exact hparallel
  have hpreserve (x : Euc d) :
      inner ℝ n (hyperplaneProjection e x) = inner ℝ n x := by
    rw [hyperplaneProjection_apply, inner_sub_right, inner_smul_right,
      hne, mul_zero, sub_zero]
  have hle : (affineSpan ℝ S).direction ≤
      LinearMap.ker (innerSL ℝ e).toLinearMap := by
    rw [direction_affineSpan, vectorSpan_def]
    apply Submodule.span_le.mpr
    rintro z ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    change inner ℝ e (hyperplaneProjection e x - hyperplaneProjection e y) = 0
    rw [inner_sub_right, inner_hyperplaneProjection he,
      inner_hyperplaneProjection he, sub_self]
  have hln : (affineSpan ℝ S).direction ≤
      LinearMap.ker (innerSL ℝ n).toLinearMap := by
    rw [direction_affineSpan, vectorSpan_def]
    apply Submodule.span_le.mpr
    rintro z ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    change inner ℝ n (hyperplaneProjection e x - hyperplaneProjection e y) = 0
    rw [inner_sub_right, hpreserve, hpreserve, ← inner_sub_right]
    exact T.orthogonal hvw hx hy
  have hfunctional : (innerSL ℝ e).toLinearMap ≠ 0 := by
    intro hzero
    have h := congrArg (fun f : Euc d →ₗ[ℝ] ℝ => f e) hzero
    change inner ℝ e e = 0 at h
    exact (real_inner_self_pos.mpr he).ne' h
  have hker := Module.Dual.finrank_ker_add_one_of_ne_zero hfunctional
  have hamb : Module.finrank ℝ (Euc d) = d := finrank_euclideanSpace_fin
  have hrank : Module.finrank ℝ (affineSpan ℝ S).direction < d - 1 := by
    have hrankle := Submodule.finrank_mono hle
    by_contra hnot
    have heq : (affineSpan ℝ S).direction =
        LinearMap.ker (innerSL ℝ e).toLinearMap := by
      apply Submodule.eq_of_le_of_finrank_eq hle
      omega
    have hnmem : n ∈ (affineSpan ℝ S).direction := by
      rw [heq]
      exact hparallel
    have hnn : inner ℝ n n = 0 := hln hnmem
    exact (real_inner_self_pos.mpr hn).ne' hnn
  exact euclideanHausdorffMeasure_eq_zero_of_affineSpan_rank_lt
    ((T.toTilingData.facet_compact v w).image (hyperplaneProjection e).continuous)
    ((T.toTilingData.facet_convex v w).linear_image (hyperplaneProjection e).toLinearMap)
    (hvw.2.1.image _) hrank

end BouRabeeGwynne.OrthogonalTiling
