module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/FacetNormals.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.PolytopeBoundary
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

open scoped Pointwise

namespace BouRabeeGwynne

namespace TilingData

variable {d : ℕ} (T : TilingData d)

/-- Closed cells can be separated, strictly at their marked interior points. -/
lemma exists_cell_separator {v w : T.V} (hvw : v ≠ w) :
    ∃ (f : Euc d →L[ℝ] ℝ) (a : ℝ),
      (∀ y ∈ (T.cell v).carrier, f y ≤ a) ∧
      (∀ y ∈ (T.cell w).carrier, a ≤ f y) ∧
      f (T.pos v) < a ∧ a < f (T.pos w) := by
  obtain ⟨f, a, hPv, hPw⟩ := geometric_hahn_banach_open_open
    (T.cell v).convex.interior isOpen_interior
    (T.cell w).convex.interior isOpen_interior (T.interiors_pairwise_disjoint hvw)
  have hP : (T.cell v).carrier ⊆ {y | f y ≤ a} := by
    have h : closure (interior (T.cell v).carrier) ⊆ {y | f y ≤ a} :=
      closure_minimal (fun y hy => (hPv y hy).le)
        (isClosed_le f.continuous continuous_const)
    simpa only [(T.cell v).closure_interior] using h
  have hQ : (T.cell w).carrier ⊆ {y | a ≤ f y} := by
    have h : closure (interior (T.cell w).carrier) ⊆ {y | a ≤ f y} :=
      closure_minimal (fun y hy => (hPw y hy).le)
        (isClosed_le continuous_const f.continuous)
    simpa only [(T.cell w).closure_interior] using h
  exact ⟨f, a, hP, hQ, hPv _ (T.pos_mem_interior v), hPw _ (T.pos_mem_interior w)⟩

/-- A nonzero functional constant on a codimension-one contact has that contact's kernel. -/
lemma facet_direction_eq_ker {v w : T.V} (_hd : 1 ≤ d) (hvw : T.adj v w)
    (f : Euc d →L[ℝ] ℝ) (hf : f.toLinearMap ≠ 0) (a : ℝ)
    (hconst : ∀ x ∈ T.facet v w, f x = a) :
    (affineSpan ℝ (T.facet v w)).direction = LinearMap.ker f.toLinearMap := by
  have hle : (affineSpan ℝ (T.facet v w)).direction ≤ LinearMap.ker f.toLinearMap := by
    rw [direction_affineSpan, vectorSpan_def]
    apply Submodule.span_le.mpr
    rintro z ⟨x, hx, y, hy, rfl⟩
    change f (x - y) = 0
    rw [map_sub, hconst x hx, hconst y hy, sub_self]
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hdim : Module.finrank ℝ (affineSpan ℝ (T.facet v w)).direction = d - 1 := hvw.2.2
  have hker := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  have hamb : Module.finrank ℝ (Euc d) = d := finrank_euclideanSpace_fin
  omega

end TilingData

namespace OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

/-- The marked edge is orthogonal to the whole direction space of its contact. -/
lemma inner_edge_eq_zero_of_mem_facet_direction {v w : T.V} (hvw : T.adj v w)
    {z : Euc d} (hz : z ∈ (affineSpan ℝ (T.facet v w)).direction) :
    inner ℝ (T.pos w - T.pos v) z = 0 := by
  have hle : (affineSpan ℝ (T.facet v w)).direction ≤
      LinearMap.ker (innerSL ℝ (T.pos w - T.pos v)).toLinearMap := by
    rw [direction_affineSpan, vectorSpan_def]
    apply Submodule.span_le.mpr
    rintro z ⟨x, hx, y, hy, rfl⟩
    change inner ℝ (T.pos w - T.pos v) (x - y) = 0
    exact T.orthogonal hvw hx hy
  exact hle hz

/-- The edge vector points outward from its first cell and inward to the second. -/
theorem facet_normal_separation (hd : 1 ≤ d) {v w : T.V} (hvw : T.adj v w)
    {x : Euc d} (hx : x ∈ T.facet v w) :
    (∀ y ∈ (T.cell v).carrier, inner ℝ (T.pos w - T.pos v) (y - x) ≤ 0) ∧
    (∀ y ∈ (T.cell w).carrier, 0 ≤ inner ℝ (T.pos w - T.pos v) (y - x)) ∧
    inner ℝ (T.pos w - T.pos v) (T.pos v - x) < 0 ∧
    0 < inner ℝ (T.pos w - T.pos v) (T.pos w - x) := by
  obtain ⟨f, a, hPv, hPw, hpv, hpw⟩ := T.toTilingData.exists_cell_separator hvw.1
  let n := T.pos w - T.pos v
  have hfn : 0 < f n := by
    dsimp [n]
    rw [map_sub]
    linarith
  have hf : f.toLinearMap ≠ 0 := by
    intro hzero
    have h := congrArg (fun g : Euc d →ₗ[ℝ] ℝ => g n) hzero
    change f n = 0 at h
    exact hfn.ne' h
  have hconst : ∀ z ∈ T.facet v w, f z = a := by
    intro z hz
    exact le_antisymm (hPv z hz.1) (hPw z hz.2)
  have hker := T.toTilingData.facet_direction_eq_ker hd hvw f hf a hconst
  have hn : n ≠ 0 := by
    intro hn
    simp only [hn, map_zero, lt_self_iff_false] at hfn
  have hnn : 0 < inner ℝ n n := real_inner_self_pos.mpr hn
  have hidentity (y : Euc d) :
      f n * inner ℝ n (y - x) = f (y - x) * inner ℝ n n := by
    have hz : (f n) • (y - x) - (f (y - x)) • n ∈ LinearMap.ker f.toLinearMap := by
      change f ((f n) • (y - x) - (f (y - x)) • n) = 0
      simp only [map_sub, map_smul, smul_eq_mul]
      ring
    rw [← hker] at hz
    have h := T.inner_edge_eq_zero_of_mem_facet_direction hvw hz
    change inner ℝ n ((f n) • (y - x) - (f (y - x)) • n) = 0 at h
    simp only [inner_sub_right, inner_smul_right] at h
    simpa only [inner_sub_right] using sub_eq_zero.mp h
  have hfx : f x = a := hconst x hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy
    have hfy : f (y - x) ≤ 0 := by
      rw [map_sub, hfx]
      exact sub_nonpos.mpr (hPv y hy)
    have hmul : f n * inner ℝ n (y - x) ≤ 0 := by
      rw [hidentity]
      exact mul_nonpos_of_nonpos_of_nonneg hfy hnn.le
    exact nonpos_of_mul_nonpos_right hmul hfn
  · intro y hy
    have hfy : 0 ≤ f (y - x) := by
      rw [map_sub, hfx]
      exact sub_nonneg.mpr (hPw y hy)
    have hmul : 0 ≤ f n * inner ℝ n (y - x) := by
      rw [hidentity]
      exact mul_nonneg hfy hnn.le
    exact (mul_nonneg_iff_of_pos_left hfn).mp hmul
  · have hfy : f (T.pos v - x) < 0 := by
      rw [map_sub, hfx]
      exact sub_neg.mpr hpv
    have hmul : f n * inner ℝ n (T.pos v - x) < 0 := by
      rw [hidentity]
      exact mul_neg_of_neg_of_pos hfy hnn
    exact neg_of_mul_neg_right hmul hfn.le
  · have hfy : 0 < f (T.pos w - x) := by
      rw [map_sub, hfx]
      exact sub_pos.mpr hpw
    have hmul : 0 < f n * inner ℝ n (T.pos w - x) := by
      rw [hidentity]
      exact mul_pos hfy hnn
    exact (mul_pos_iff_of_pos_left hfn).mp hmul

end OrthogonalTiling

end BouRabeeGwynne
