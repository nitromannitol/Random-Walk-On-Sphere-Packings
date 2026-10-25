module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/Section3WeightedEnergy.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.TilingNetwork

@[expose] public section

/-!
# Section 3: weighted gradient-energy estimate

This proves Lemma 3.5 in its facet-area times edge-length form, directly from
the actual tiling conductances. The equality of this geometric weight with
`d * volume Q_e` is the independent dual-polytope identity of Lemma 2.4.
There is no assumed energy bound in these statements.
-/

open scoped BigOperators Classical

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

/-- On an edge, the conductance times squared length is exactly facet area
times length, with all quantities taken from the actual tiling. -/
lemma conductanceReal_mul_edge_norm_sq {v w : T.V} (hvw : T.adj v w) :
    T.conductanceReal v w * ‖T.pos w - T.pos v‖ ^ 2 =
      (T.facetVolume v w).toReal * ‖T.pos w - T.pos v‖ := by
  rw [T.conductanceReal_of_adj hvw]
  field_simp [ne_of_gt (T.edge_norm_pos hvw)]

/-- The one-edge inequality underlying the weighted gradient-energy estimate. -/
lemma facet_weight_le_gradient_energy {v w : T.V} (hvw : T.adj v w)
    (f : T.V → ℝ) {δ : ℝ} (hlength : ‖T.pos w - T.pos v‖ ≤ δ)
    (hgradient : δ < |f w - f v|) :
    (T.facetVolume v w).toReal * ‖T.pos w - T.pos v‖ ≤
      T.conductanceReal v w * (f w - f v) ^ 2 := by
  have hsq : ‖T.pos w - T.pos v‖ ^ 2 ≤ (f w - f v) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (norm_nonneg _) (abs_nonneg (f w - f v))).mpr
        (hlength.trans hgradient.le)
  rw [← T.conductanceReal_mul_edge_norm_sq hvw]
  exact mul_le_mul_of_nonneg_left hsq (T.conductanceReal_nonneg v w)

/-- Lemma 3.5 in facet form, on any finite collection of actual edges. Using
the same orientations on both sides preserves the paper's normalization. -/
theorem weighted_gradient_energy_estimate_on_edges (E : Finset (T.V × T.V))
    (hE : ∀ e ∈ E, T.adj e.1 e.2) (f : T.V → ℝ) (δ : ℝ)
    (hlength : ∀ e ∈ E, ‖T.pos e.2 - T.pos e.1‖ ≤ δ) :
    (∑ e ∈ E, if δ < |f e.2 - f e.1| then
      (T.facetVolume e.1 e.2).toReal * ‖T.pos e.2 - T.pos e.1‖ else 0) ≤
      ∑ e ∈ E, T.conductanceReal e.1 e.2 * (f e.2 - f e.1) ^ 2 := by
  apply Finset.sum_le_sum
  intro e he
  split_ifs with hlarge
  · exact T.facet_weight_le_gradient_energy (hE e he) f (hlength e he) hlarge
  · exact mul_nonneg (T.conductanceReal_nonneg _ _) (sq_nonneg _)

/-- The same estimate in the canonical finite-network normalization, where
`1/2` removes the double counting of edge orientations. -/
theorem weighted_gradient_energy_estimate_finiteNetwork
    (R : Set T.V) [Fintype R] (f : T.V → ℝ) (δ : ℝ)
    (hlength : ∀ v w : R, T.adj v.val w.val → ‖T.pos w.val - T.pos v.val‖ ≤ δ) :
    (1 / 2 : ℝ) * (∑ v : R, ∑ w : R,
      if T.adj v.val w.val ∧ δ < |f w.val - f v.val| then
        (T.facetVolume v.val w.val).toReal * ‖T.pos w.val - T.pos v.val‖ else 0) ≤
      (T.finiteNetwork R).energy (fun v => f v.val) := by
  unfold FiniteConductanceNetwork.energy
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro v _
  apply Finset.sum_le_sum
  intro w _
  split_ifs with hlarge
  · exact T.facet_weight_le_gradient_energy hlarge.1 f
      (hlength v w hlarge.1) hlarge.2
  · exact mul_nonneg (T.conductanceReal_nonneg _ _) (sq_nonneg _)

end BouRabeeGwynne.OrthogonalTiling
