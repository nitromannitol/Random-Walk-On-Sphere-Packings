module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/SupportedSurfaceField.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.FacetFlux
public import BouRabeeGwynne.TilingNetwork

@[expose] public section

open scoped BigOperators Classical

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

/-- The actual outward contact flux, extended by zero off the tiling edges.
The field indices `(w,v)` match the paper's divergence convention at `v`. -/
noncomputable def supportedSurfaceField (h : Euc d → ℝ) (w v : T.V) : ℝ :=
  if T.adj v w then T.surfaceFlux h v w else 0

lemma supportedSurfaceField_of_adj (h : Euc d → ℝ) {v w : T.V} (hvw : T.adj v w) :
    T.supportedSurfaceField h w v = T.surfaceFlux h v w := by
  simp only [supportedSurfaceField, if_pos hvw]

lemma supportedSurfaceField_antisymm (h : Euc d → ℝ) (w v : T.V) :
    T.supportedSurfaceField h w v = - T.supportedSurfaceField h v w := by
  by_cases hvw : T.adj v w
  · rw [T.supportedSurfaceField_of_adj h hvw,
      T.supportedSurfaceField_of_adj h (T.adj_symm hvw)]
    exact T.surfaceFlux_rev h w v
  · have hwv : ¬ T.adj w v := fun hwv => hvw (T.adj_symm hwv)
    simp only [supportedSurfaceField, if_neg hvw, if_neg hwv, neg_zero]

lemma supportedSurfaceField_zero_of_conductance_zero (h : Euc d → ℝ)
    {w v : T.V} (ha : T.conductanceReal w v = 0) :
    T.supportedSurfaceField h w v = 0 := by
  have hvw : ¬ T.adj v w := fun hvw =>
    (T.conductanceReal_pos (T.adj_symm hvw)).ne' ha
  simp only [supportedSurfaceField, if_neg hvw]

/-- Restricting to a finite region containing all neighbors does not change
the outward flux sum at an interior vertex. -/
theorem finite_div_supportedSurfaceField (R : Set T.V) [Fintype R]
    (h : Euc d → ℝ) (v : R) (hv : (T.neighbors v).Finite)
    (hneighbors : T.neighbors v ⊆ R) :
    discreteDiv (fun w u : R => T.supportedSurfaceField h w u) v =
      ∑ w ∈ T.neighborFinset v hv, T.surfaceFlux h v w := by
  change (∑ w : R, T.supportedSurfaceField h w v) = _
  calc
    (∑ w : R, T.supportedSurfaceField h w v) =
        ∑ w ∈ T.neighborFinset v hv, T.supportedSurfaceField h w v := by
      rw [Finset.sum_set_coe R (f := fun w : T.V => T.supportedSurfaceField h w v)]
      symm
      apply Finset.sum_subset
      · intro w hw
        exact Set.mem_toFinset.mpr (hneighbors ((T.mem_neighborFinset hv).mp hw))
      · intro w _ hw
        have hnot : ¬ T.adj v w := fun h => hw ((T.mem_neighborFinset hv).mpr h)
        simp only [supportedSurfaceField, if_neg hnot]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w hw
      exact T.supportedSurfaceField_of_adj h ((T.mem_neighborFinset hv).mp hw)

/-- Squaring a contact-flux residual and dividing by the actual conductance
produces exactly the facet-area times edge-length weight. -/
theorem residual_dual_energy_bound {v w : T.V} (hvw : T.adj v w)
    {C r : ℝ} (hC : 0 ≤ C)
    (hr : |r| ≤ C * (T.facetVolume v w).toReal) :
    r ^ 2 / T.conductanceReal v w ≤
      C ^ 2 * (T.facetVolume v w).toReal * ‖T.pos w - T.pos v‖ := by
  have harea := T.facetVolume_toReal_pos hvw
  have hlength := T.edge_norm_pos hvw
  have hsq : r ^ 2 ≤ (C * (T.facetVolume v w).toReal) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg r) (mul_nonneg hC harea.le)).mpr hr
  rw [T.conductanceReal_of_adj hvw]
  calc
    _ ≤ (C * (T.facetVolume v w).toReal) ^ 2 /
        ((T.facetVolume v w).toReal / ‖T.pos w - T.pos v‖) :=
      div_le_div_of_nonneg_right hsq (div_nonneg harea.le hlength.le)
    _ = _ := by
      field_simp [harea.ne', hlength.ne'] <;> ring

end BouRabeeGwynne.OrthogonalTiling
