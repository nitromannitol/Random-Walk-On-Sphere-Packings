-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/FacetFlux.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.DiscretePDE
import BouRabeeGwynne.FluxResidual
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LocallyIntegrable

open scoped Topology ENNReal MeasureTheory
open MeasureTheory

namespace BouRabeeGwynne

/-- Integrating an actual pointwise residual on a set of finite measure. -/
theorem abs_const_mul_sub_setIntegral_le {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {s : Set X} {f : X → ℝ} {c C : ℝ}
    (hs : μ s < ∞) (hf : IntegrableOn f s μ)
    (hbound : ∀ x ∈ s, |c - f x| ≤ C) :
    |μ.real s * c - ∫ x in s, f x ∂μ| ≤ C * μ.real s := by
  have hc : IntegrableOn (fun _ : X => c) s μ := integrableOn_const hs.ne
  have hres : ‖∫ x in s, c - f x ∂μ‖ ≤ C * μ.real s :=
    norm_setIntegral_le_of_norm_le_const hs
      (fun x hx => by simpa only [Real.norm_eq_abs] using hbound x hx)
  rw [integral_sub hc hf, setIntegral_const, smul_eq_mul, Real.norm_eq_abs] at hres
  exact hres

namespace OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

/-- The oriented unit edge direction points from the marked point of `v` toward
the marked point of `w`. It is zero when the marked points coincide. -/
noncomputable def unitEdgeDirection (v w : T.V) : Euc d :=
  ‖T.pos w - T.pos v‖⁻¹ • (T.pos w - T.pos v)

theorem norm_unitEdgeDirection {v w : T.V} (hvw : T.adj v w) :
    ‖T.unitEdgeDirection v w‖ = 1 := by
  rw [unitEdgeDirection, norm_smul, norm_inv,
    Real.norm_of_nonneg (norm_nonneg _), inv_mul_cancel₀ (T.edge_norm_pos hvw).ne']

theorem unitEdgeDirection_rev (v w : T.V) :
    T.unitEdgeDirection w v = - T.unitEdgeDirection v w := by
  unfold unitEdgeDirection
  rw [norm_sub_rev, ← neg_sub (T.pos w) (T.pos v), smul_neg]

/-- The actual contact surface integral, oriented from `v` toward `w`. This
definition does not assert a divergence theorem or a harmonic-flux identity. -/
noncomputable def surfaceFlux (h : Euc d → ℝ) (v w : T.V) : ℝ :=
  ∫ y in T.facet v w, (fderiv ℝ h y) (T.unitEdgeDirection v w) ∂μHE[d - 1]

theorem surfaceFlux_rev (h : Euc d → ℝ) (v w : T.V) :
    T.surfaceFlux h w v = - T.surfaceFlux h v w := by
  have hfacet : T.facet w v = T.facet v w := T.toTilingData.facet_symm w v
  unfold surfaceFlux
  rw [hfacet, T.unitEdgeDirection_rev v w]
  simp only [map_neg, integral_neg]

/-- Finite contact measure and continuity on the compact contact give genuine
integrability. No local finiteness of ambient codimension-one measure is assumed. -/
theorem surfaceFlux_integrable_of_continuousOn (h : Euc d → ℝ) {v w : T.V}
    (hvw : T.adj v w) (hD : ContinuousOn (fderiv ℝ h) (T.facet v w)) :
    IntegrableOn (fun y => (fderiv ℝ h y) (T.unitEdgeDirection v w))
      (T.facet v w) μHE[d - 1] := by
  have hcont : ContinuousOn (fun y => (fderiv ℝ h y) (T.unitEdgeDirection v w))
      (T.facet v w) := hD.clm_apply continuousOn_const
  have hK := T.toTilingData.facet_compact v w
  exact hcont.integrableOn_of_subset_isCompact hK hK.measurableSet
    Set.Subset.rfl (T.toTilingData.facetVolume_ne_top hvw)

theorem surfaceFlux_integrable (h : Euc d → ℝ) {v w : T.V} (hvw : T.adj v w)
    {W : Set (Euc d)} (hW : IsOpen W) (hh : ContDiffOn ℝ 2 h W)
    (hfacet : T.facet v w ⊆ W) :
    IntegrableOn (fun y => (fderiv ℝ h y) (T.unitEdgeDirection v w))
      (T.facet v w) μHE[d - 1] :=
  T.surfaceFlux_integrable_of_continuousOn h hvw
    ((hh.continuousOn_fderiv_of_isOpen hW (by norm_num)).mono hfacet)

/-- The single-contact integral residual. The conductance increment and surface
integral both have orientation from `v` toward `w`. -/
theorem surfaceFlux_residual_bound_on_closedBall (h : Euc d → ℝ) {v w : T.V}
    (hvw : T.adj v w) (hmesh : T.mesh ≠ ∞)
    {W : Set (Euc d)} (hW : IsOpen W) (hh : ContDiffOn ℝ 2 h W)
    (hball : Metric.closedBall (T.pos v) (2 * T.mesh.toReal) ⊆ W)
    {M : ℝ} (hM : 0 ≤ M)
    (hH : ∀ x ∈ Metric.closedBall (T.pos v) (2 * T.mesh.toReal),
      ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M) :
    |T.conductanceReal v w * (h (T.pos w) - h (T.pos v)) - T.surfaceFlux h v w| ≤
      3 * M * T.mesh.toReal * (T.facetVolume v w).toReal := by
  have hε : 0 ≤ T.mesh.toReal := ENNReal.toReal_nonneg
  have hfacetB : T.facet v w ⊆ Metric.closedBall (T.pos v) (2 * T.mesh.toReal) := by
    intro y hy
    apply Metric.mem_closedBall.mpr
    exact (T.toTilingData.dist_pos_le_mesh hy.1 hmesh).trans (by linarith)
  have hCF : ContDiffOn ℝ 1 (fderiv ℝ h) W :=
    hh.fderiv_of_isOpen hW (by norm_num)
  have hlength : 0 < ‖T.pos w - T.pos v‖ := T.edge_norm_pos hvw
  have hpoint : ∀ y ∈ T.facet v w,
      |(h (T.pos w) - h (T.pos v)) / ‖T.pos w - T.pos v‖ -
        (fderiv ℝ h y) (T.unitEdgeDirection v w)| ≤ 3 * M * T.mesh.toReal := by
    intro y hy
    have hraw := fluxResidual_bound_on_closedBall h hε hM
      (T.toTilingData.edge_dist_le_two_mesh hvw hmesh)
      (by simpa only [dist_comm] using T.toTilingData.dist_pos_le_mesh hy.1 hmesh)
      (fun x hx => (hh.differentiableOn (by norm_num)).differentiableAt
        (hW.mem_nhds (hball hx)))
      (fun x hx => (hCF.differentiableOn (by norm_num)).differentiableAt
        (hW.mem_nhds (hball hx))) hH
    have hid : (h (T.pos w) - h (T.pos v)) / ‖T.pos w - T.pos v‖ -
        (fderiv ℝ h y) (T.unitEdgeDirection v w) =
        (h (T.pos w) - h (T.pos v) - (fderiv ℝ h y) (T.pos w - T.pos v)) /
          ‖T.pos w - T.pos v‖ := by
      simp only [unitEdgeDirection, map_smul, smul_eq_mul, div_eq_mul_inv]
      ring
    rw [hid, abs_div, abs_of_pos hlength]
    exact (div_le_iff₀ hlength).mpr hraw
  have hres := abs_const_mul_sub_setIntegral_le
    (μ := μHE[d - 1]) (s := T.facet v w)
    (c := (h (T.pos w) - h (T.pos v)) / ‖T.pos w - T.pos v‖)
    (C := 3 * M * T.mesh.toReal)
    (T.toTilingData.facetVolume_pos_lt_top hvw).2
    (T.surfaceFlux_integrable h hvw hW hh (hfacetB.trans hball)) hpoint
  change |(T.facetVolume v w).toReal *
      ((h (T.pos w) - h (T.pos v)) / ‖T.pos w - T.pos v‖) - T.surfaceFlux h v w| ≤
    3 * M * T.mesh.toReal * (T.facetVolume v w).toReal at hres
  have hconstant : (T.facetVolume v w).toReal *
      ((h (T.pos w) - h (T.pos v)) / ‖T.pos w - T.pos v‖) =
      T.conductanceReal v w * (h (T.pos w) - h (T.pos v)) := by
    rw [T.conductanceReal_of_adj hvw]
    simp only [div_eq_mul_inv]
    ring
  rw [hconstant] at hres
  exact hres

end OrthogonalTiling

/-- The single-contact estimate for B(a), with a radius and Hessian constant
chosen from the fixed continuum neighborhood before the tiling is chosen.
The surface integrand is integrable on every contact covered by the estimate. -/
theorem exists_uniform_surfaceFlux_residual_bound {d : ℕ} (h : Euc d → ℝ)
    {U W : Set (Euc d)} (hU : Bornology.IsBounded U) (hW : IsOpen W)
    (hUW : closure U ⊆ W) (hh : ContDiffOn ℝ 2 h W) :
    ∃ r : ℝ, 0 < r ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ (T : OrthogonalTiling d) (v w : T.V), T.adj v w → T.mesh ≠ ∞ →
      T.pos v ∈ U → 2 * T.mesh.toReal ≤ r →
      IntegrableOn (fun y => (fderiv ℝ h y) (T.unitEdgeDirection v w))
        (T.facet v w) μHE[d - 1] ∧
      |T.conductanceReal v w * (h (T.pos w) - h (T.pos v)) - T.surfaceFlux h v w| ≤
        3 * M * T.mesh.toReal * (T.facetVolume v w).toReal := by
  obtain ⟨r, hr, M, hM, hKW, _, _, hH⟩ :=
    exists_collar_derivative_bounds h hU hW hUW hh
  refine ⟨r, hr, M, hM, ?_⟩
  intro T v w hvw hmesh hv hsmall
  have hε : 0 ≤ T.mesh.toReal := ENNReal.toReal_nonneg
  have hεr : T.mesh.toReal ≤ r := by linarith
  have hfacetK : T.facet v w ⊆ Metric.cthickening r (closure U) :=
    fun _ hy => T.toTilingData.cell_subset_cthickening hv hmesh hεr hy.1
  have hBK : Metric.closedBall (T.pos v) (2 * T.mesh.toReal) ⊆
      Metric.cthickening r (closure U) :=
    (Metric.closedBall_subset_cthickening (subset_closure hv) (2 * T.mesh.toReal)).trans
      (Metric.cthickening_mono hsmall (closure U))
  refine ⟨T.surfaceFlux_integrable h hvw hW hh (hfacetK.trans hKW), ?_⟩
  exact T.surfaceFlux_residual_bound_on_closedBall h hvw hmesh hW hh
    (hBK.trans hKW) hM (fun x hx => hH x (hBK hx))

end BouRabeeGwynne
