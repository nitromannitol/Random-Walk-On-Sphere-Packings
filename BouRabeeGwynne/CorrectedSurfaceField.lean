module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/CorrectedSurfaceField.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.BoundaryTaylorCorrection
public import BouRabeeGwynne.LocalFacetResidual
public import BouRabeeGwynne.SupportedSurfaceField

@[expose] public section

/-! The actual corrected surface field has the shrinking interior diameter scale. -/

open scoped Classical BigOperators

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

noncomputable def surfaceTaylorRemainder (h : Euc d → ℝ) (v w : T.V) : ℝ :=
  h (T.pos w) - h (T.pos v) - (fderiv ℝ h (T.pos v)) (T.pos w - T.pos v)

noncomputable def surfaceResidualField (h : Euc d → ℝ) (w v : T.V) : ℝ :=
  T.supportedSurfaceField h w v - T.conductanceReal w v * (h (T.pos w) - h (T.pos v))

theorem surfaceResidualField_antisymm (h : Euc d → ℝ) :
    IsDiscreteVectorField (T.surfaceResidualField h) := by
  intro w v
  dsimp only [surfaceResidualField]
  rw [T.supportedSurfaceField_antisymm h w v, T.conductanceReal_symm w v]
  ring

theorem surfaceResidualField_support (h : Euc d → ℝ) {w v : T.V}
    (ha : T.conductanceReal w v = 0) : T.surfaceResidualField h w v = 0 := by
  simp only [surfaceResidualField, ha,
    T.supportedSurfaceField_zero_of_conductance_zero h ha, zero_mul, sub_zero]

noncomputable def correctedSurfaceField (R : Set T.V) [Fintype R] (A : Set R)
    (h : Euc d → ℝ) : R → R → ℝ :=
  (T.finiteNetwork R).correctedIncidentFlux A
    (fun w v => T.surfaceResidualField h w v) (fun v w => T.surfaceTaylorRemainder h v w)

theorem correctedSurfaceField_antisymm (R : Set T.V) [Fintype R] (A : Set R)
    (h : Euc d → ℝ) : IsDiscreteVectorField (T.correctedSurfaceField R A h) :=
  (T.finiteNetwork R).correctedIncidentFlux_antisymm A _ _
    (fun w v => T.surfaceResidualField_antisymm h w v)

theorem correctedSurfaceField_support (R : Set T.V) [Fintype R] (A : Set R)
    (h : Euc d → ℝ) (w v : R) (ha : (T.finiteNetwork R).a w v = 0) :
    T.correctedSurfaceField R A h w v = 0 :=
  (T.finiteNetwork R).correctedIncidentFlux_support A _ _
    (fun _ _ hzero => T.surfaceResidualField_support h hzero) w v ha

theorem correctedSurfaceField_bound_at_interior (R : Set T.V) [Fintype R]
    (A : Set R) (h : Euc d → ℝ) {δ M : ℝ} (hδ : 0 ≤ δ) (hM : 0 ≤ M)
    (hdiam : ∀ v ∈ A, Metric.diam (T.cell v.val).carrier ≤ δ)
    {W : Set (Euc d)} (hW : IsOpen W) (hh : ContDiffOn ℝ 2 h W)
    (hball : ∀ v ∈ A, Metric.closedBall (T.pos v) (2 * δ) ⊆ W)
    (hH : ∀ v ∈ A, ∀ x ∈ Metric.closedBall (T.pos v) (2 * δ),
      ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M)
    {v w : R} (hv : v ∈ A) (ha : T.adj v w) :
    |T.correctedSurfaceField R A h w v| ≤ 3 * M * δ * (T.facetVolume v w).toReal := by
  have hθ : T.surfaceResidualField h w v = T.surfaceFlux h v w -
      T.conductanceReal v w * (h (T.pos w) - h (T.pos v)) := by
    rw [surfaceResidualField, T.supportedSurfaceField_of_adj h ha,
      T.conductanceReal_symm w v]
  by_cases hw : w ∈ A
  · have heq : T.correctedSurfaceField R A h w v = T.surfaceResidualField h w v := by
      simp only [correctedSurfaceField, FiniteConductanceNetwork.correctedIncidentFlux,
        FiniteConductanceNetwork.boundaryRewardField, hv, hw, or_true, ite_true, add_zero]
    rw [heq, hθ]
    exact T.surfaceFlux_residual_bound_of_cell_diameters h ha hδ hM
      (hdiam v hv) (hdiam w hw) hW hh (hball v hv) (hH v hv)
  · have heq : T.correctedSurfaceField R A h w v = T.surfaceFlux h v w -
        T.conductanceReal v w * (fderiv ℝ h (T.pos v)) (T.pos w - T.pos v) := by
      simp only [correctedSurfaceField, FiniteConductanceNetwork.correctedIncidentFlux,
        FiniteConductanceNetwork.boundaryRewardField, hv, hw, or_true, ite_true, ite_false]
      change T.surfaceResidualField h w v + T.conductanceReal v w *
        T.surfaceTaylorRemainder h v w = _
      rw [hθ, surfaceTaylorRemainder]
      ring
    have hcellB : (T.cell v.val).carrier ⊆ Metric.closedBall (T.pos v) (2 * δ) := by
      intro x hx
      apply Metric.mem_closedBall.mpr
      have hxδ := T.dist_pos_le_diam_bound hx (hdiam v hv)
      rw [dist_comm]
      linarith
    rw [heq]
    have hb := T.surfaceFlux_affine_residual_bound h ha hW
      (hcellB.trans (hball v hv)) hh hM (hdiam v hv)
      (fun x hx => hH v hv x (hcellB hx))
    apply hb.trans
    have harea : 0 ≤ (T.facetVolume v w).toReal := ENNReal.toReal_nonneg
    have hprod : 0 ≤ M * δ * (T.facetVolume v w).toReal := by positivity
    nlinarith

theorem correctedSurfaceField_bound (R : Set T.V) [Fintype R] (A : Set R)
    (h : Euc d → ℝ) {δ M : ℝ} (hδ : 0 ≤ δ) (hM : 0 ≤ M)
    (hdiam : ∀ v ∈ A, Metric.diam (T.cell v.val).carrier ≤ δ)
    {W : Set (Euc d)} (hW : IsOpen W) (hh : ContDiffOn ℝ 2 h W)
    (hball : ∀ v ∈ A, Metric.closedBall (T.pos v) (2 * δ) ⊆ W)
    (hH : ∀ v ∈ A, ∀ x ∈ Metric.closedBall (T.pos v) (2 * δ),
      ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M)
    {v w : R} (hinc : w ∈ A ∨ v ∈ A) (ha : T.adj v w) :
    |T.correctedSurfaceField R A h w v| ≤ 3 * M * δ * (T.facetVolume v w).toReal := by
  rcases hinc with hw | hv
  · rw [T.correctedSurfaceField_antisymm R A h w v, abs_neg]
    have harea : T.facetVolume v w = T.facetVolume w v := T.toTilingData.facetVolume_symm v w
    rw [harea]
    exact T.correctedSurfaceField_bound_at_interior R A h hδ hM hdiam hW hh hball hH
      hw (T.adj_symm ha)
  · exact T.correctedSurfaceField_bound_at_interior R A h hδ hM hdiam hW hh hball hH hv ha

end BouRabeeGwynne.OrthogonalTiling
