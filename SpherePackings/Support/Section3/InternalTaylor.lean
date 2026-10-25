module

-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (files `BouRabeeGwynne/BoundaryCorrectedSurfaceEnergy.lean` and `BouRabeeGwynne/HypIIIErrorBound.lean`
-- at commit cf73d6e): the boundary-corrected error, for complete cells and Taylor control on
-- internal edges only.
public import SpherePackings.Support.Section3.TaylorEnergy
public import SpherePackings.Support.Complete.GaussGreen
public import SpherePackings.Support.Section2.AffineKernel
public import BouRabeeGwynne.BoundaryCorrectedIteration
public import BouRabeeGwynne.BoundaryCorrectedSurfaceEnergy
public import BouRabeeGwynne.FacetAffineResidual
public import BouRabeeGwynne.Section3LocalMaximum

@[expose] public section

/-!
# Internal-edge Taylor control

`rw-spheres-corrected.tex`, the internal-edge comparison before Theorem 3.3.  The quantitative
theorems of Section 3 use the finite Taylor inequality
`|h(w) - h(v) - ∇h(v)·(w - v)| ≤ (M/2) ‖w - v‖²` only on internal edges (both endpoints active),
and the Hessian bound on the cells.  The error `h_D - h_C` is split, after leobon12, as the
boundary correction `b` (the Poisson solution whose source is the Taylor remainders of the
boundary edges) plus the corrected error `f₀`:

* `|b| ≤ 2 M ε²`, from the cell Hessian alone, along the broken segment through a contact point
  (`surfaceTaylorRemainder_abs_le_cells`, `boundaryCorrection_abs_le_cells`);
* the energy of `f₀` is at most `9 M² δ²` times the incident mass
  (`energy_boundaryCorrected_le_internal`);
* the Laplacian of `f₀` at `u` involves the Taylor remainders of the internal edges only, so
  `|Δ f₀(u)| ≤ (M/2) ∑_w a(u, w) ‖w - u‖²` (`abs_laplacian_boundaryCorrected_le`; the sum runs over
  all neighbours, a weaker bound), and `±f₀ + (M/2) ‖· - v‖²` is subharmonic
  (`abs_le_of_abs_laplacian_le`).
-/

namespace SpherePackings

open BouRabeeGwynne BouRabeeGwynne.OrthogonalTiling

open scoped MeasureTheory BigOperators Classical Laplacian

variable {d : ℕ}

/-- The Taylor remainder of an edge from the Hessian on the two cells alone, along the broken
segment `v, z, w` through a contact point `z`:
`|h(w) - h(v) - ∇h(v)·(w - v)| ≤ (M/2) (diam P_v + diam P_w)² ≤ 2 M δ²`. -/
theorem surfaceTaylorRemainder_abs_le_cells (T : OrthogonalTiling d) (h : Euc d → ℝ)
    {v w : T.V} (hvw : T.adj v w) {W : Set (Euc d)} (hW : IsOpen W) (hh : ContDiffOn ℝ 2 h W)
    (hvW : (T.cell v).carrier ⊆ W) (hwW : (T.cell w).carrier ⊆ W) {M δ : ℝ} (hM : 0 ≤ M)
    (hdv : Metric.diam (T.cell v).carrier ≤ δ) (hdw : Metric.diam (T.cell w).carrier ≤ δ)
    (hHv : ∀ x ∈ (T.cell v).carrier, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M)
    (hHw : ∀ x ∈ (T.cell w).carrier, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M) :
    |T.surfaceTaylorRemainder h v w| ≤ 2 * M * δ ^ 2 := by
  obtain ⟨z, hzv, hzw⟩ := hvw.2.1
  have hposv : T.pos v ∈ (T.cell v).carrier := interior_subset (T.pos_mem_interior v)
  have hposw : T.pos w ∈ (T.cell w).carrier := interior_subset (T.pos_mem_interior w)
  have hsegv : segment ℝ (T.pos v) z ⊆ (T.cell v).carrier :=
    (T.cell v).convex.segment_subset hposv hzv
  have hsegw : segment ℝ z (T.pos w) ⊆ (T.cell w).carrier :=
    (T.cell w).convex.segment_subset hzw hposw
  have ha : ‖z - T.pos v‖ ≤ δ := by
    rw [← dist_eq_norm, dist_comm]
    exact (Metric.dist_le_diam_of_mem (T.cell v).compact.isBounded hposv hzv).trans hdv
  have hb : ‖T.pos w - z‖ ≤ δ := by
    rw [← dist_eq_norm]
    exact (Metric.dist_le_diam_of_mem (T.cell w).compact.isBounded hposw hzw).trans hdw
  have ha0 : 0 ≤ ‖z - T.pos v‖ := norm_nonneg _
  have hb0 : 0 ≤ ‖T.pos w - z‖ := norm_nonneg _
  have hCF : ContDiffOn ℝ 1 (fderiv ℝ h) W := hh.fderiv_of_isOpen hW (by norm_num)
  have hdfh : ∀ x ∈ segment ℝ (T.pos v) z, DifferentiableAt ℝ (fderiv ℝ h) x := fun x hx =>
    (hCF.differentiableOn (by norm_num)).differentiableAt (hW.mem_nhds (hvW (hsegv hx)))
  have hgrad : ‖fderiv ℝ h z - fderiv ℝ h (T.pos v)‖ ≤ M * ‖z - T.pos v‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le hdfh (fun x hx => hHv x (hsegv hx))
      (convex_segment (T.pos v) z) (left_mem_segment ℝ (T.pos v) z)
      (right_mem_segment ℝ (T.pos v) z)
  have hF1 := taylor_of_segment hW hh (Set.Subset.trans hsegv hvW)
    (fun x hx => hHv x (hsegv hx))
  have hF2 := taylor_of_segment hW hh (Set.Subset.trans hsegw hwW)
    (fun x hx => hHw x (hsegw hx))
  have hF3 : ‖(fderiv ℝ h z - fderiv ℝ h (T.pos v)) (T.pos w - z)‖ ≤
      M * ‖z - T.pos v‖ * ‖T.pos w - z‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hgrad (norm_nonneg _))
  have hF3' : |(fderiv ℝ h z - fderiv ℝ h (T.pos v)) (T.pos w - z)| ≤
      M * ‖z - T.pos v‖ * ‖T.pos w - z‖ := by
    rw [← Real.norm_eq_abs]
    exact hF3
  have hsplit : T.surfaceTaylorRemainder h v w =
      (h z - h (T.pos v) - fderiv ℝ h (T.pos v) (z - T.pos v)) +
        (h (T.pos w) - h z - fderiv ℝ h z (T.pos w - z)) +
        (fderiv ℝ h z - fderiv ℝ h (T.pos v)) (T.pos w - z) := by
    have hqp : T.pos w - T.pos v = (z - T.pos v) + (T.pos w - z) := by abel
    simp only [surfaceTaylorRemainder, hqp, map_add, sub_apply]
    ring
  have hkey : M / 2 * ‖z - T.pos v‖ ^ 2 + M / 2 * ‖T.pos w - z‖ ^ 2 +
      M * ‖z - T.pos v‖ * ‖T.pos w - z‖ ≤ 2 * M * δ ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg hM (by linarith : (0 : ℝ) ≤ 2 * δ - (‖z - T.pos v‖ + ‖T.pos w - z‖)))
      (by linarith : (0 : ℝ) ≤ 2 * δ + (‖z - T.pos v‖ + ‖T.pos w - z‖))]
  rw [hsplit]
  have htri1 := abs_add_le (h z - h (T.pos v) - fderiv ℝ h (T.pos v) (z - T.pos v) +
    (h (T.pos w) - h z - fderiv ℝ h z (T.pos w - z)))
    ((fderiv ℝ h z - fderiv ℝ h (T.pos v)) (T.pos w - z))
  have htri2 := abs_add_le (h z - h (T.pos v) - fderiv ℝ h (T.pos v) (z - T.pos v))
    (h (T.pos w) - h z - fderiv ℝ h z (T.pos w - z))
  linarith [htri1, htri2, hF1, hF2, hF3', hkey]

/-- The boundary correction with the Taylor remainders as rewards is at most `2 M ε²`, from the
cell Hessian alone. -/
theorem boundaryCorrection_abs_le_cells (T : OrthogonalTiling d) (R : Set T.V) [Fintype R]
    (A : Set R) (hA : (T.finiteNetwork R).BoundaryAccessible A) (h : Euc d → ℝ)
    {W : Set (Euc d)} (hW : IsOpen W) (hh : ContDiffOn ℝ 2 h W)
    (hcellW : ∀ v : R, (T.cell v.val).carrier ⊆ W) {M ε : ℝ} (hM : 0 ≤ M)
    (hdiam : ∀ v : R, Metric.diam (T.cell v.val).carrier ≤ ε)
    (hHcell : ∀ v : R, ∀ x ∈ (T.cell v.val).carrier, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M) (x : R) :
    |(T.finiteNetwork R).boundaryCorrection A hA
        (fun v w => T.surfaceTaylorRemainder h v w) x| ≤ 2 * M * ε ^ 2 :=
  (T.finiteNetwork R).boundaryCorrection_abs_le A hA _ (C := 2 * M * ε ^ 2) (by positivity)
    (fun u _ w _ hpos => by
      have ha : T.adj u.val w.val := T.conductanceReal_pos_iff.mp hpos
      exact surfaceTaylorRemainder_abs_le_cells T h ha hW hh (hcellW u) (hcellW w) hM
        (hdiam u) (hdiam w) (hHcell u) (hHcell w)) x

/-- The corrected surface field at an edge whose active endpoint is `v`: the flux residual of an
internal edge from the Taylor inequality at `v` and the Hessian on the cell of `v`; the affine
residual of a boundary edge from the Hessian on the cell of `v`. -/
private theorem correctedSurfaceField_bound_active (T : OrthogonalTiling d) (R : Set T.V)
    [Fintype R] (A : Set R) (h : Euc d → ℝ) {δ M : ℝ} (hM : 0 ≤ M)
    (hdiam : ∀ v ∈ A, Metric.diam (T.cell v.val).carrier ≤ δ)
    {W : Set (Euc d)} (hW : IsOpen W) (hh : ContDiffOn ℝ 2 h W)
    (hcellW : ∀ v ∈ A, (T.cell v.val).carrier ⊆ W)
    (hHcell : ∀ v ∈ A, ∀ x ∈ (T.cell v.val).carrier, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M)
    (htaylor : ∀ v ∈ A, ∀ w ∈ A, T.adj v.val w.val →
      |T.surfaceTaylorRemainder h v w| ≤ M / 2 * ‖T.pos w - T.pos v‖ ^ 2)
    {v w : R} (hv : v ∈ A) (ha : T.adj v w) :
    |T.correctedSurfaceField R A h w v| ≤ 3 * M * δ * (T.facetVolume v w).toReal := by
  have hθ : T.surfaceResidualField h w v = T.surfaceFlux h v w -
      T.conductanceReal v w * (h (T.pos w) - h (T.pos v)) := by
    rw [surfaceResidualField, T.supportedSurfaceField_of_adj h ha,
      T.conductanceReal_symm w v]
  have hδ : 0 ≤ δ := Metric.diam_nonneg.trans (hdiam v hv)
  by_cases hw : w ∈ A
  · have heq : T.correctedSurfaceField R A h w v = T.surfaceResidualField h w v := by
      simp only [correctedSurfaceField, FiniteConductanceNetwork.correctedIncidentFlux,
        FiniteConductanceNetwork.boundaryRewardField, hv, hw, or_true, ite_true, add_zero]
    rw [heq, hθ, abs_sub_comm]
    exact surfaceFlux_residual_bound_taylor T h ha (hdiam v hv) (hdiam w hw) hW hh
      (hcellW v hv) hM (htaylor v hv w hw ha) (hHcell v hv)
  · have heq : T.correctedSurfaceField R A h w v = T.surfaceFlux h v w -
        T.conductanceReal v w * (fderiv ℝ h (T.pos v)) (T.pos w - T.pos v) := by
      simp only [correctedSurfaceField, FiniteConductanceNetwork.correctedIncidentFlux,
        FiniteConductanceNetwork.boundaryRewardField, hv, hw, or_true, ite_true, ite_false]
      change T.surfaceResidualField h w v + T.conductanceReal v w *
        T.surfaceTaylorRemainder h v w = _
      rw [hθ, surfaceTaylorRemainder]
      ring
    rw [heq]
    have hb := T.surfaceFlux_affine_residual_bound h ha hW (hcellW v hv) hh hM (hdiam v hv)
      (hHcell v hv)
    apply hb.trans
    have harea : 0 ≤ (T.facetVolume v w).toReal := ENNReal.toReal_nonneg
    have hprod : 0 ≤ M * δ * (T.facetVolume v w).toReal := by positivity
    nlinarith

/-- The corrected surface field at an edge incident to `A`: the flux residual of an internal edge
from the Taylor inequality at one endpoint and the Hessian on its cell; the affine residual of a
boundary edge from the Hessian on the cell of its active endpoint. -/
theorem correctedSurfaceField_bound_internal (T : OrthogonalTiling d) (R : Set T.V) [Fintype R]
    (A : Set R) (h : Euc d → ℝ) {δ M : ℝ} (hM : 0 ≤ M)
    (hdiam : ∀ v ∈ A, Metric.diam (T.cell v.val).carrier ≤ δ)
    {W : Set (Euc d)} (hW : IsOpen W) (hh : ContDiffOn ℝ 2 h W)
    (hcellW : ∀ v ∈ A, (T.cell v.val).carrier ⊆ W)
    (hHcell : ∀ v ∈ A, ∀ x ∈ (T.cell v.val).carrier, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M)
    (htaylor : ∀ v ∈ A, ∀ w ∈ A, T.adj v.val w.val →
      |T.surfaceTaylorRemainder h v w| ≤ M / 2 * ‖T.pos w - T.pos v‖ ^ 2)
    {v w : R} (hinc : w ∈ A ∨ v ∈ A) (ha : T.adj v w) :
    |T.correctedSurfaceField R A h w v| ≤ 3 * M * δ * (T.facetVolume v w).toReal := by
  rcases hinc with hw | hv
  · rw [T.correctedSurfaceField_antisymm R A h w v, abs_neg]
    have harea : T.facetVolume v w = T.facetVolume w v := T.toTilingData.facetVolume_symm v w
    rw [harea]
    exact correctedSurfaceField_bound_active T R A h hM hdiam hW hh hcellW hHcell htaylor hw
      (T.adj_symm ha)
  · exact correctedSurfaceField_bound_active T R A h hM hdiam hW hh hcellW hHcell htaylor hv ha

/-- The energy of the corrected error: at most `9 M² δ²` times the incident mass, with the Taylor
inequality on internal edges only. -/
theorem energy_boundaryCorrected_le_internal (hd : 1 ≤ d) (T : OrthogonalTiling d)
    (R : Set T.V) [Fintype R] (A : Set R) (hA : (T.finiteNetwork R).BoundaryAccessible A)
    (hD : R → ℝ) (h : Euc d → ℝ) {δ M : ℝ} (hM : 0 ≤ M)
    (hsol : (T.finiteNetwork R).SolvesDirichlet A (fun v => h (T.pos v)) hD)
    (hdiam : ∀ v ∈ A, Metric.diam (T.cell v.val).carrier ≤ δ)
    (hcomplete : ∀ v ∈ A, CompleteCell T v.val)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v.val w → w ∈ R)
    {W : Set (Euc d)} (hW : IsOpen W) (hh : ContDiffOn ℝ 2 h W)
    (hcellW : ∀ v ∈ A, (T.cell v.val).carrier ⊆ W)
    (hharm : ∀ v ∈ A, ∀ x ∈ (T.cell v.val).carrier, Δ h x = 0)
    (hHcell : ∀ v ∈ A, ∀ x ∈ (T.cell v.val).carrier, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M)
    (htaylor : ∀ v ∈ A, ∀ w ∈ A, T.adj v.val w.val →
      |T.surfaceTaylorRemainder h v w| ≤ M / 2 * ‖T.pos w - T.pos v‖ ^ 2) :
    (T.finiteNetwork R).energy
      ((hD - fun v : R => h (T.pos v)) - (T.finiteNetwork R).boundaryCorrection A hA
        (fun v w => T.surfaceTaylorRemainder h v w)) ≤
      9 * M ^ 2 * δ ^ 2 * T.incidentMass R A := by
  let N := T.finiteNetwork R
  let g : R → ℝ := fun v => h (T.pos v)
  let θ : R → R → ℝ := fun w v => T.surfaceResidualField h w v
  let r : R → R → ℝ := fun v w => T.surfaceTaylorRemainder h v w
  let Φ : R → R → ℝ := fun w v => T.supportedSurfaceField h w v
  have hθ : IsDiscreteVectorField θ := fun w v => T.surfaceResidualField_antisymm h w v
  have hsupport : ∀ w v, N.a w v = 0 → θ w v = 0 :=
    fun _ _ ha => T.surfaceResidualField_support h ha
  have he : ∀ v, v ∉ A → (hD - g) v = 0 := by
    intro v hv
    simp only [Pi.sub_apply, hsol.2 v hv, g, sub_self]
  have hflux : ∀ v ∈ A, discreteDiv Φ v = 0 := by
    intro v hv
    have hfinite := (hcomplete v hv).1
    change discreteDiv (fun w u : R => T.supportedSurfaceField h w u) v = 0
    rw [T.finite_div_supportedSurfaceField R h v hfinite (fun w hw => hneighbors v hv w hw)]
    exact sum_surfaceFlux_eq_zero_of_complete hd T (hcomplete v hv) hW (hcellW v hv) hh
      (hharm v hv)
  have hdiv : ∀ v ∈ A, discreteDiv θ v = N.laplacian (hD - g) v := by
    intro v hv
    have hsplit : discreteDiv θ v = discreteDiv Φ v -
        discreteDiv (N.weightedGradient g) v := by
      simp only [θ, Φ, discreteDiv, surfaceResidualField,
        FiniteConductanceNetwork.weightedGradient, discreteGrad, N, finiteNetwork, g,
        Finset.sum_sub_distrib]
    rw [hsplit, hflux v hv, N.div_weightedGradient_eq_laplacian,
      N.laplacian_sub, hsol.1 v hv]
  have hbound := N.energy_boundaryCorrected_le_flux A hA (hD - g) θ r
    hθ hsupport he hdiv
  have hδ : ∀ v ∈ A, 0 ≤ δ := fun v hv => Metric.diam_nonneg.trans (hdiam v hv)
  have hterm : ∀ v w : R,
      (T.correctedSurfaceField R A h w v) ^ 2 / N.a w v ≤
        (3 * M * δ) ^ 2 * (if (w ∈ A ∨ v ∈ A) ∧ T.adj v.val w.val then
          (T.facetVolume v w).toReal * ‖T.pos w - T.pos v‖ else 0) := by
    intro v w
    by_cases hinc : w ∈ A ∨ v ∈ A
    · by_cases hadj : T.adj v.val w.val
      · simp only [hinc, hadj, and_self, ite_true]
        change _ / T.conductanceReal w v ≤ _
        rw [T.conductanceReal_symm w v]
        have hδ0 : 0 ≤ δ := by rcases hinc with hw | hv; exacts [hδ w hw, hδ v hv]
        simpa only [mul_assoc] using T.residual_dual_energy_bound hadj
          (show 0 ≤ 3 * M * δ by positivity)
          (correctedSurfaceField_bound_internal T R A h hM hdiam hW hh hcellW hHcell htaylor
            hinc hadj)
      · have hrev : ¬ T.adj w.val v.val := fun ha => hadj (T.adj_symm ha)
        have ha : N.a w v = 0 := by
          change T.conductanceReal w v = 0
          simp only [conductanceReal, hrev, ite_false]
        simp only [ha, div_zero, hadj, and_false, ite_false, mul_zero, le_refl]
    · have hv : v ∉ A := fun hv => hinc (Or.inr hv)
      have hw : w ∉ A := fun hw => hinc (Or.inl hw)
      have hz : T.correctedSurfaceField R A h w v = 0 := by
        simp only [correctedSurfaceField, FiniteConductanceNetwork.correctedIncidentFlux,
          FiniteConductanceNetwork.boundaryRewardField, hv, hw, or_self, ite_false, add_zero]
      simp only [hz, zero_pow (by decide : 2 ≠ 0), zero_div, hinc, false_and,
        ite_false, mul_zero, le_refl]
  have hmass : ((1 / 2 : ℝ) * ∑ v : R, ∑ w : R,
      if (w ∈ A ∨ v ∈ A) ∧ T.adj v.val w.val then
        (T.facetVolume v w).toReal * ‖T.pos w - T.pos v‖ else 0) = T.incidentMass R A := by
    rw [T.incidentMass_eq_half_ordered]
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro w _
    simp only [or_comm, and_comm]
  calc
    _ ≤ (1 / 2 : ℝ) * N.dualEnergy (T.correctedSurfaceField R A h) := hbound
    _ ≤ (1 / 2 : ℝ) * ∑ v : R, ∑ w : R,
        (3 * M * δ) ^ 2 * (if (w ∈ A ∨ v ∈ A) ∧ T.adj v.val w.val then
          (T.facetVolume v w).toReal * ‖T.pos w - T.pos v‖ else 0) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun w _ => hterm v w
    _ = (3 * M * δ) ^ 2 * ((1 / 2 : ℝ) * ∑ v : R, ∑ w : R,
        if (w ∈ A ∨ v ∈ A) ∧ T.adj v.val w.val then
          (T.facetVolume v w).toReal * ‖T.pos w - T.pos v‖ else 0) := by
      simp only [← Finset.mul_sum]
      ring
    _ = _ := by rw [hmass]; ring

/-- The identity `‖w - z‖² - ‖u - z‖² = ‖w - u‖² + 2 ⟪u - z, w - u⟫`. -/
private lemma norm_sq_sub_sq_eq_internal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u w z : E) :
    ‖w - z‖ ^ 2 - ‖u - z‖ ^ 2 = ‖w - u‖ ^ 2 + 2 * inner ℝ (u - z) (w - u) := by
  have h : w - z = (w - u) + (u - z) := by abel
  rw [h, norm_add_sq_real, real_inner_comm (u - z) (w - u)]
  ring

/-- By Lemma 2.2 at a complete vertex `u`, `∑ a(u, w) ⟪p, w - u⟫ = 0`. -/
private lemma sum_inner_eq_zero_of_complete (hd : 1 ≤ d) (T : OrthogonalTiling d)
    (U : Set (Euc d)) [Fintype (T.closedVertices U)] (u : T.closedVertices U)
    (hu : u ∈ T.finiteInterior U) (hcomplete : CompleteCell T u) (p : Euc d) :
    ∑ w : T.closedVertices U,
      (T.finiteNetwork (T.closedVertices U)).a u w * inner ℝ p (T.pos w - T.pos u) = 0 := by
  have h1 : (T.finiteNetwork (T.closedVertices U)).laplacian
      (fun w => inner ℝ p (T.pos w) + 0) u = 0 := by
    rw [T.closedNetwork_laplacian U (fun x => inner ℝ p (T.pos x) + 0) u hu hcomplete.1]
    exact discreteLaplacian_affine_eq_zero_of_complete hd T (u : T.V) hcomplete p 0
  simp only [FiniteConductanceNetwork.laplacian, add_zero] at h1
  simp only [inner_sub_right]
  exact h1

/-- By Lemma 2.2 at a complete vertex `u`, `∑ a(u, w) L(w - u) = 0` for a continuous linear
functional `L`. -/
private lemma sum_clm_eq_zero_of_complete (hd : 1 ≤ d) (T : OrthogonalTiling d)
    (U : Set (Euc d)) [Fintype (T.closedVertices U)] (u : T.closedVertices U)
    (hu : u ∈ T.finiteInterior U) (hcomplete : CompleteCell T u) (L : Euc d →L[ℝ] ℝ) :
    ∑ w : T.closedVertices U,
      (T.finiteNetwork (T.closedVertices U)).a u w * L (T.pos w - T.pos u) = 0 := by
  obtain ⟨p, hp⟩ : ∃ p : Euc d, ∀ x, L x = inner ℝ p x :=
    ⟨(InnerProductSpace.toDual ℝ (Euc d)).symm L, fun x => InnerProductSpace.toDual_symm_apply.symm⟩
  simp only [hp]
  exact sum_inner_eq_zero_of_complete hd T U u hu hcomplete p

/-- By Lemma 2.2 at a complete vertex, the discrete Laplacian of `‖· - z‖²` is
`∑ a(u, w) ‖w - u‖²`. -/
theorem laplacian_sq_dist_of_complete (hd : 1 ≤ d) (T : OrthogonalTiling d) (U : Set (Euc d))
    [Fintype (T.closedVertices U)] (u : T.closedVertices U) (hu : u ∈ T.finiteInterior U)
    (hcomplete : CompleteCell T u) (z : Euc d) :
    (T.finiteNetwork (T.closedVertices U)).laplacian (fun w => ‖T.pos w - z‖ ^ 2) u =
      ∑ w : T.closedVertices U,
        (T.finiteNetwork (T.closedVertices U)).a u w * ‖T.pos w - T.pos u‖ ^ 2 := by
  simp only [FiniteConductanceNetwork.laplacian]
  have hlin := sum_inner_eq_zero_of_complete hd T U u hu hcomplete (T.pos u - z)
  calc ∑ w : T.closedVertices U, (T.finiteNetwork (T.closedVertices U)).a u w *
        (‖T.pos w - z‖ ^ 2 - ‖T.pos u - z‖ ^ 2)
      = ∑ w : T.closedVertices U, ((T.finiteNetwork (T.closedVertices U)).a u w *
          ‖T.pos w - T.pos u‖ ^ 2 + 2 * ((T.finiteNetwork (T.closedVertices U)).a u w *
          inner ℝ (T.pos u - z) (T.pos w - T.pos u))) :=
        Finset.sum_congr rfl fun w _ => by rw [norm_sq_sub_sq_eq_internal]; ring
    _ = ∑ w : T.closedVertices U, (T.finiteNetwork (T.closedVertices U)).a u w *
          ‖T.pos w - T.pos u‖ ^ 2 + 2 * ∑ w : T.closedVertices U,
          (T.finiteNetwork (T.closedVertices U)).a u w *
            inner ℝ (T.pos u - z) (T.pos w - T.pos u) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = ∑ w : T.closedVertices U, (T.finiteNetwork (T.closedVertices U)).a u w *
          ‖T.pos w - T.pos u‖ ^ 2 := by
        rw [hlin, mul_zero, add_zero]

/-- The Laplacian of the corrected error at a complete vertex of `A` is minus the conductance
sum of the Taylor remainders over the internal edges, so it is at most
`(M/2) ∑ a(u, w) ‖w - u‖²` in absolute value. -/
theorem abs_laplacian_boundaryCorrected_le (hd : 1 ≤ d) (T : OrthogonalTiling d)
    (U : Set (Euc d)) [Fintype (T.closedVertices U)] (A : Set (T.closedVertices U))
    (hAU : A ⊆ T.finiteInterior U)
    (hA : (T.finiteNetwork (T.closedVertices U)).BoundaryAccessible A)
    (hD : T.closedVertices U → ℝ) (h : Euc d → ℝ)
    (hsol : (T.finiteNetwork (T.closedVertices U)).SolvesDirichlet A
      (fun v => h (T.pos v)) hD)
    (hcomplete : ∀ v ∈ A, CompleteCell T v.val) {M : ℝ} (hM : 0 ≤ M)
    (htaylor : ∀ v ∈ A, ∀ w ∈ A, T.adj v.val w.val →
      |T.surfaceTaylorRemainder h v w| ≤ M / 2 * ‖T.pos w - T.pos v‖ ^ 2)
    {u : T.closedVertices U} (hu : u ∈ A) :
    |(T.finiteNetwork (T.closedVertices U)).laplacian
        ((hD - fun v : T.closedVertices U => h (T.pos v)) -
          (T.finiteNetwork (T.closedVertices U)).boundaryCorrection
            A hA (fun v w => T.surfaceTaylorRemainder h v w)) u| ≤
      M / 2 * ∑ w : T.closedVertices U,
        (T.finiteNetwork (T.closedVertices U)).a u w * ‖T.pos w - T.pos u‖ ^ 2 := by
  have hLg : (T.finiteNetwork (T.closedVertices U)).laplacian
      (fun v : T.closedVertices U => h (T.pos v)) u =
      ∑ w : T.closedVertices U, (T.finiteNetwork (T.closedVertices U)).a u w *
        T.surfaceTaylorRemainder h u w := by
    have hlin := sum_clm_eq_zero_of_complete hd T U u (hAU hu) (hcomplete u hu)
      (fderiv ℝ h (T.pos u))
    simp only [FiniteConductanceNetwork.laplacian]
    calc ∑ w : T.closedVertices U, (T.finiteNetwork (T.closedVertices U)).a u w *
          (h (T.pos w) - h (T.pos u))
        = ∑ w : T.closedVertices U, ((T.finiteNetwork (T.closedVertices U)).a u w *
            T.surfaceTaylorRemainder h u w +
            (T.finiteNetwork (T.closedVertices U)).a u w *
              fderiv ℝ h (T.pos u) (T.pos w - T.pos u)) :=
          Finset.sum_congr rfl fun w _ => by unfold surfaceTaylorRemainder; ring
      _ = ∑ w : T.closedVertices U, (T.finiteNetwork (T.closedVertices U)).a u w *
            T.surfaceTaylorRemainder h u w +
          ∑ w : T.closedVertices U, (T.finiteNetwork (T.closedVertices U)).a u w *
            fderiv ℝ h (T.pos u) (T.pos w - T.pos u) := Finset.sum_add_distrib
      _ = _ := by rw [hlin, add_zero]
  have hLb : (T.finiteNetwork (T.closedVertices U)).laplacian
      ((T.finiteNetwork (T.closedVertices U)).boundaryCorrection A hA
        (fun v w => T.surfaceTaylorRemainder h v w)) u =
      -(∑ w : T.closedVertices U, if w ∉ A then
        (T.finiteNetwork (T.closedVertices U)).a u w * T.surfaceTaylorRemainder h u w else 0) :=
    (T.finiteNetwork (T.closedVertices U)).boundaryCorrection_laplacian A hA
      (fun v w => T.surfaceTaylorRemainder h v w) hu
  have hS : ∑ w : T.closedVertices U,
      (T.finiteNetwork (T.closedVertices U)).a u w * T.surfaceTaylorRemainder h u w =
      (∑ w : T.closedVertices U, if w ∉ A then
        (T.finiteNetwork (T.closedVertices U)).a u w * T.surfaceTaylorRemainder h u w else 0) +
      ∑ w : T.closedVertices U, if w ∈ A then
        (T.finiteNetwork (T.closedVertices U)).a u w * T.surfaceTaylorRemainder h u w else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases hw : w ∈ A <;> simp [hw]
  have hL : (T.finiteNetwork (T.closedVertices U)).laplacian
      ((hD - fun v : T.closedVertices U => h (T.pos v)) -
        (T.finiteNetwork (T.closedVertices U)).boundaryCorrection A hA
          (fun v w => T.surfaceTaylorRemainder h v w)) u =
      -(∑ w : T.closedVertices U, if w ∈ A then
        (T.finiteNetwork (T.closedVertices U)).a u w * T.surfaceTaylorRemainder h u w else 0) := by
    rw [(T.finiteNetwork (T.closedVertices U)).laplacian_sub,
      (T.finiteNetwork (T.closedVertices U)).laplacian_sub, hsol.1 u hu, hLg, hLb, hS]
    ring
  have hterm : ∀ w : T.closedVertices U,
      |if w ∈ A then (T.finiteNetwork (T.closedVertices U)).a u w *
        T.surfaceTaylorRemainder h u w else 0| ≤
        (T.finiteNetwork (T.closedVertices U)).a u w * (M / 2 * ‖T.pos w - T.pos u‖ ^ 2) := by
    intro w
    have ha0 := (T.finiteNetwork (T.closedVertices U)).nonneg u w
    by_cases hw : w ∈ A
    · by_cases hpos : 0 < (T.finiteNetwork (T.closedVertices U)).a u w
      · simp only [hw, ↓reduceIte]
        rw [abs_mul, abs_of_nonneg ha0]
        exact mul_le_mul_of_nonneg_left
          (htaylor u hu w hw (T.conductanceReal_pos_iff.mp hpos)) ha0
      · have ha : (T.finiteNetwork (T.closedVertices U)).a u w = 0 :=
          le_antisymm (not_lt.mp hpos) ha0
        simp [hw, ha]
    · simp only [hw, ↓reduceIte, abs_zero]
      exact mul_nonneg ha0 (mul_nonneg (div_nonneg hM (by norm_num)) (sq_nonneg _))
  rw [hL, abs_neg]
  calc |∑ w : T.closedVertices U, if w ∈ A then
          (T.finiteNetwork (T.closedVertices U)).a u w * T.surfaceTaylorRemainder h u w else 0|
      ≤ ∑ w : T.closedVertices U, |if w ∈ A then
          (T.finiteNetwork (T.closedVertices U)).a u w * T.surfaceTaylorRemainder h u w else 0| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ w : T.closedVertices U,
          (T.finiteNetwork (T.closedVertices U)).a u w * (M / 2 * ‖T.pos w - T.pos u‖ ^ 2) :=
        Finset.sum_le_sum fun w _ => hterm w
    _ = M / 2 * ∑ w : T.closedVertices U,
          (T.finiteNetwork (T.closedVertices U)).a u w * ‖T.pos w - T.pos u‖ ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun w _ => by ring

/-- The comparison principle: if `|Δφ| ≤ c Δq` on `Q`, then `|φ(v)| ≤ η` at `v ∈ Q` with
`c q(v) ≥ 0`, whenever `|φ| + c q ≤ η` on the external boundary of `Q`. -/
theorem abs_le_of_abs_laplacian_le {V : Type*} [Fintype V] (N : FiniteConductanceNetwork V)
    (Q : Set V) (hQ : N.BoundaryAccessible Q) (φ q : V → ℝ) {c η : ℝ}
    (hlap : ∀ u ∈ Q, |N.laplacian φ u| ≤ c * N.laplacian q u)
    (hbdry : ∀ w ∈ N.externalBoundary Q, |φ w| + c * q w ≤ η)
    {v : V} (hv : v ∈ Q) (hqv : 0 ≤ c * q v) : |φ v| ≤ η := by
  have hsub : ∀ u ∈ Q, 0 ≤ N.laplacian (fun x => φ x + c * q x) u := by
    intro u hu
    have habs := abs_le.mp (hlap u hu)
    have hL := N.laplacian_add φ (fun x => c * q x) u
    have hc := N.laplacian_const_mul c q u
    change 0 ≤ N.laplacian (φ + fun x => c * q x) u
    rw [hL, hc]
    linarith [habs.1]
  have hsub' : ∀ u ∈ Q, 0 ≤ N.laplacian (fun x => -φ x + c * q x) u := by
    intro u hu
    have habs := abs_le.mp (hlap u hu)
    have hL := N.laplacian_add (-φ) (fun x => c * q x) u
    have hn := N.laplacian_neg φ u
    have hc := N.laplacian_const_mul c q u
    change 0 ≤ N.laplacian (-φ + fun x => c * q x) u
    rw [hL, hn, hc]
    linarith [habs.2]
  have hbdry₁ : ∀ w ∈ N.externalBoundary Q, φ w + c * q w ≤ η := fun w hw => by
    linarith [le_abs_self (φ w), hbdry w hw]
  have hbdry₂ : ∀ w ∈ N.externalBoundary Q, -φ w + c * q w ≤ η := fun w hw => by
    linarith [neg_le_abs (φ w), hbdry w hw]
  have h1 : φ v + c * q v ≤ η :=
    N.local_maximum_principle Q hQ (fun x => φ x + c * q x) η hsub hbdry₁ v hv
  have h2 : -φ v + c * q v ≤ η :=
    N.local_maximum_principle Q hQ (fun x => -φ x + c * q x) η hsub' hbdry₂ v hv
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end SpherePackings
