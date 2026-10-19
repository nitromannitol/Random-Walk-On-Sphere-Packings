-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (files `BouRabeeGwynne/HypIIIErrorBound.lean` and `BouRabeeGwynne/BoundaryCorrectedSurfaceEnergy.lean`
-- at commit cf73d6e): the error and energy estimates of the corrected iteration, with the Hessian
-- bound on the cells and the edge segments in place of the balls of radius twice the mesh.
import SpherePackings.Support.Section3.EnergyMinimal
import BouRabeeGwynne.HypIIIErrorBound
import BouRabeeGwynne.BoundaryCorrectedSurfaceEnergy
import BouRabeeGwynne.HypIIICorrectedTrimming
import BouRabeeGwynne.FacetAffineResidual

/-!
# The corrected iteration of Theorem 3.7 under the edge-segment hypothesis (intermediate result)

**Intermediate result**, under the earlier, stronger hypotheses (the cells of `V[U]` in the interior
of the ambient set, and the Hessian bound also on the edge segments of `E[Ū]`); superseded by
`DecayInternal.lean` (complete cells, and Taylor control on internal edges only).

leobon12's corrected iteration (`correctedRegions`) controls `h_C` on the balls of radius `2 ε`
around the vertices of `V[U]`.  Here the same chain of estimates is proved with the hypotheses of
the edge-segment form of Proposition 2.6 (`EnergyMinimal.lean`): `h_C` harmonic near the cells, with the
Hessian bound `M` on the cells and on the edge segments incident to the region.  The Taylor remainder
of an edge is controlled on its segment, the flux residual of an interior edge by
`surfaceFlux_residual_bound_segment`, and that of a boundary edge on the cell of its interior
endpoint.  The regions, corrections and diameters are leobon12's, unchanged.
-/

namespace SpherePackings

open BouRabeeGwynne BouRabeeGwynne.OrthogonalTiling

open scoped MeasureTheory BigOperators Classical ENNReal

variable {d : ℕ}

/-- The Taylor remainder of an edge, from the Hessian on its segment. -/
theorem surfaceTaylorRemainder_abs_le_segment (T : OrthogonalTiling d) (h : Euc d → ℝ)
    {v w : T.V} {δ M : ℝ} (hM : 0 ≤ M) (hdist : dist (T.pos v) (T.pos w) ≤ 2 * δ)
    {W' : Set (Euc d)} (hW' : IsOpen W') (hh' : ContDiffOn ℝ 2 h W')
    (hseg : segment ℝ (T.pos v) (T.pos w) ⊆ W')
    (hH : ∀ x ∈ segment ℝ (T.pos v) (T.pos w), ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M) :
    |T.surfaceTaylorRemainder h v w| ≤ 6 * M * δ ^ 2 := by
  have hCF' : ContDiffOn ℝ 1 (fderiv ℝ h) W' := hh'.fderiv_of_isOpen hW' (by norm_num)
  have hdiff : ∀ x ∈ segment ℝ (T.pos v) (T.pos w), DifferentiableAt ℝ h x := fun x hx =>
    (hh'.differentiableOn (by norm_num)).differentiableAt (hW'.mem_nhds (hseg hx))
  have hdiff' : ∀ x ∈ segment ℝ (T.pos v) (T.pos w), DifferentiableAt ℝ (fderiv ℝ h) x :=
    fun x hx => (hCF'.differentiableOn (by norm_num)).differentiableAt (hW'.mem_nhds (hseg hx))
  have hδ : 0 ≤ δ := by linarith [dist_nonneg (x := T.pos v) (y := T.pos w)]
  have hbound : ∀ x ∈ segment ℝ (T.pos v) (T.pos w),
      ‖fderiv ℝ h x - fderiv ℝ h (T.pos v)‖ ≤ M * (2 * δ) := by
    intro x hx
    have h1 := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff' hH (convex_segment _ _)
      (left_mem_segment ℝ (T.pos v) (T.pos w)) hx
    have hxp : ‖x - T.pos v‖ ≤ 2 * δ := by
      have := dist_add_dist_of_mem_segment hx
      rw [← dist_eq_norm, dist_comm]
      linarith [dist_nonneg (x := x) (y := T.pos w)]
    exact h1.trans (mul_le_mul_of_nonneg_left hxp hM)
  have hg : ∀ x ∈ segment ℝ (T.pos v) (T.pos w),
      HasFDerivWithinAt (fun z => h z - (fderiv ℝ h (T.pos v)) z)
        (fderiv ℝ h x - fderiv ℝ h (T.pos v)) (segment ℝ (T.pos v) (T.pos w)) x := fun x hx =>
    ((hdiff x hx).hasFDerivAt.sub (fderiv ℝ h (T.pos v)).hasFDerivAt).hasFDerivWithinAt
  have hres := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hg hbound (convex_segment _ _)
    (left_mem_segment ℝ (T.pos v) (T.pos w)) (right_mem_segment ℝ (T.pos v) (T.pos w))
  have hid : (h (T.pos w) - (fderiv ℝ h (T.pos v)) (T.pos w)) -
      (h (T.pos v) - (fderiv ℝ h (T.pos v)) (T.pos v)) = T.surfaceTaylorRemainder h v w := by
    simp only [surfaceTaylorRemainder, map_sub]
    ring
  rw [hid, Real.norm_eq_abs] at hres
  have hqp : ‖T.pos w - T.pos v‖ ≤ 2 * δ := by rw [← dist_eq_norm, dist_comm]; exact hdist
  calc _ ≤ M * (2 * δ) * ‖T.pos w - T.pos v‖ := hres
    _ ≤ M * (2 * δ) * (2 * δ) := mul_le_mul_of_nonneg_left hqp (by positivity)
    _ ≤ 6 * M * δ ^ 2 := by nlinarith [mul_nonneg hM (sq_nonneg δ)]

/-- The corrected surface field at an edge with an endpoint in the region, from the Hessian on the
cells of the region and on the edge segments. -/
theorem correctedSurfaceField_bound_at_interior_segment (T : OrthogonalTiling d) (R : Set T.V)
    [Fintype R] (A : Set R) (h : Euc d → ℝ) {δ M : ℝ} (hM : 0 ≤ M)
    (hdiam : ∀ v ∈ A, Metric.diam (T.cell v.val).carrier ≤ δ)
    {W : Set (Euc d)} (hW : IsOpen W) (hh : ContDiffOn ℝ 2 h W)
    (hcellW : ∀ v ∈ A, (T.cell v.val).carrier ⊆ W)
    (hHcell : ∀ v ∈ A, ∀ x ∈ (T.cell v.val).carrier, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M)
    {W' : Set (Euc d)} (hW' : IsOpen W') (hh' : ContDiffOn ℝ 2 h W')
    (hseg : ∀ v ∈ A, ∀ w : R, T.adj v w → segment ℝ (T.pos v) (T.pos w) ⊆ W')
    (hHseg : ∀ v ∈ A, ∀ w : R, T.adj v w → ∀ x ∈ segment ℝ (T.pos v) (T.pos w),
      ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M)
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
    exact surfaceFlux_residual_bound_segment T h ha (hdiam v hv) (hdiam w hw) hW hh
      (hcellW w hw) hW' hh' (hseg v hv w ha) hM (hHseg v hv w ha) (hHcell w hw)
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

/-- The corrected surface field at every edge incident to the region. -/
theorem correctedSurfaceField_bound_segment (T : OrthogonalTiling d) (R : Set T.V) [Fintype R]
    (A : Set R) (h : Euc d → ℝ) {δ M : ℝ} (hM : 0 ≤ M)
    (hdiam : ∀ v ∈ A, Metric.diam (T.cell v.val).carrier ≤ δ)
    {W : Set (Euc d)} (hW : IsOpen W) (hh : ContDiffOn ℝ 2 h W)
    (hcellW : ∀ v ∈ A, (T.cell v.val).carrier ⊆ W)
    (hHcell : ∀ v ∈ A, ∀ x ∈ (T.cell v.val).carrier, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M)
    {W' : Set (Euc d)} (hW' : IsOpen W') (hh' : ContDiffOn ℝ 2 h W')
    (hseg : ∀ v ∈ A, ∀ w : R, T.adj v w → segment ℝ (T.pos v) (T.pos w) ⊆ W')
    (hHseg : ∀ v ∈ A, ∀ w : R, T.adj v w → ∀ x ∈ segment ℝ (T.pos v) (T.pos w),
      ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M)
    {v w : R} (hinc : w ∈ A ∨ v ∈ A) (ha : T.adj v w) :
    |T.correctedSurfaceField R A h w v| ≤ 3 * M * δ * (T.facetVolume v w).toReal := by
  rcases hinc with hw | hv
  · rw [T.correctedSurfaceField_antisymm R A h w v, abs_neg]
    have harea : T.facetVolume v w = T.facetVolume w v := T.toTilingData.facetVolume_symm v w
    rw [harea]
    exact correctedSurfaceField_bound_at_interior_segment T R A h hM hdiam hW hh hcellW hHcell
      hW' hh' hseg hHseg hw (T.adj_symm ha)
  · exact correctedSurfaceField_bound_at_interior_segment T R A h hM hdiam hW hh hcellW hHcell
      hW' hh' hseg hHseg hv ha

/-- leobon12's boundary-corrected energy estimate, with the Hessian bound on the cells of the
region and on its edge segments. -/
theorem energy_boundaryCorrected_le_hessian_diam_mass_segment
    (hd : 1 ≤ d) (T : OrthogonalTiling d) (R : Set T.V) [Fintype R] (A : Set R)
    (hA : (T.finiteNetwork R).BoundaryAccessible A)
    (hD : R → ℝ) (h : Euc d → ℝ) {δ M : ℝ} (hM : 0 ≤ M)
    (hsol : (T.finiteNetwork R).SolvesDirichlet A (fun v => h (T.pos v)) hD)
    (hdiam : ∀ v ∈ A, Metric.diam (T.cell v.val).carrier ≤ δ)
    (hcellD : ∀ v ∈ A, (T.cell v.val).carrier ⊆ interior T.domain)
    (hneighbors : ∀ v ∈ A, T.neighbors v.val ⊆ R)
    {W : Set (Euc d)} (hW : IsOpen W) (hh : IsHarmonicOn h W)
    (hcellW : ∀ v ∈ A, (T.cell v.val).carrier ⊆ W)
    (hHcell : ∀ v ∈ A, ∀ x ∈ (T.cell v.val).carrier, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M)
    {W' : Set (Euc d)} (hW' : IsOpen W') (hh' : ContDiffOn ℝ 2 h W')
    (hseg : ∀ v ∈ A, ∀ w : R, T.adj v w → segment ℝ (T.pos v) (T.pos w) ⊆ W')
    (hHseg : ∀ v ∈ A, ∀ w : R, T.adj v w → ∀ x ∈ segment ℝ (T.pos v) (T.pos w),
      ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M) :
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
    have hfinite := T.neighbors_finite v.val ((hcellD v hv).trans interior_subset)
    change discreteDiv (fun w u : R => T.supportedSurfaceField h w u) v = 0
    rw [T.finite_div_supportedSurfaceField R h v hfinite (hneighbors v hv)]
    exact T.sum_surfaceFlux_eq_zero_of_harmonic hd v.val (hcellD v hv) hfinite hW
      (hcellW v hv) hh
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
          (correctedSurfaceField_bound_segment T R A h hM hdiam hW hh.contDiffOn hcellW hHcell
            hW' hh' hseg hHseg hinc hadj)
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

/-- leobon12's trimming step, with the Hessian bound on the cells of the region and on its edge
segments. -/
theorem boundaryCorrected_trimmed_mass_le_half_segment (hd : 1 ≤ d) (T : OrthogonalTiling d)
    (R : Set T.V) [Fintype R] (A : Set R)
    (hA : (T.finiteNetwork R).BoundaryAccessible A)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    (hcellD : ∀ v ∈ A, (T.cell v).carrier ⊆ interior T.domain)
    (h : Euc d → ℝ) (e : Euc d) (he : e ≠ 0) (a b : ℝ) (hab : a ≤ b)
    (hheight : ∀ v ∈ A, ∀ x ∈ (T.cell v).carrier,
      inner ℝ e x / inner ℝ e e ∈ Set.Icc a b)
    {K M ε δ : ℝ} (hK : 0 < K) (hM : 0 < M) (hε : 0 < ε)
    (hδ : 0 < δ) (hδε : δ ≤ ε)
    (hwidth : 12 * ((d : ℝ) * ‖e‖ * (b - a)) ≤ K)
    (hsmall : 144 * M ^ 2 * ε ^ 2 ≤ 1)
    (hlength : ∀ v w : R, T.adj v w → ‖T.pos w - T.pos v‖ ≤ 2 * ε)
    (hdiam : ∀ v ∈ A, Metric.diam (T.cell v).carrier ≤ δ)
    {W : Set (Euc d)} (hW : IsOpen W) (hh : IsHarmonicOn h W)
    (hcellW : ∀ v ∈ A, (T.cell v.val).carrier ⊆ W)
    (hHcell : ∀ v ∈ A, ∀ x ∈ (T.cell v.val).carrier, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M)
    {W' : Set (Euc d)} (hW' : IsOpen W') (hh' : ContDiffOn ℝ 2 h W')
    (hseg : ∀ v ∈ A, ∀ w : R, T.adj v w → segment ℝ (T.pos v) (T.pos w) ⊆ W')
    (hHseg : ∀ v ∈ A, ∀ w : R, T.adj v w → ∀ x ∈ segment ℝ (T.pos v) (T.pos w),
      ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M) :
    let f := (T.finiteNetwork R).boundaryCorrectedError A hA
      (fun v => h (T.pos v)) (fun v w => T.surfaceTaylorRemainder h v w)
    T.incidentMass R ((T.finiteNetwork R).trimmedErrorSet A f
      (K * M * δ) (Real.sqrt (ε * δ))) ≤ (1 / 2 : ℝ) * T.incidentMass R A := by
  dsimp only
  apply T.correctedError_trimmed_mass_le_half hd R A hneighbors hcellD _
    (fun _ hv => (T.finiteNetwork R).boundaryCorrectedError_boundary A hA _ _ hv)
    e he a b hab hheight hK hM hε hδ hδε hwidth hsmall hlength
  exact energy_boundaryCorrected_le_hessian_diam_mass_segment hd T R A hA _ h hM.le
    ((T.finiteNetwork R).dirichletSolution_spec A hA _) hdiam hcellD hneighbors
    hW hh hcellW hHcell hW' hh' hseg hHseg

/-- leobon12's geometric mass decay of the corrected regions, with the Hessian bound on the cells
of the region and on its edge segments. -/
theorem correctedRegions_mass_le_geometric_segment (hd : 1 ≤ d) (T : OrthogonalTiling d)
    (R : Set T.V) [Fintype R] (A : Set R)
    (hA : (T.finiteNetwork R).BoundaryAccessible A)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    (hcellD : ∀ v ∈ A, (T.cell v).carrier ⊆ interior T.domain)
    (h : Euc d → ℝ) (e : Euc d) (he : e ≠ 0) (a b : ℝ) (hab : a ≤ b)
    (hheight : ∀ v ∈ A, ∀ x ∈ (T.cell v).carrier,
      inner ℝ e x / inner ℝ e e ∈ Set.Icc a b)
    {K M ε : ℝ} (hK : 0 < K) (hM : 0 < M) (hε : 0 < ε)
    (hwidth : 12 * ((d : ℝ) * ‖e‖ * (b - a)) ≤ K)
    (hsmall : 144 * M ^ 2 * ε ^ 2 ≤ 1)
    (hlength : ∀ v w : R, T.adj v w → ‖T.pos w - T.pos v‖ ≤ 2 * ε)
    (hdiam : ∀ v ∈ A, Metric.diam (T.cell v).carrier ≤ ε)
    {W : Set (Euc d)} (hW : IsOpen W) (hh : IsHarmonicOn h W)
    (hcellW : ∀ v ∈ A, (T.cell v.val).carrier ⊆ W)
    (hHcell : ∀ v ∈ A, ∀ x ∈ (T.cell v.val).carrier, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M)
    {W' : Set (Euc d)} (hW' : IsOpen W') (hh' : ContDiffOn ℝ 2 h W')
    (hseg : ∀ v ∈ A, ∀ w : R, T.adj v w → segment ℝ (T.pos v) (T.pos w) ⊆ W')
    (hHseg : ∀ v ∈ A, ∀ w : R, T.adj v w → ∀ x ∈ segment ℝ (T.pos v) (T.pos w),
      ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M) :
    ∀ n, T.incidentMass R (T.correctedRegions R A hA h K M ε n).val ≤
      T.incidentMass R A * (1 / 2 : ℝ) ^ n := by
  let S := T.correctedRegions R A hA h K M ε
  have hsub (n : ℕ) : (S n).val ⊆ A := (S n).property
  have hstep (n : ℕ) : T.incidentMass R (S (n + 1)).val ≤
      (1 / 2 : ℝ) * T.incidentMass R (S n).val := by
    by_cases hempty : (S n).val = ∅
    · have hnext : (S (n + 1)).val = ∅ := by
        apply Set.eq_empty_of_forall_notMem
        intro v hv
        have hvold : v ∈ (S n).val :=
          T.correctedRegions_antitone R A hA h K M ε (Nat.le_succ n) hv
        simp only [hempty, Set.mem_empty_iff_false] at hvold
      rw [hnext, hempty, T.incidentMass_empty, mul_zero]
    · let δ := T.toTilingData.regionDiameter R (S n).val
      have hδ : 0 < δ := T.toTilingData.regionDiameter_pos hd R
        (Set.nonempty_iff_ne_empty.mpr hempty)
      have hδε : δ ≤ ε := T.toTilingData.regionDiameter_le R (S n).val hε.le
        (fun v hv => hdiam v (hsub n hv))
      exact boundaryCorrected_trimmed_mass_le_half_segment hd T R (S n).val
        ((T.finiteNetwork R).boundaryAccessible_mono (hsub n) hA)
        (fun v hv => hneighbors v (hsub n hv))
        (fun v hv => hcellD v (hsub n hv)) h e he a b hab
        (fun v hv => hheight v (hsub n hv)) hK hM hε hδ hδε hwidth hsmall hlength
        (fun _ hv => T.toTilingData.cell_diam_le_regionDiameter R (S n).val hv)
        hW hh (fun v hv => hcellW v (hsub n hv)) (fun v hv => hHcell v (hsub n hv))
        hW' hh' (fun v hv => hseg v (hsub n hv)) (fun v hv => hHseg v (hsub n hv))
  intro n
  induction n with
  | zero => simp only [correctedRegions, Nat.rec_zero, pow_zero, mul_one, le_refl]
  | succ n ih =>
    calc
      _ ≤ (1 / 2 : ℝ) * T.incidentMass R (S n).val := hstep n
      _ ≤ (1 / 2 : ℝ) * (T.incidentMass R A * (1 / 2 : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; ring

/-- leobon12's bound of the Dirichlet error by the corrected cost series, given the mass decay,
with the Hessian bound on the edge segments of the region. -/
theorem dirichlet_error_le_hypIIICost_of_mass_decay_segment (hd : 1 ≤ d) (T : OrthogonalTiling d)
    (R : Set T.V) [Fintype R] (A : Set R)
    (hA : (T.finiteNetwork R).BoundaryAccessible A)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    (h : Euc d → ℝ) {K M ε : ℝ} (hK : 0 ≤ K) (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hlength : ∀ v w : R, T.adj v w → ‖T.pos w - T.pos v‖ ≤ 2 * ε)
    (hdiam : ∀ v ∈ A, Metric.diam (T.cell v).carrier ≤ ε)
    {W' : Set (Euc d)} (hW' : IsOpen W') (hh' : ContDiffOn ℝ 2 h W')
    (hseg : ∀ v ∈ A, ∀ w : R, T.adj v w → segment ℝ (T.pos v) (T.pos w) ⊆ W')
    (hHseg : ∀ v ∈ A, ∀ w : R, T.adj v w → ∀ x ∈ segment ℝ (T.pos v) (T.pos w),
      ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M)
    {α : ℝ} (hα : 0 < α) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hreg : ∀ v ∈ A, (T.cell v).diamENN ≤ C * T.incidentScale α v)
    {I : ℝ} (hI : 0 ≤ I)
    (hmass : ∀ n, T.incidentMass R (T.correctedRegions R A hA h K M ε n).val ≤
      I * (1 / 2 : ℝ) ^ n) (v : R) :
    |(T.finiteNetwork R).dirichletSolution A hA (fun v => h (T.pos v)) v - h (T.pos v)| ≤
      hypIIICost K (3 * M) ε
        (fun n => T.toTilingData.regionDiameter R
          (T.correctedRegions R A hA h K M ε n).val) := by
  let N := T.finiteNetwork R
  let S : ℕ → Set R := fun n => (T.correctedRegions R A hA h K M ε n).val
  have hsub (n : ℕ) : S n ⊆ A := (T.correctedRegions R A hA h K M ε n).property
  have hS (n : ℕ) : N.BoundaryAccessible (S n) := N.boundaryAccessible_mono (hsub n) hA
  let δ : ℕ → ℝ := fun n => T.toTilingData.regionDiameter R (S n)
  have hδ (n : ℕ) : 0 ≤ δ n := T.toTilingData.regionDiameter_nonneg R (S n)
  have hmesh (n : ℕ) : δ n ≤ ε := T.toTilingData.regionDiameter_le R (S n) hε
    (fun u hu => hdiam u (hsub n hu))
  have hneigh (n : ℕ) : ∀ u ∈ S n, ∀ w, T.adj u w → w ∈ R :=
    fun u hu => hneighbors u (hsub n hu)
  have hregS (n : ℕ) : ∀ u ∈ S n,
      (T.cell u).diamENN ≤ C * T.incidentScale α u := fun u hu => hreg u (hsub n hu)
  have hgeom := T.regionDiameter_le_geometric_of_mass R S hneigh hα.le hC hregS hI hmass
  obtain ⟨n, hempty⟩ := (T.eventually_empty_of_geometric_mass_hypIII hd R S hneigh
    hα hC hregS hI hmass).exists
  let g : R → ℝ := fun u => h (T.pos u)
  let reward : R → R → ℝ := fun u w => T.surfaceTaylorRemainder h u w
  have hq (i : ℕ) (u : R) (hu : u ∉ S (i + 1)) :
      |N.boundaryCorrectedError (S i) (hS i) g reward u| ≤
        K * M * δ i + Real.sqrt (ε * δ i) := by
    have hδi := hδ i
    apply N.abs_le_outside_trimmedErrorSet (by positivity) (Real.sqrt_nonneg _)
      (fun z hz => N.boundaryCorrectedError_boundary (S i) (hS i) g reward hz)
    exact hu
  have hnew (i : ℕ) (u : R) (hu : u ∈ S i) (w : R) (hw : w ∈ S i)
      (huw : 0 < N.a u w) : |reward u w| ≤ 6 * M * δ i ^ 2 := by
    have ha : T.adj u w := T.conductanceReal_pos_iff.mp huw
    exact surfaceTaylorRemainder_abs_le_segment T h hM
      (T.edge_dist_le_two_diam_bound ha
        (T.toTilingData.cell_diam_le_regionDiameter R (S i) hu)
        (T.toTilingData.cell_diam_le_regionDiameter R (S i) hw)) hW' hh'
      (hseg u (hsub i hu) w ha) (hHseg u (hsub i hu) w ha)
  have hinitial (u : R) (hu : u ∈ S 0) (w : R) (_ : w ∉ S 0)
      (huw : 0 < N.a u w) : |reward u w| ≤ 6 * M * ε ^ 2 := by
    have ha : T.adj u w := T.conductanceReal_pos_iff.mp huw
    have hdist : dist (T.pos u) (T.pos w) ≤ 2 * ε := by
      simpa only [dist_eq_norm, norm_sub_rev] using hlength u w ha
    exact surfaceTaylorRemainder_abs_le_segment T h hM hdist hW' hh'
      (hseg u (hsub 0 hu) w ha) (hHseg u (hsub 0 hu) w ha)
  have hbound := N.boundaryCorrectedIteration_error_bound S hS
    (fun i => T.correctedRegions_antitone R A hA h K M ε (Nat.le_succ i))
    g reward (fun i => K * M * δ i + Real.sqrt (ε * δ i))
    (fun i => 6 * M * δ i ^ 2) (fun i => by positivity) hq hnew
    (by positivity : 0 ≤ 6 * M * ε ^ 2) hinitial n hempty v
  have hcost := finite_corrected_cost_le_hypIIICost δ hK hM hε
    (show 0 ≤ C.toReal * (2 * I) ^ α by positivity)
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) α)
    (Real.rpow_lt_one (by norm_num) (by norm_num) hα) hδ hmesh hgeom n
  exact hbound.trans hcost

/-- leobon12's finite Case III estimate, with the hypotheses of the edge-segment form of Proposition 2.6:
`h` harmonic near the cells of the region, with the Hessian bound on the cells and on the edge
segments. -/
theorem dirichlet_error_le_hypIIICost_segment (hd : 1 ≤ d) (T : OrthogonalTiling d)
    (R : Set T.V) [Fintype R] (A : Set R)
    (hA : (T.finiteNetwork R).BoundaryAccessible A)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    (hcellD : ∀ v ∈ A, (T.cell v).carrier ⊆ interior T.domain)
    (h : Euc d → ℝ) (e : Euc d) (he : e ≠ 0) (a b : ℝ) (hab : a ≤ b)
    (hheight : ∀ v ∈ A, ∀ x ∈ (T.cell v).carrier,
      inner ℝ e x / inner ℝ e e ∈ Set.Icc a b)
    {K M ε : ℝ} (hK : 0 < K) (hM : 0 < M) (hε : 0 < ε)
    (hwidth : 12 * ((d : ℝ) * ‖e‖ * (b - a)) ≤ K)
    (hsmall : 144 * M ^ 2 * ε ^ 2 ≤ 1)
    (hlength : ∀ v w : R, T.adj v w → ‖T.pos w - T.pos v‖ ≤ 2 * ε)
    (hdiam : ∀ v ∈ A, Metric.diam (T.cell v).carrier ≤ ε)
    {W : Set (Euc d)} (hW : IsOpen W) (hh : IsHarmonicOn h W)
    (hcellW : ∀ v ∈ A, (T.cell v.val).carrier ⊆ W)
    (hHcell : ∀ v ∈ A, ∀ x ∈ (T.cell v.val).carrier, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M)
    {W' : Set (Euc d)} (hW' : IsOpen W') (hh' : ContDiffOn ℝ 2 h W')
    (hseg : ∀ v ∈ A, ∀ w : R, T.adj v w → segment ℝ (T.pos v) (T.pos w) ⊆ W')
    (hHseg : ∀ v ∈ A, ∀ w : R, T.adj v w → ∀ x ∈ segment ℝ (T.pos v) (T.pos w),
      ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M)
    {α : ℝ} (hα : 0 < α) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hreg : ∀ v ∈ A, (T.cell v).diamENN ≤ C * T.incidentScale α v)
    {I : ℝ} (hI : 0 ≤ I) (hIbound : T.incidentMass R A ≤ I) (v : R) :
    |(T.finiteNetwork R).dirichletSolution A hA (fun v => h (T.pos v)) v - h (T.pos v)| ≤
      hypIIICost K (3 * M) ε
        (fun n => T.toTilingData.regionDiameter R
          (T.correctedRegions R A hA h K M ε n).val) := by
  apply dirichlet_error_le_hypIIICost_of_mass_decay_segment hd T R A hA hneighbors h
    hK.le hM.le hε.le hlength hdiam hW' hh' hseg hHseg hα hC hreg hI _ v
  intro n
  exact (correctedRegions_mass_le_geometric_segment hd T R A hA hneighbors hcellD h e he a b
    hab hheight hK hM hε hwidth hsmall hlength hdiam hW hh hcellW hHcell hW' hh' hseg hHseg
    n).trans (mul_le_mul_of_nonneg_right hIbound (pow_nonneg (by norm_num) n))

end SpherePackings
