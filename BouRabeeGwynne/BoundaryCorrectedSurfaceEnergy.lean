module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/BoundaryCorrectedSurfaceEnergy.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.CorrectedSurfaceField
public import BouRabeeGwynne.PolytopeGaussGreen
public import BouRabeeGwynne.Section3EnergyNormalization

@[expose] public section

/-!
# Actual corrected geometric energy estimate

The correction is the concrete finite Poisson solution for the actual Taylor
remainder. The flux balance is supplied by Gauss–Green, and the residual bound
uses only the diameters of cells in the current interior. Exterior cell sizes
do not occur in the estimate.
-/

open scoped BigOperators Classical

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

theorem energy_boundaryCorrected_le_hessian_diam_mass
    (hd : 1 ≤ d) (R : Set T.V) [Fintype R] (A : Set R)
    (hA : (T.finiteNetwork R).BoundaryAccessible A)
    (hD : R → ℝ) (h : Euc d → ℝ) {δ M : ℝ} (hδ : 0 ≤ δ) (hM : 0 ≤ M)
    (hsol : (T.finiteNetwork R).SolvesDirichlet A (fun v => h (T.pos v)) hD)
    (hdiam : ∀ v ∈ A, Metric.diam (T.cell v.val).carrier ≤ δ)
    (hcellD : ∀ v ∈ A, (T.cell v.val).carrier ⊆ interior T.domain)
    (hneighbors : ∀ v ∈ A, T.neighbors v.val ⊆ R)
    {W : Set (Euc d)} (hW : IsOpen W) (hh : IsHarmonicOn h W)
    (hball : ∀ v ∈ A, Metric.closedBall (T.pos v) (2 * δ) ⊆ W)
    (hH : ∀ v ∈ A, ∀ x ∈ Metric.closedBall (T.pos v) (2 * δ),
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
    apply T.sum_surfaceFlux_eq_zero_of_harmonic hd v.val (hcellD v hv) hfinite hW _ hh
    intro x hx
    apply hball v hv
    apply Metric.mem_closedBall.mpr
    have hxδ := T.dist_pos_le_diam_bound hx (hdiam v hv)
    rw [dist_comm]
    linarith
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
  have hterm : ∀ v w : R,
      (T.correctedSurfaceField R A h w v) ^ 2 / N.a w v ≤
        (3 * M * δ) ^ 2 * (if (w ∈ A ∨ v ∈ A) ∧ T.adj v.val w.val then
          (T.facetVolume v w).toReal * ‖T.pos w - T.pos v‖ else 0) := by
    intro v w
    by_cases hinc : w ∈ A ∨ v ∈ A
    · by_cases hadj : T.adj v.val w.val
      · rw [if_pos ⟨hinc, hadj⟩]
        change _ / T.conductanceReal w v ≤ _
        rw [T.conductanceReal_symm w v]
        simpa only [mul_assoc] using T.residual_dual_energy_bound hadj
          (show 0 ≤ 3 * M * δ by positivity)
          (T.correctedSurfaceField_bound R A h hδ hM hdiam hW hh.contDiffOn hball hH
            hinc hadj)
      · have hrev : ¬ T.adj w.val v.val := fun ha => hadj (T.adj_symm ha)
        have ha : N.a w v = 0 := by
          change T.conductanceReal w v = 0
          simp only [conductanceReal, if_neg hrev]
        simp only [ha, div_zero, hadj, and_false, ite_false, mul_zero, le_refl]
    · have hv : v ∉ A := fun hv => hinc (Or.inr hv)
      have hw : w ∉ A := fun hw => hinc (Or.inl hw)
      have hz : T.correctedSurfaceField R A h w v = 0 := by
        simp only [correctedSurfaceField, FiniteConductanceNetwork.correctedIncidentFlux,
          FiniteConductanceNetwork.boundaryRewardField, hinc, hv, hw, or_self,
          ite_false, add_zero]
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

end BouRabeeGwynne.OrthogonalTiling
