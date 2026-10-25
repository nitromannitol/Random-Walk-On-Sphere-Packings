module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/SurfaceEnergyEstimate.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.FiniteFluxEnergy
public import BouRabeeGwynne.SupportedSurfaceField
public import BouRabeeGwynne.PolytopeGaussGreen

@[expose] public section

open scoped BigOperators Classical

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

/-- The tiling specialization of the finite variational estimate. The flux
balance and contact residual are explicit intermediate obligations, discharged
by Gauss–Green and the actual Taylor integral estimate in Proposition 2.6. -/
theorem energy_error_le_surfaceFlux_mass (R : Set T.V) [Fintype R]
    (A : Set R) (hD : R → ℝ) (h : Euc d → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hsol : (T.finiteNetwork R).SolvesDirichlet A (fun v : R => h (T.pos v)) hD)
    (hdiv : ∀ v ∈ A, discreteDiv
      (fun w u : R => T.supportedSurfaceField h w u) v = 0)
    (hres : ∀ v w : R, w ∈ A ∨ v ∈ A → T.adj v.val w.val →
      |T.surfaceFlux h v w -
        T.conductanceReal v w * (h (T.pos w) - h (T.pos v))| ≤
        C * (T.facetVolume v w).toReal) :
    (T.finiteNetwork R).energy (hD - fun v : R => h (T.pos v)) ≤
      C ^ 2 * ((1 / 2 : ℝ) * ∑ v : R, ∑ w : R,
        if (w ∈ A ∨ v ∈ A) ∧ T.adj v.val w.val then
          (T.facetVolume v w).toReal * ‖T.pos w - T.pos v‖ else 0) := by
  let N := T.finiteNetwork R
  let Φ : R → R → ℝ := fun w v => T.supportedSurfaceField h w v
  have hbound := N.energy_error_le_incident_flux_residual A hD
    (fun v : R => h (T.pos v)) hsol Φ
    (fun w v => T.supportedSurfaceField_antisymm h w v)
    (fun w v ha => T.supportedSurfaceField_zero_of_conductance_zero h ha) hdiv
  have hterm : ∀ v w : R,
      (if w ∈ A ∨ v ∈ A then
        (Φ w v - N.weightedGradient (fun u : R => h (T.pos u)) w v) ^ 2 / N.a w v
        else 0) ≤
      C ^ 2 * (if (w ∈ A ∨ v ∈ A) ∧ T.adj v.val w.val then
        (T.facetVolume v w).toReal * ‖T.pos w - T.pos v‖ else 0) := by
    intro v w
    by_cases hinc : w ∈ A ∨ v ∈ A
    · by_cases hadj : T.adj v.val w.val
      · simp only [if_pos hinc, if_pos (And.intro hinc hadj)]
        have hg : Φ w v - N.weightedGradient (fun u : R => h (T.pos u)) w v =
            T.surfaceFlux h v w -
              T.conductanceReal v w * (h (T.pos w) - h (T.pos v)) := by
          simp only [Φ, T.supportedSurfaceField_of_adj h hadj,
            FiniteConductanceNetwork.weightedGradient, discreteGrad,
            N, finiteNetwork, T.conductanceReal_symm w v]
        rw [hg]
        change _ / T.conductanceReal w v ≤ _
        rw [T.conductanceReal_symm w v]
        simpa only [mul_assoc] using T.residual_dual_energy_bound hadj hC
          (hres v w hinc hadj)
      · have hwv : ¬ T.adj w.val v.val := fun hwv => hadj (T.adj_symm hwv)
        have ha : N.a w v = 0 := by
          change T.conductanceReal w v = 0
          simp only [conductanceReal, if_neg hwv]
        simp only [ha, div_zero, ite_self, hadj, and_false, if_false, mul_zero, le_refl]
    · simp only [hinc, if_false, false_and, mul_zero, le_refl]
  calc
    _ ≤ _ := hbound
    _ ≤ (1 / 2 : ℝ) * ∑ v : R, ∑ w : R,
        C ^ 2 * (if (w ∈ A ∨ v ∈ A) ∧ T.adj v.val w.val then
          (T.facetVolume v w).toReal * ‖T.pos w - T.pos v‖ else 0) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun w _ => hterm v w
    _ = _ := by simp only [← Finset.mul_sum]; ring

/-- Actual harmonic-flux error estimate used for B(a). The fixed-neighborhood
hypotheses ensure the Taylor estimate throughout the required convex balls.
The energy and mass both count each unoriented incident edge once. -/
theorem energy_error_le_hessian_mesh_mass
    (hd : 1 ≤ d) (R : Set T.V) [Fintype R] (A : Set R)
    (hD : R → ℝ) (h : Euc d → ℝ) (hmesh : T.mesh ≠ ⊤)
    {M : ℝ} (hM : 0 ≤ M)
    (hsol : (T.finiteNetwork R).SolvesDirichlet A (fun v : R => h (T.pos v)) hD)
    (hcellD : ∀ v ∈ A, (T.cell v.val).carrier ⊆ interior T.domain)
    (hneighbors : ∀ v ∈ A, T.neighbors v.val ⊆ R)
    {W : Set (Euc d)} (hW : IsOpen W) (hh : IsHarmonicOn h W)
    (hball : ∀ v : R, Metric.closedBall (T.pos v) (2 * T.mesh.toReal) ⊆ W)
    (hH : ∀ v : R, ∀ x ∈ Metric.closedBall (T.pos v) (2 * T.mesh.toReal),
      ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M) :
    (T.finiteNetwork R).energy (hD - fun v : R => h (T.pos v)) ≤
      9 * M ^ 2 * T.mesh.toReal ^ 2 *
        ((1 / 2 : ℝ) * ∑ v : R, ∑ w : R,
          if (w ∈ A ∨ v ∈ A) ∧ T.adj v.val w.val then
            (T.facetVolume v w).toReal * ‖T.pos w - T.pos v‖ else 0) := by
  have hε : 0 ≤ T.mesh.toReal := ENNReal.toReal_nonneg
  have hdiv : ∀ v ∈ A, discreteDiv
      (fun w u : R => T.supportedSurfaceField h w u) v = 0 := by
    intro v hv
    have hfinite := T.neighbors_finite v.val ((hcellD v hv).trans interior_subset)
    rw [T.finite_div_supportedSurfaceField R h v hfinite (hneighbors v hv)]
    apply T.sum_surfaceFlux_eq_zero_of_harmonic hd v.val (hcellD v hv) hfinite hW _ hh
    intro x hx
    apply hball v
    exact Metric.mem_closedBall.mpr
      ((T.toTilingData.dist_pos_le_mesh hx hmesh).trans (by linarith))
  have hres : ∀ v w : R, w ∈ A ∨ v ∈ A → T.adj v.val w.val →
      |T.surfaceFlux h v w -
        T.conductanceReal v w * (h (T.pos w) - h (T.pos v))| ≤
        (3 * M * T.mesh.toReal) * (T.facetVolume v w).toReal := by
    intro v w _ hvw
    rw [abs_sub_comm]
    exact T.surfaceFlux_residual_bound_on_closedBall h hvw hmesh hW hh.contDiffOn
      (hball v) hM (hH v)
  have hbound := T.energy_error_le_surfaceFlux_mass R A hD h
    (C := 3 * M * T.mesh.toReal) (by positivity) hsol hdiv hres
  convert hbound using 1 <;> ring

/-- The same estimate with the paper's ordered-edge energy normalization.
`dualEnergy (weightedGradient f)` is exactly the displayed sum of inverse
conductance times squared weighted gradients in the definition of D(f,A). -/
theorem ordered_energy_error_le_hessian_mesh_mass
    (hd : 1 ≤ d) (R : Set T.V) [Fintype R] (A : Set R)
    (hD : R → ℝ) (h : Euc d → ℝ) (hmesh : T.mesh ≠ ⊤)
    {M : ℝ} (hM : 0 ≤ M)
    (hsol : (T.finiteNetwork R).SolvesDirichlet A (fun v : R => h (T.pos v)) hD)
    (hcellD : ∀ v ∈ A, (T.cell v.val).carrier ⊆ interior T.domain)
    (hneighbors : ∀ v ∈ A, T.neighbors v.val ⊆ R)
    {W : Set (Euc d)} (hW : IsOpen W) (hh : IsHarmonicOn h W)
    (hball : ∀ v : R, Metric.closedBall (T.pos v) (2 * T.mesh.toReal) ⊆ W)
    (hH : ∀ v : R, ∀ x ∈ Metric.closedBall (T.pos v) (2 * T.mesh.toReal),
      ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M) :
    (T.finiteNetwork R).dualEnergy
      ((T.finiteNetwork R).weightedGradient (hD - fun v : R => h (T.pos v))) ≤
      9 * M ^ 2 * T.mesh.toReal ^ 2 *
        (∑ v : R, ∑ w : R,
          if (w ∈ A ∨ v ∈ A) ∧ T.adj v.val w.val then
            (T.facetVolume v w).toReal * ‖T.pos w - T.pos v‖ else 0) := by
  have hbound := T.energy_error_le_hessian_mesh_mass hd R A hD h hmesh hM hsol
    hcellD hneighbors hW hh hball hH
  have hid := (T.finiteNetwork R).energy_eq_half_dualEnergy_weightedGradient
    (hD - fun v : R => h (T.pos v))
  rw [hid] at hbound
  nlinarith only [hbound]

end BouRabeeGwynne.OrthogonalTiling
