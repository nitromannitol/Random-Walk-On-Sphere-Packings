-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/Section3HarmonicInput.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.Section3EnergyNormalization
import BouRabeeGwynne.SurfaceEnergyEstimate

/-! The actual harmonic surface-flux estimate in the Section 3 normalization. -/

open scoped Classical BigOperators ENNReal

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

/-- Proposition 2.6 in the exact once-oriented energy/mass normalization used
by the column and contraction arguments. -/
theorem harmonic_error_energy_le_incidentMass
    (hd : 1 ≤ d) (R : Set T.V) [Fintype R] (A : Set R)
    (hD : R → ℝ) (h : Euc d → ℝ) (hmesh : T.mesh ≠ ∞)
    {M : ℝ} (hM : 0 ≤ M)
    (hsol : (T.finiteNetwork R).SolvesDirichlet A (fun v => h (T.pos v)) hD)
    (hcellD : ∀ v ∈ A, (T.cell v).carrier ⊆ interior T.domain)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    {W : Set (Euc d)} (hW : IsOpen W) (hh : IsHarmonicOn h W)
    (hball : ∀ v : R, Metric.closedBall (T.pos v) (2 * T.mesh.toReal) ⊆ W)
    (hH : ∀ v : R, ∀ x ∈ Metric.closedBall (T.pos v) (2 * T.mesh.toReal),
      ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M) :
    (T.finiteNetwork R).energy (hD - fun v : R => h (T.pos v)) ≤
      (3 * M * T.mesh.toReal) ^ 2 * T.incidentMass R A := by
  have hb := T.energy_error_le_hessian_mesh_mass hd R A hD h hmesh hM hsol
    hcellD (fun v hv w hw => hneighbors v hv w hw) hW hh hball hH
  have hmass : ((1 / 2 : ℝ) * ∑ v : R, ∑ w : R,
      if (w ∈ A ∨ v ∈ A) ∧ T.adj v.val w.val then
        (T.facetVolume v w).toReal * ‖T.pos w - T.pos v‖ else 0) =
      T.incidentMass R A := by
    rw [T.incidentMass_eq_half_ordered]
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro w _
    congr 1
    exact propext (by tauto)
  rw [hmass] at hb
  convert hb using 1 <;> ring

/-- The same fixed collar and Hessian control work for every intermediate
region in the genuine harmonic-replacement iteration. -/
theorem harmonic_error_energy_le_for_subsets
    (hd : 1 ≤ d) (R : Set T.V) [Fintype R] (A : Set R)
    (h : Euc d → ℝ) (hmesh : T.mesh ≠ ∞) {M : ℝ} (hM : 0 ≤ M)
    (hcellD : ∀ v ∈ A, (T.cell v).carrier ⊆ interior T.domain)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    {W : Set (Euc d)} (hW : IsOpen W) (hh : IsHarmonicOn h W)
    (hball : ∀ v : R, Metric.closedBall (T.pos v) (2 * T.mesh.toReal) ⊆ W)
    (hH : ∀ v : R, ∀ x ∈ Metric.closedBall (T.pos v) (2 * T.mesh.toReal),
      ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M) :
    ∀ S ⊆ A, ∀ hD : R → ℝ,
      (T.finiteNetwork R).SolvesDirichlet S (fun v => h (T.pos v)) hD →
      (T.finiteNetwork R).energy (hD - fun v : R => h (T.pos v)) ≤
        (3 * M * T.mesh.toReal) ^ 2 * T.incidentMass R S := by
  intro S hSA hD hsol
  exact T.harmonic_error_energy_le_incidentMass hd R S hD h hmesh hM hsol
    (fun v hv => hcellD v (hSA hv))
    (fun v hv => hneighbors v (hSA hv)) hW hh hball hH

end BouRabeeGwynne.OrthogonalTiling
