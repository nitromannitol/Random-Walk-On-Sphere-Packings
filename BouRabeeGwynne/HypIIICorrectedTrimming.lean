module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/HypIIICorrectedTrimming.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.BoundaryCorrectedSurfaceEnergy
public import BouRabeeGwynne.BoundaryCorrectedIteration
public import BouRabeeGwynne.Section3MassDecay

@[expose] public section

/-! Actual mass contraction at the current interior diameter scale. -/

open scoped Classical BigOperators

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

/-- The global boundary-edge length remains `2ε`, while both the corrected
energy and threshold use only the shrinking interior diameter `δ`. -/
theorem correctedError_trimmed_mass_le_half (hd : 1 ≤ d)
    (R : Set T.V) [Fintype R] (A : Set R)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    (hcellD : ∀ v ∈ A, (T.cell v).carrier ⊆ interior T.domain)
    (f : R → ℝ) (hzero : ∀ v, v ∉ A → f v = 0)
    (e : Euc d) (he : e ≠ 0) (a b : ℝ) (hab : a ≤ b)
    (hheight : ∀ v ∈ A, ∀ x ∈ (T.cell v).carrier,
      inner ℝ e x / inner ℝ e e ∈ Set.Icc a b)
    {K M ε δ : ℝ} (hK : 0 < K) (hM : 0 < M) (hε : 0 < ε)
    (hδ : 0 < δ) (hδε : δ ≤ ε)
    (hwidth : 12 * ((d : ℝ) * ‖e‖ * (b - a)) ≤ K)
    (hsmall : 144 * M ^ 2 * ε ^ 2 ≤ 1)
    (hlength : ∀ v w : R, T.adj v w → ‖T.pos w - T.pos v‖ ≤ 2 * ε)
    (henergy : (T.finiteNetwork R).energy f ≤
      9 * M ^ 2 * δ ^ 2 * T.incidentMass R A) :
    T.incidentMass R ((T.finiteNetwork R).trimmedErrorSet A f
      (K * M * δ) (Real.sqrt (ε * δ))) ≤ (1 / 2 : ℝ) * T.incidentMass R A := by
  let F := T.finiteAmbientFunction R f
  have hF : (fun v : R => F v) = f := by
    funext v
    exact T.finiteAmbientFunction_apply R f v
  have hzeroF : ∀ v : R, v ∉ A → F v = 0 := by
    intro v hv
    simpa only [F, T.finiteAmbientFunction_apply] using hzero v hv
  have hE : T.incidentEnergy R A F ≤ (3 * M * δ) ^ 2 * T.incidentMass R A := by
    rw [T.incidentEnergy_eq_networkEnergy R A F hzeroF, hF]
    convert henergy using 1 <;> ring
  have htrim := T.incidentMass_trimmed_le_contraction_factor hd R A hneighbors hcellD
    F hzeroF e he a b hab hheight (C := 3 * M * δ) (τ := K * M * δ)
    (L := 2 * ε) (ℓ := Real.sqrt (ε * δ))
    (by positivity) (by positivity) (Real.sqrt_pos.mpr (mul_pos hε hδ)) hlength hE
  rw [hF] at htrim
  have hfactor : (d : ℝ) * ‖e‖ * (b - a) * (3 * M * δ) / (K * M * δ) +
      ((2 * ε) ^ 2 / (Real.sqrt (ε * δ)) ^ 2) * (3 * M * δ) ^ 2 ≤ 1 / 2 := by
    have hid : (d : ℝ) * ‖e‖ * (b - a) * (3 * M * δ) / (K * M * δ) +
        ((2 * ε) ^ 2 / (Real.sqrt (ε * δ)) ^ 2) * (3 * M * δ) ^ 2 =
        3 * ((d : ℝ) * ‖e‖ * (b - a)) / K + 36 * M ^ 2 * ε * δ := by
      rw [Real.sq_sqrt (mul_pos hε hδ).le]
      field_simp [hK.ne', hM.ne', hε.ne', hδ.ne']
      ring
    rw [hid]
    have hfirst : 3 * ((d : ℝ) * ‖e‖ * (b - a)) / K ≤ 1 / 4 :=
      (div_le_iff₀ hK).mpr (by linarith)
    have hsecond : 36 * M ^ 2 * ε * δ ≤ 1 / 4 := by
      have hle := mul_le_mul_of_nonneg_left hδε
        (show 0 ≤ 36 * M ^ 2 * ε by positivity)
      nlinarith
    linarith
  exact htrim.trans (mul_le_mul_of_nonneg_right hfactor (T.incidentMass_nonneg R A))

/-- Specialization to the actual finite corrected harmonic error. The energy
estimate is derived from harmonicity and the cell geometry. -/
theorem boundaryCorrected_trimmed_mass_le_half (hd : 1 ≤ d)
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
    (hball : ∀ v ∈ A, Metric.closedBall (T.pos v) (2 * δ) ⊆ W)
    (hH : ∀ v ∈ A, ∀ x ∈ Metric.closedBall (T.pos v) (2 * δ),
      ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M) :
    let f := (T.finiteNetwork R).boundaryCorrectedError A hA
      (fun v => h (T.pos v)) (fun v w => T.surfaceTaylorRemainder h v w)
    T.incidentMass R ((T.finiteNetwork R).trimmedErrorSet A f
      (K * M * δ) (Real.sqrt (ε * δ))) ≤ (1 / 2 : ℝ) * T.incidentMass R A := by
  dsimp only
  apply T.correctedError_trimmed_mass_le_half hd R A hneighbors hcellD _
    (fun _ hv => (T.finiteNetwork R).boundaryCorrectedError_boundary A hA _ _ hv)
    e he a b hab hheight hK hM hε hδ hδε hwidth hsmall hlength
  exact T.energy_boundaryCorrected_le_hessian_diam_mass hd R A hA _ h hδ.le hM.le
    ((T.finiteNetwork R).dirichletSolution_spec A hA _) hdiam hcellD hneighbors
    hW hh hball hH

end BouRabeeGwynne.OrthogonalTiling
