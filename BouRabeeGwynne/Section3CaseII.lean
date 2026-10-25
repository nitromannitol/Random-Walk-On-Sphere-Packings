module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/Section3CaseII.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.Section3MassDecay
public import BouRabeeGwynne.Section3CellMass
public import BouRabeeGwynne.Section3GeometricCutoff
public import BouRabeeGwynne.Section3HarmonicInput

@[expose] public section

/-! Termination and uniform error under the actual tile-volume lower bound. -/

open scoped Classical Topology BigOperators ENNReal

namespace BouRabeeGwynne

/-- One fixed threshold coefficient makes the geometric part contract by a
quarter; the remaining quarter comes from the small mesh energy term. -/
def caseIIThresholdCoefficient (Q C : ℝ) : ℝ := 4 * Q * C + 1

lemma caseIIThresholdCoefficient_pos {Q C : ℝ} (hQ : 0 ≤ Q) (hC : 0 ≤ C) :
    0 < caseIIThresholdCoefficient Q C := by
  have hQC := mul_nonneg hQ hC
  dsimp [caseIIThresholdCoefficient]
  nlinarith

lemma caseII_mesh_scaled_contraction {Q C ε : ℝ} (hQ : 0 ≤ Q)
    (hC : 0 ≤ C) (hε : 0 < ε) (hsmall : C * ε ≤ 1 / 2) :
    Q * (C * ε) / (caseIIThresholdCoefficient Q C * ε) +
      ((2 * ε) ^ 2 / (2 * ε) ^ 2) * (C * ε) ^ 2 ≤ 1 / 2 := by
  have hA := caseIIThresholdCoefficient_pos hQ hC
  have hcancel : Q * (C * ε) / (caseIIThresholdCoefficient Q C * ε) =
      Q * C / caseIIThresholdCoefficient Q C := by
    field_simp [hε.ne', hA.ne']
  have hquarter : Q * C / caseIIThresholdCoefficient Q C ≤ 1 / 4 := by
    apply (div_le_iff₀ hA).mpr
    dsimp [caseIIThresholdCoefficient]
    linarith
  have hnonneg := mul_nonneg hC hε.le
  have hsquare : (C * ε) ^ 2 ≤ 1 / 4 := by nlinarith
  rw [hcancel, div_self (pow_ne_zero 2 (mul_ne_zero (by norm_num) hε.ne')), one_mul]
  linarith

/-- The literal small-tile witness `epsilon_n q_n → 0` controls the number of
actual geometric contraction steps. No extra entropy assumption is required. -/
theorem geometricVolumeCutoff_mul_mesh_tendsto_zero {K : ℝ} (hK : 1 ≤ K)
    (ε q : ℕ → ℝ) (hε0 : ∀ n, 0 ≤ ε n)
    (hq : ∀ᶠ n in Filter.atTop, 0 ≤ q n)
    (hε : Filter.Tendsto ε Filter.atTop (𝓝 0))
    (hεq : Filter.Tendsto (fun n => ε n * q n) Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n => (geometricVolumeCutoff K (q n) : ℝ) * ε n)
      Filter.atTop (𝓝 0) := by
  have hlimit : Filter.Tendsto (fun n => (ε n * q n) / Real.log 2 +
      ε n * (Real.log K / Real.log 2 + 2)) Filter.atTop (𝓝 0) := by
    simpa only [zero_div, zero_mul, add_zero] using
      (hεq.div_const (Real.log 2)).add (hε.mul_const (Real.log K / Real.log 2 + 2))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlimit
  · exact Filter.Eventually.of_forall (fun n => mul_nonneg (Nat.cast_nonneg _) (hε0 n))
  · filter_upwards [hq] with n hn
    exact geometricVolumeCutoff_cost hK hn (hε0 n)

namespace OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

/-- The uniform discrete Dirichlet error follows from the actual tile-volume
lower bound, actual geometric mass contraction, and the upstream energy
estimate for intermediate harmonic replacements. It is not a premise about
an auxiliary error sequence or assumed convergence. -/
theorem dirichlet_error_le_volume_cutoff (hd : 1 ≤ d)
    (R : Set T.V) [Fintype R] (A : Set R)
    (haccess : (T.finiteNetwork R).BoundaryAccessible A)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    (hcellD : ∀ v ∈ A, (T.cell v).carrier ⊆ interior T.domain)
    (g h : R → ℝ) (hsol : (T.finiteNetwork R).SolvesDirichlet A g h)
    (e : Euc d) (he : e ≠ 0) (a b : ℝ) (hab : a ≤ b)
    (hheight : ∀ v ∈ A, ∀ x ∈ (T.cell v).carrier,
      inner ℝ e x / inner ℝ e e ∈ Set.Icc a b)
    {C τ L ℓ K q : ℝ} (hC : 0 ≤ C) (hτ : 0 < τ) (hℓ : 0 < ℓ)
    (hlength : ∀ v w : R, T.adj v w → ‖T.pos w - T.pos v‖ ≤ L)
    (henergy : ∀ S ⊆ A, ∀ h : R → ℝ,
      (T.finiteNetwork R).SolvesDirichlet S g h →
      (T.finiteNetwork R).energy (h - g) ≤ C ^ 2 * T.incidentMass R S)
    (hfactor : (d : ℝ) * ‖e‖ * (b - a) * C / τ + (L ^ 2 / ℓ ^ 2) * C ^ 2 ≤ 1 / 2)
    (hK : 1 ≤ K) (hmass : 2 * T.incidentMass R A ≤ K)
    (hvolume : Real.exp (-q) ≤ T.minTileVolume.toReal) :
    ∀ v, |h v - g v| ≤ (geometricVolumeCutoff K q : ℝ) * (τ + ℓ) := by
  let N := T.finiteNetwork R
  have hdecay := T.harmonicIteration_mass_le_geometric hd R A haccess hneighbors hcellD
    g e he a b hab hheight hC hτ hℓ hlength henergy hfactor
  apply N.harmonicIteration_uniform_error_of_volume_decay A haccess g h hsol hτ.le hℓ.le
    (fun v : R => (T.cell v).volume.toReal) hK
  · intro v _
    exact hvolume.trans (T.minTileVolume_toReal_le_cellVolume v)
  · intro j v hv
    let S := (N.harmonicIteration A haccess g (fun _ => τ) (fun _ => ℓ) j).region
    have hsub : S ⊆ A :=
      N.harmonicIteration_region_antitone A haccess g (fun _ => τ) (fun _ => ℓ)
        (Nat.zero_le j)
    calc
      _ ≤ 2 * T.incidentMass R S := T.cellVolume_le_twice_incidentMass hd R S
        (fun u hu => hneighbors u (hsub hu)) hv (hcellD v (hsub hv))
      _ ≤ 2 * (T.incidentMass R A * (1 / 2 : ℝ) ^ j) :=
        mul_le_mul_of_nonneg_left (hdecay j) (by norm_num)
      _ = (2 * T.incidentMass R A) * (1 / 2 : ℝ) ^ j := by ring
      _ ≤ K * (1 / 2 : ℝ) ^ j := mul_le_mul_of_nonneg_right hmass (by positivity)

/-- The finite Hypothesis II estimate for an actual continuum harmonic
function. The upstream energy estimate is now proved from harmonicity and a
Hessian bound; it is no longer an extra premise in this statement. -/
theorem dirichlet_error_le_volume_cutoff_of_harmonic (hd : 1 ≤ d)
    (R : Set T.V) [Fintype R] (A : Set R)
    (haccess : (T.finiteNetwork R).BoundaryAccessible A)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    (hcellD : ∀ v ∈ A, (T.cell v).carrier ⊆ interior T.domain)
    (hC : Euc d → ℝ) (hD : R → ℝ)
    (hsol : (T.finiteNetwork R).SolvesDirichlet A (fun v => hC (T.pos v)) hD)
    (e : Euc d) (he : e ≠ 0) (a b : ℝ) (hab : a ≤ b)
    (hheight : ∀ v ∈ A, ∀ x ∈ (T.cell v).carrier,
      inner ℝ e x / inner ℝ e e ∈ Set.Icc a b)
    {M τ L ℓ K q : ℝ} (hM : 0 ≤ M) (hτ : 0 < τ) (hℓ : 0 < ℓ)
    (hmesh : T.mesh ≠ ∞)
    (hlength : ∀ v w : R, T.adj v w → ‖T.pos w - T.pos v‖ ≤ L)
    {W : Set (Euc d)} (hW : IsOpen W) (hh : IsHarmonicOn hC W)
    (hball : ∀ v : R, Metric.closedBall (T.pos v) (2 * T.mesh.toReal) ⊆ W)
    (hH : ∀ v : R, ∀ x ∈ Metric.closedBall (T.pos v) (2 * T.mesh.toReal),
      ‖fderiv ℝ (fderiv ℝ hC) x‖ ≤ M)
    (hfactor : (d : ℝ) * ‖e‖ * (b - a) * (3 * M * T.mesh.toReal) / τ +
      (L ^ 2 / ℓ ^ 2) * (3 * M * T.mesh.toReal) ^ 2 ≤ 1 / 2)
    (hK : 1 ≤ K) (hmass : 2 * T.incidentMass R A ≤ K)
    (hvolume : Real.exp (-q) ≤ T.minTileVolume.toReal) :
    ∀ v, |hD v - hC (T.pos v)| ≤ (geometricVolumeCutoff K q : ℝ) * (τ + ℓ) :=
  T.dirichlet_error_le_volume_cutoff hd R A haccess hneighbors hcellD
    (fun v => hC (T.pos v)) hD hsol e he a b hab hheight
    (by positivity) hτ hℓ hlength
    (T.harmonic_error_energy_le_for_subsets hd R A hC hmesh hM hcellD hneighbors
      hW hh hball hH) hfactor hK hmass hvolume

end OrthogonalTiling
end BouRabeeGwynne
