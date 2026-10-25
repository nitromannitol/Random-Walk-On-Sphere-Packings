module

-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (files `BouRabeeGwynne/FluxResidual.lean` and `BouRabeeGwynne/FacetFlux.lean` at commit cf73d6e):
-- the energy estimate, for complete cells and the finite Taylor inequalities.
public import SpherePackings.Support.Section3.TaylorEnergy
public import SpherePackings.Support.Complete.GaussGreen
public import SpherePackings.Support.Complete.Columns

@[expose] public section

/-!
# Propositions 2.6 and 3.2 as in the corrected paper

`rw-spheres-corrected.tex`, Corrections 4 and 8.  The active cells (those of `V[U]`) are complete;
`h_C` is `C²` on an open set containing the cells of `V̄[U]` and harmonic on the active cells; `M`
bounds its Hessian on the active cells and, for each edge of `E[Ū]`, the finite Taylor remainder at
one active endpoint: `|h(w) - h(v) - ∇h(v)·(w - v)| ≤ (M/2) ‖w - v‖²`.  The published Propositions
2.6 and 3.2, with the Hessian bound on the cells only, are false (`rw-spheres-corrected.tex`,
Correction 8: a slit-domain harmonic function, and a thin reflected Voronoi configuration).
-/

namespace SpherePackings

open BouRabeeGwynne BouRabeeGwynne.OrthogonalTiling

open scoped MeasureTheory BigOperators Classical Laplacian

variable {d : ℕ}

/-- The energy estimate of Proposition 2.6 for complete cells, with the finite Taylor inequality at
one active endpoint of each incident edge. -/
theorem energy_error_le_complete (hd : 1 ≤ d) (T : OrthogonalTiling d) (R : Set T.V)
    [Fintype R] (A : Set R) (hD : R → ℝ) (h : Euc d → ℝ) {M ε : ℝ} (hM : 0 ≤ M)
    (hsol : (T.finiteNetwork R).SolvesDirichlet A (fun v : R => h (T.pos v)) hD)
    (hcomplete : ∀ v ∈ A, CompleteCell T v.val)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v.val w → w ∈ R)
    {W : Set (Euc d)} (hW : IsOpen W) (hh : ContDiffOn ℝ 2 h W)
    (hcells : ∀ v : R, (T.cell v.val).carrier ⊆ W)
    (hharm : ∀ v ∈ A, ∀ x ∈ (T.cell v.val).carrier, Δ h x = 0)
    (hdiam : ∀ v : R, Metric.diam (T.cell v.val).carrier ≤ ε)
    (hHcell : ∀ v ∈ A, ∀ x ∈ (T.cell v.val).carrier, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M)
    (htaylor : ∀ v w : R, T.adj v.val w.val → v ∈ A ∨ w ∈ A →
      (v ∈ A ∧ |h (T.pos w) - h (T.pos v) - (fderiv ℝ h (T.pos v)) (T.pos w - T.pos v)| ≤
        M / 2 * ‖T.pos w - T.pos v‖ ^ 2) ∨
      (w ∈ A ∧ |h (T.pos v) - h (T.pos w) - (fderiv ℝ h (T.pos w)) (T.pos v - T.pos w)| ≤
        M / 2 * ‖T.pos v - T.pos w‖ ^ 2)) :
    (T.finiteNetwork R).energy (hD - fun v : R => h (T.pos v)) ≤
      9 * M ^ 2 * ε ^ 2 * T.incidentMass R A := by
  have hdiv : ∀ v ∈ A, discreteDiv (fun w u : R => T.supportedSurfaceField h w u) v = 0 := by
    intro v hv
    have hfinite := (hcomplete v hv).1
    rw [T.finite_div_supportedSurfaceField R h v hfinite (fun w hw => hneighbors v hv w hw)]
    rw [sum_surfaceFlux_eq_integral_laplacian_of_complete hd T (hcomplete v hv) hW (hcells v) hh]
    exact MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun x hx => hharm v hv x hx
  have hres : ∀ v w : R, w ∈ A ∨ v ∈ A → T.adj v.val w.val →
      |T.surfaceFlux h v w - T.conductanceReal v w * (h (T.pos w) - h (T.pos v))| ≤
        (3 * M * |ε|) * (T.facetVolume v w).toReal := by
    intro v w hinc hvw
    rcases htaylor v w hvw hinc.symm with ⟨hvA, hT⟩ | ⟨hwA, hT⟩
    · rw [abs_sub_comm]
      exact surfaceFlux_residual_bound_taylor T h hvw ((hdiam v).trans (le_abs_self ε))
        ((hdiam w).trans (le_abs_self ε)) hW hh (hcells v) hM hT (hHcell v hvA)
    · have hrev := surfaceFlux_residual_bound_taylor T h (T.adj_symm hvw)
        ((hdiam w).trans (le_abs_self ε)) ((hdiam v).trans (le_abs_self ε)) hW hh (hcells w) hM
        hT (hHcell w hwA)
      have hc : T.conductanceReal w v = T.conductanceReal v w := T.conductanceReal_symm w v
      have hS : T.surfaceFlux h w v = -T.surfaceFlux h v w := T.surfaceFlux_rev h v w
      have hfv : T.facetVolume w v = T.facetVolume v w := T.facetVolume_symm w v
      rw [hc, hS, hfv] at hrev
      have heq : T.surfaceFlux h v w - T.conductanceReal v w * (h (T.pos w) - h (T.pos v)) =
          T.conductanceReal v w * (h (T.pos v) - h (T.pos w)) - -T.surfaceFlux h v w := by
        ring
      rw [heq]
      exact hrev
  have hbound := T.energy_error_le_surfaceFlux_mass R A hD h (C := 3 * M * |ε|)
    (by positivity) hsol hdiv hres
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
  rw [hmass] at hbound
  calc _ ≤ _ := hbound
    _ = 9 * M ^ 2 * ε ^ 2 * T.incidentMass R A := by rw [mul_pow, mul_pow, sq_abs]; ring

/-- **Proposition 2.6** (`prop:energy-bound`), as in the corrected paper. -/
theorem harmonic_energy_bound_complete (hd : 1 ≤ d) (T : OrthogonalTiling d) (U : Set (Euc d))
    [Fintype (T.closedVertices U)]
    (hcomplete : ∀ v ∈ T.interiorVertices U, CompleteCell T v)
    {W : Set (Euc d)} (hW : IsOpen W) {hC : Euc d → ℝ} (hC2 : ContDiffOn ℝ 2 hC W)
    (hcells : ∀ v ∈ T.closedVertices U, (T.cell v).carrier ⊆ W)
    (hharm : ∀ v ∈ T.interiorVertices U, ∀ x ∈ (T.cell v).carrier, Δ hC x = 0)
    {M ε : ℝ} (hM : 0 ≤ M)
    (hdiam : ∀ v ∈ T.closedVertices U, Metric.diam (T.cell v).carrier ≤ ε)
    (hHcell : ∀ v ∈ T.interiorVertices U, ∀ x ∈ (T.cell v).carrier,
      ‖fderiv ℝ (fderiv ℝ hC) x‖ ≤ M)
    (hTaylor : ∀ v w, T.adj v w → v ∈ T.interiorVertices U ∨ w ∈ T.interiorVertices U →
      (v ∈ T.interiorVertices U ∧
        |hC (T.pos w) - hC (T.pos v) - (fderiv ℝ hC (T.pos v)) (T.pos w - T.pos v)| ≤
          M / 2 * ‖T.pos w - T.pos v‖ ^ 2) ∨
      (w ∈ T.interiorVertices U ∧
        |hC (T.pos v) - hC (T.pos w) - (fderiv ℝ hC (T.pos w)) (T.pos v - T.pos w)| ≤
          M / 2 * ‖T.pos v - T.pos w‖ ^ 2))
    (hD : T.V → ℝ) (hsol : T.SolvesDirichlet U (fun v => hC (T.pos v)) hD) :
    T.incidentEnergy (T.closedVertices U) (T.finiteInterior U) (fun v => hD v - hC (T.pos v)) ≤
      9 * M ^ 2 * ε ^ 2 * T.incidentMass (T.closedVertices U) (T.finiteInterior U) := by
  have hsolR := T.solvesDirichlet_restrict hsol
  have hzero : ∀ w : T.closedVertices U, w ∉ T.finiteInterior U →
      (hD - fun w => hC (T.pos w)) w = 0 :=
    fun w hw => sub_eq_zero.mpr (hsolR.2 w hw)
  rw [show (fun v => hD v - hC (T.pos v)) = (hD - fun w => hC (T.pos w)) from rfl,
    T.incidentEnergy_eq_networkEnergy (T.closedVertices U) (T.finiteInterior U)
      (hD - fun w => hC (T.pos w)) hzero]
  exact energy_error_le_complete hd T (T.closedVertices U) (T.finiteInterior U)
    (fun w => hD w) hC hM hsolR (fun v hv => hcomplete (v : T.V) hv)
    (fun v hv w hvw =>
      T.neighbor_mem_closedVertices (show (v : T.V) ∈ T.interiorVertices U from hv) hvw)
    hW hC2 (fun v => hcells v v.property) (fun v hv => hharm v hv)
    (fun v => hdiam v v.property) (fun v hv => hHcell v hv)
    (fun v w hvw hinc => hTaylor v w hvw hinc)

/-- **Proposition 3.2** (`prop:energy-poincare-bound`), as in the corrected paper, for columns in
any direction `e ≠ 0`. -/
theorem harmonic_column_bound_complete (hd : 1 ≤ d) (T : OrthogonalTiling d) (U : Set (Euc d))
    [Fintype (T.closedVertices U)]
    (hcomplete : ∀ v ∈ T.interiorVertices U, CompleteCell T v)
    {W : Set (Euc d)} (hW : IsOpen W) {hC : Euc d → ℝ} (hC2 : ContDiffOn ℝ 2 hC W)
    (hcells : ∀ v ∈ T.closedVertices U, (T.cell v).carrier ⊆ W)
    (hharm : ∀ v ∈ T.interiorVertices U, ∀ x ∈ (T.cell v).carrier, Δ hC x = 0)
    {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hdiam : ∀ v ∈ T.closedVertices U, Metric.diam (T.cell v).carrier ≤ ε)
    (hHcell : ∀ v ∈ T.interiorVertices U, ∀ x ∈ (T.cell v).carrier,
      ‖fderiv ℝ (fderiv ℝ hC) x‖ ≤ M)
    (hTaylor : ∀ v w, T.adj v w → v ∈ T.interiorVertices U ∨ w ∈ T.interiorVertices U →
      (v ∈ T.interiorVertices U ∧
        |hC (T.pos w) - hC (T.pos v) - (fderiv ℝ hC (T.pos v)) (T.pos w - T.pos v)| ≤
          M / 2 * ‖T.pos w - T.pos v‖ ^ 2) ∨
      (w ∈ T.interiorVertices U ∧
        |hC (T.pos v) - hC (T.pos w) - (fderiv ℝ hC (T.pos w)) (T.pos v - T.pos w)| ≤
          M / 2 * ‖T.pos v - T.pos w‖ ^ 2))
    (hD : T.V → ℝ) (hsol : T.SolvesDirichlet U (fun v => hC (T.pos v)) hD)
    (e : Euc d) (he : e ≠ 0) {k : ℝ} (hk : 0 < k) :
    μHE[d - 1] (T.columnBadSet (T.closedVertices U) (T.finiteInterior U) e he
        (fun v => hD v - hC (T.pos v))
        (3 * k * M * ε * T.incidentMass (T.closedVertices U) (T.finiteInterior U))) ≤
      ENNReal.ofReal (1 / k) := by
  rw [← abs_of_nonneg hε]
  have hC0 : 0 ≤ 3 * M * |ε| := by positivity
  have henergy : T.incidentEnergy (T.closedVertices U) (T.finiteInterior U)
      (fun v => hD v - hC (T.pos v)) ≤ (3 * M * |ε|) ^ 2 *
        T.incidentMass (T.closedVertices U) (T.finiteInterior U) :=
    (harmonic_energy_bound_complete hd T U hcomplete hW hC2 hcells hharm hM hdiam hHcell hTaylor
      hD hsol).trans_eq (by rw [mul_pow, mul_pow, sq_abs]; ring)
  have hsolR := T.solvesDirichlet_restrict hsol
  have key := column_poincare_of_energy_bound_of_complete hd T e he (T.closedVertices U)
    (T.finiteInterior U)
    (fun v hv w hvw => T.neighbor_mem_closedVertices
      (show (v : T.V) ∈ T.interiorVertices U from hv) hvw)
    (fun v hv => hcomplete (v : T.V) hv)
    (fun v => hD v - hC (T.pos v)) (fun w hw => sub_eq_zero.mpr (hsolR.2 w hw)) hC0 hk henergy
  have harg : 3 * k * M * |ε| * T.incidentMass (T.closedVertices U) (T.finiteInterior U) =
      k * (3 * M * |ε|) * T.incidentMass (T.closedVertices U) (T.finiteInterior U) := by
    ring
  rw [harg]
  exact key

end SpherePackings
