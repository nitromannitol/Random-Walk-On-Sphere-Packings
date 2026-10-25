module

-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (files `BouRabeeGwynne/FluxResidual.lean` and `BouRabeeGwynne/FacetFlux.lean` at commit cf73d6e):
-- the flux-residual bounds, from the finite Taylor inequalities and the Hessian on the active cell.
public import SpherePackings.Support.Section3.EnergyMinimal
public import SpherePackings.Support.Section3.ComponentLaplacian

@[expose] public section

/-!
# Finite Taylor control (`rw-spheres-corrected.tex`, Correction 8)

**Intermediate results**: the finite Taylor estimates below still ask the cells to lie in the
interior of the ambient set; the registered forms, for complete cells, are in `EnergyComplete.lean`
and `InternalTaylor.lean`.

The corrected paper replaces the Hessian bound along the edge segments by the finite Taylor
inequalities `|h(w) - h(v) - ∇h(v)·(w - v)| ≤ (M/2) ‖w - v‖²` at the active vertices `v` and their
neighbours `w`, together with the Hessian bound `M` on the cells.  `h` is `C²` on an open set
containing the cells, and harmonic on the active cells only.
-/

namespace SpherePackings

open BouRabeeGwynne BouRabeeGwynne.OrthogonalTiling

open scoped MeasureTheory BigOperators Classical Laplacian

variable {d : ℕ}

/-- Taylor's theorem with the sharp constant: a Hessian bound `M` on the segment `[a, b]` gives the
finite Taylor inequality with `M / 2`. -/
theorem taylor_of_segment {W : Set (Euc d)} (hW : IsOpen W) {h : Euc d → ℝ}
    (hh : ContDiffOn ℝ 2 h W) {M : ℝ} {a b : Euc d} (hseg : segment ℝ a b ⊆ W)
    (hH : ∀ x ∈ segment ℝ a b, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M) :
    |h b - h a - (fderiv ℝ h a) (b - a)| ≤ M / 2 * ‖b - a‖ ^ 2 := by
  have hCF : ContDiffOn ℝ 1 (fderiv ℝ h) W := hh.fderiv_of_isOpen hW (by norm_num)
  have hdfh : ∀ x ∈ segment ℝ a b, DifferentiableAt ℝ (fderiv ℝ h) x := fun x hx =>
    (hCF.differentiableOn (by norm_num)).differentiableAt (hW.mem_nhds (hseg hx))
  have hgrad : ∀ x ∈ segment ℝ a b, ‖fderiv ℝ h x - fderiv ℝ h a‖ ≤ M * ‖x - a‖ := fun x hx =>
    Convex.norm_image_sub_le_of_norm_fderiv_le hdfh hH (convex_segment a b)
      (left_mem_segment ℝ a b) hx
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) 1, a + t • (b - a) ∈ segment ℝ a b := fun t ht => by
    rw [segment_eq_image']
    exact ⟨t, ht, rfl⟩
  have hdiff : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasFDerivAt h (fderiv ℝ h (a + t • (b - a))) (a + t • (b - a)) := fun t ht =>
    ((hh.differentiableOn (by norm_num)).differentiableAt
      (hW.mem_nhds (hseg (hpt t ht)))).hasFDerivAt
  -- `φ t = h (a + t (b - a)) - h a - t Dh(a)(b - a)` has derivative `(Dh(a + t (b - a)) - Dh(a))(b - a)`
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt
      (fun s : ℝ => h (a + s • (b - a)) - h a - s * fderiv ℝ h a (b - a))
      ((fderiv ℝ h (a + t • (b - a)) - fderiv ℝ h a) (b - a)) t := fun t ht => by
    have hline : HasDerivAt (fun s : ℝ => a + s • (b - a)) (b - a) t := by
      simpa using ((hasDerivAt_id' t).smul_const (b - a)).const_add a
    have hcomp : HasDerivAt (fun s : ℝ => h (a + s • (b - a)))
        (fderiv ℝ h (a + t • (b - a)) (b - a)) t := (hdiff t ht).comp_hasDerivAt t hline
    have hlin : HasDerivAt (fun s : ℝ => s * fderiv ℝ h a (b - a))
        (fderiv ℝ h a (b - a)) t := by
      simpa using (hasDerivAt_id' t).mul_const (fderiv ℝ h a (b - a))
    rw [sub_apply]
    exact (hcomp.sub_const (h a)).sub hlin
  have hbound : ∀ x ∈ Set.Ico (0 : ℝ) 1,
      ‖(fderiv ℝ h (a + x • (b - a)) - fderiv ℝ h a) (b - a)‖ ≤ M * x * ‖b - a‖ ^ 2 := by
    intro x hx
    have hpa : ‖a + x • (b - a) - a‖ = x * ‖b - a‖ := by
      rw [show a + x • (b - a) - a = x • (b - a) by abel, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hx.1]
    calc ‖(fderiv ℝ h (a + x • (b - a)) - fderiv ℝ h a) (b - a)‖
        ≤ ‖fderiv ℝ h (a + x • (b - a)) - fderiv ℝ h a‖ * ‖b - a‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (M * ‖a + x • (b - a) - a‖) * ‖b - a‖ :=
          mul_le_mul_of_nonneg_right (hgrad _ (hpt x (Set.Ico_subset_Icc_self hx))) (norm_nonneg _)
      _ = M * x * ‖b - a‖ ^ 2 := by rw [hpa]; ring
  have hB : ∀ x : ℝ, HasDerivAt (fun s : ℝ => M / 2 * s ^ 2 * ‖b - a‖ ^ 2)
      (M * x * ‖b - a‖ ^ 2) x := fun x => by
    refine (((hasDerivAt_pow 2 x).const_mul (M / 2)).mul_const (‖b - a‖ ^ 2)).congr_deriv ?_
    rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one, Nat.cast_ofNat]
    ring
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (a := 0) (b := 1)
    (f := fun s : ℝ => h (a + s • (b - a)) - h a - s * fderiv ℝ h a (b - a))
    (f' := fun x : ℝ => (fderiv ℝ h (a + x • (b - a)) - fderiv ℝ h a) (b - a))
    (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hderiv t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (B := fun s : ℝ => M / 2 * s ^ 2 * ‖b - a‖ ^ 2) (B' := fun x : ℝ => M * x * ‖b - a‖ ^ 2)
    (by simp) hB hbound
  have h1 := key (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩)
  simp only [one_smul, add_sub_cancel, one_mul, one_pow, mul_one] at h1
  rw [← Real.norm_eq_abs]
  exact h1

/-- The flux residual of an edge from the finite Taylor inequality at `v` and the Hessian on the
segment from `v` to the facet point `y`. -/
theorem fluxResidual_bound_taylor {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : E → ℝ) {v w y : E} {ε M : ℝ} (hM : 0 ≤ M)
    (hw : dist v w ≤ 2 * ε) (hy : dist v y ≤ ε)
    (htaylor : |h w - h v - (fderiv ℝ h v) (w - v)| ≤ M / 2 * ‖w - v‖ ^ 2)
    (hcell : ∀ x ∈ segment ℝ v y, DifferentiableAt ℝ (fderiv ℝ h) x ∧
      ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M) :
    |h w - h v - (fderiv ℝ h y) (w - v)| ≤ 3 * M * ε * ‖w - v‖ := by
  have hε : 0 ≤ ε := le_trans dist_nonneg hy
  have hvy : ‖fderiv ℝ h v - fderiv ℝ h y‖ ≤ M * ε := by
    have h1 := Convex.norm_image_sub_le_of_norm_fderiv_le (fun x hx => (hcell x hx).1)
      (fun x hx => (hcell x hx).2) (convex_segment v y) (right_mem_segment ℝ v y)
      (left_mem_segment ℝ v y)
    calc ‖fderiv ℝ h v - fderiv ℝ h y‖ ≤ M * ‖v - y‖ := h1
      _ ≤ M * ε := mul_le_mul_of_nonneg_left (by rw [← dist_eq_norm]; exact hy) hM
  have hsplit : h w - h v - (fderiv ℝ h y) (w - v) =
      (h w - h v - (fderiv ℝ h v) (w - v)) + (fderiv ℝ h v - fderiv ℝ h y) (w - v) := by
    rw [sub_apply]
    ring
  have hn : ‖w - v‖ ≤ 2 * ε := by
    rw [← dist_eq_norm, dist_comm]
    exact hw
  have hfirst : |h w - h v - (fderiv ℝ h v) (w - v)| ≤ M * ε * ‖w - v‖ := by
    refine htaylor.trans ?_
    calc M / 2 * ‖w - v‖ ^ 2 = M / 2 * (‖w - v‖ * ‖w - v‖) := by ring
      _ ≤ M / 2 * (‖w - v‖ * (2 * ε)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hn (norm_nonneg _))
            (div_nonneg hM (by norm_num))
      _ = M * ε * ‖w - v‖ := by ring
  have hsecond : |(fderiv ℝ h v - fderiv ℝ h y) (w - v)| ≤ M * ε * ‖w - v‖ := by
    rw [← Real.norm_eq_abs]
    calc ‖(fderiv ℝ h v - fderiv ℝ h y) (w - v)‖
        ≤ ‖fderiv ℝ h v - fderiv ℝ h y‖ * ‖w - v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ M * ε * ‖w - v‖ := mul_le_mul_of_nonneg_right hvy (norm_nonneg _)
  have hnn : 0 ≤ M * ε * ‖w - v‖ := mul_nonneg (mul_nonneg hM hε) (norm_nonneg _)
  rw [hsplit]
  have htri := abs_add_le (h w - h v - (fderiv ℝ h v) (w - v))
    ((fderiv ℝ h v - fderiv ℝ h y) (w - v))
  linarith

/-- Two points of a cell are at most its diameter apart. -/
private lemma dist_le_of_mem_cell_taylor (T : OrthogonalTiling d) {v : T.V} {ε : ℝ}
    (hv : Metric.diam (T.cell v).carrier ≤ ε) {x y : Euc d} (hx : x ∈ (T.cell v).carrier)
    (hy : y ∈ (T.cell v).carrier) : dist x y ≤ ε :=
  (Metric.dist_le_diam_of_mem (T.cell v).compact.isBounded hx hy).trans hv

/-- The single-contact residual, from the finite Taylor inequality at `v` and the Hessian bound on
the cell of `v`. -/
theorem surfaceFlux_residual_bound_taylor (T : OrthogonalTiling d) (h : Euc d → ℝ) {v w : T.V}
    (hvw : T.adj v w) {ε : ℝ}
    (hdv : Metric.diam (T.cell v).carrier ≤ ε) (hdw : Metric.diam (T.cell w).carrier ≤ ε)
    {W : Set (Euc d)} (hW : IsOpen W) (hh : ContDiffOn ℝ 2 h W) (hcell : (T.cell v).carrier ⊆ W)
    {M : ℝ} (hM : 0 ≤ M)
    (htaylor : |h (T.pos w) - h (T.pos v) - (fderiv ℝ h (T.pos v)) (T.pos w - T.pos v)| ≤
      M / 2 * ‖T.pos w - T.pos v‖ ^ 2)
    (hHcell : ∀ x ∈ (T.cell v).carrier, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M) :
    |T.conductanceReal v w * (h (T.pos w) - h (T.pos v)) - T.surfaceFlux h v w| ≤
      3 * M * ε * (T.facetVolume v w).toReal := by
  have hposv : T.pos v ∈ (T.cell v).carrier := interior_subset (T.pos_mem_interior v)
  have hposw : T.pos w ∈ (T.cell w).carrier := interior_subset (T.pos_mem_interior w)
  have hvw2 : dist (T.pos v) (T.pos w) ≤ 2 * ε := by
    obtain ⟨x, hxv, hxw⟩ := hvw.2.1
    calc dist (T.pos v) (T.pos w) ≤ dist (T.pos v) x + dist x (T.pos w) := dist_triangle _ _ _
      _ ≤ ε + ε := add_le_add (dist_le_of_mem_cell_taylor T hdv hposv hxv)
          (dist_le_of_mem_cell_taylor T hdw hxw hposw)
      _ = 2 * ε := (two_mul _).symm
  have hCF : ContDiffOn ℝ 1 (fderiv ℝ h) W := hh.fderiv_of_isOpen hW (by norm_num)
  have hlength : 0 < ‖T.pos w - T.pos v‖ := T.edge_norm_pos hvw
  have hpoint : ∀ y ∈ T.facet v w,
      |(h (T.pos w) - h (T.pos v)) / ‖T.pos w - T.pos v‖ -
        (fderiv ℝ h y) (T.unitEdgeDirection v w)| ≤ 3 * M * ε := by
    intro y hy
    have hsegvy : segment ℝ (T.pos v) y ⊆ (T.cell v).carrier :=
      (T.cell v).convex.segment_subset hposv hy.1
    have hraw := fluxResidual_bound_taylor h hM hvw2 (dist_le_of_mem_cell_taylor T hdv hposv hy.1)
      htaylor (fun x hx => ⟨(hCF.differentiableOn (by norm_num)).differentiableAt
          (hW.mem_nhds (hcell (hsegvy hx))), hHcell x (hsegvy hx)⟩)
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
    (C := 3 * M * ε)
    (T.toTilingData.facetVolume_pos_lt_top hvw).2
    (T.surfaceFlux_integrable h hvw hW hh (fun y hy => hcell hy.1)) hpoint
  change |(T.facetVolume v w).toReal *
      ((h (T.pos w) - h (T.pos v)) / ‖T.pos w - T.pos v‖) - T.surfaceFlux h v w| ≤
    3 * M * ε * (T.facetVolume v w).toReal at hres
  have hconstant : (T.facetVolume v w).toReal *
      ((h (T.pos w) - h (T.pos v)) / ‖T.pos w - T.pos v‖) =
      T.conductanceReal v w * (h (T.pos w) - h (T.pos v)) := by
    rw [T.conductanceReal_of_adj hvw]
    simp only [div_eq_mul_inv]
    ring
  rw [hconstant] at hres
  exact hres

/-- The energy estimate of Proposition 2.6 under the finite Taylor inequalities. -/
theorem energy_error_le_hessian_taylor (hd : 1 ≤ d) (T : OrthogonalTiling d) (R : Set T.V)
    [Fintype R] (A : Set R) (hD : R → ℝ) (h : Euc d → ℝ) {M ε : ℝ} (hM : 0 ≤ M)
    (hsol : (T.finiteNetwork R).SolvesDirichlet A (fun v : R => h (T.pos v)) hD)
    (hcellD : ∀ v ∈ A, (T.cell v.val).carrier ⊆ interior T.domain)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v.val w → w ∈ R)
    {W : Set (Euc d)} (hW : IsOpen W) (hh : ContDiffOn ℝ 2 h W)
    (hcells : ∀ v : R, (T.cell v.val).carrier ⊆ W)
    (hharm : ∀ v ∈ A, ∀ x ∈ (T.cell v.val).carrier, Δ h x = 0)
    (hdiam : ∀ v : R, Metric.diam (T.cell v.val).carrier ≤ ε)
    (hHcell : ∀ v ∈ A, ∀ x ∈ (T.cell v.val).carrier, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M)
    (htaylor : ∀ v ∈ A, ∀ w : R, T.adj v.val w.val →
      |h (T.pos w) - h (T.pos v) - (fderiv ℝ h (T.pos v)) (T.pos w - T.pos v)| ≤
        M / 2 * ‖T.pos w - T.pos v‖ ^ 2) :
    (T.finiteNetwork R).energy (hD - fun v : R => h (T.pos v)) ≤
      9 * M ^ 2 * ε ^ 2 * T.incidentMass R A := by
  have hdiv : ∀ v ∈ A, discreteDiv (fun w u : R => T.supportedSurfaceField h w u) v = 0 := by
    intro v hv
    have hfinite := T.neighbors_finite v.val ((hcellD v hv).trans interior_subset)
    rw [T.finite_div_supportedSurfaceField R h v hfinite (fun w hw => hneighbors v hv w hw)]
    rw [T.sum_surfaceFlux_eq_integral_laplacian hd v.val (hcellD v hv) hfinite hW (hcells v) hh]
    exact MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun x hx => hharm v hv x hx
  have hres : ∀ v w : R, w ∈ A ∨ v ∈ A → T.adj v.val w.val →
      |T.surfaceFlux h v w - T.conductanceReal v w * (h (T.pos w) - h (T.pos v))| ≤
        (3 * M * |ε|) * (T.facetVolume v w).toReal := by
    intro v w hinc hvw
    rcases hinc with hwA | hvA
    · -- `w ∈ A`: the residual at `w`, for the reversed pair, converted by the flux symmetries
      have hrev := surfaceFlux_residual_bound_taylor T h (T.adj_symm hvw)
        ((hdiam w).trans (le_abs_self ε)) ((hdiam v).trans (le_abs_self ε)) hW hh (hcells w) hM
        (htaylor w hwA v (T.adj_symm hvw)) (hHcell w hwA)
      have hc : T.conductanceReal w v = T.conductanceReal v w := T.conductanceReal_symm w v
      have hS : T.surfaceFlux h w v = -T.surfaceFlux h v w := T.surfaceFlux_rev h v w
      have hfv : T.facetVolume w v = T.facetVolume v w := T.facetVolume_symm w v
      rw [hc, hS, hfv] at hrev
      have heq : T.surfaceFlux h v w - T.conductanceReal v w * (h (T.pos w) - h (T.pos v)) =
          T.conductanceReal v w * (h (T.pos v) - h (T.pos w)) - -T.surfaceFlux h v w := by
        ring
      rw [heq]
      exact hrev
    · rw [abs_sub_comm]
      exact surfaceFlux_residual_bound_taylor T h hvw ((hdiam v).trans (le_abs_self ε))
        ((hdiam w).trans (le_abs_self ε)) hW hh (hcells v) hM (htaylor v hvA w hvw) (hHcell v hvA)
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

/-- **Proposition 2.6** under the finite Taylor inequalities (`rw-spheres-corrected.tex`,
Correction 8), with the cells of `V[U]` in the interior of the ambient set. -/
theorem harmonic_energy_bound_taylor (hd : 1 ≤ d) (T : OrthogonalTiling d) (U : Set (Euc d))
    [Fintype (T.closedVertices U)]
    (hcellD : ∀ v ∈ T.interiorVertices U, (T.cell v).carrier ⊆ interior T.domain)
    {W : Set (Euc d)} (hW : IsOpen W) {hC : Euc d → ℝ} (hC2 : ContDiffOn ℝ 2 hC W)
    (hcells : ∀ v ∈ T.closedVertices U, (T.cell v).carrier ⊆ W)
    (hharm : ∀ v ∈ T.interiorVertices U, ∀ x ∈ (T.cell v).carrier, Δ hC x = 0)
    {M ε : ℝ} (hM : 0 ≤ M)
    (hdiam : ∀ v ∈ T.closedVertices U, Metric.diam (T.cell v).carrier ≤ ε)
    (hHcell : ∀ v ∈ T.closedVertices U, ∀ x ∈ (T.cell v).carrier,
      ‖fderiv ℝ (fderiv ℝ hC) x‖ ≤ M)
    (hTaylor : ∀ v ∈ T.interiorVertices U, ∀ w, T.adj v w →
      |hC (T.pos w) - hC (T.pos v) - (fderiv ℝ hC (T.pos v)) (T.pos w - T.pos v)| ≤
        M / 2 * ‖T.pos w - T.pos v‖ ^ 2)
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
  exact energy_error_le_hessian_taylor hd T (T.closedVertices U) (T.finiteInterior U)
    (fun w => hD w) hC hM hsolR (fun v hv => hcellD (v : T.V) hv)
    (fun v hv w hvw => T.neighbor_mem_closedVertices (show (v : T.V) ∈ T.interiorVertices U from hv) hvw)
    hW hC2 (fun v => hcells v v.property) (fun v hv => hharm (v : T.V) hv)
    (fun v => hdiam v v.property) (fun v _ => hHcell v v.property)
    (fun v hv w hvw => hTaylor (v : T.V) hv w hvw)

/-- **Proposition 3.2** under the finite Taylor inequalities, for columns in any direction. -/
theorem harmonic_column_bound_taylor (hd : 1 ≤ d) (T : OrthogonalTiling d) (U : Set (Euc d))
    [Fintype (T.closedVertices U)]
    (hcellD : ∀ v ∈ T.interiorVertices U, (T.cell v).carrier ⊆ interior T.domain)
    {W : Set (Euc d)} (hW : IsOpen W) {hC : Euc d → ℝ} (hC2 : ContDiffOn ℝ 2 hC W)
    (hcells : ∀ v ∈ T.closedVertices U, (T.cell v).carrier ⊆ W)
    (hharm : ∀ v ∈ T.interiorVertices U, ∀ x ∈ (T.cell v).carrier, Δ hC x = 0)
    {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hdiam : ∀ v ∈ T.closedVertices U, Metric.diam (T.cell v).carrier ≤ ε)
    (hHcell : ∀ v ∈ T.closedVertices U, ∀ x ∈ (T.cell v).carrier,
      ‖fderiv ℝ (fderiv ℝ hC) x‖ ≤ M)
    (hTaylor : ∀ v ∈ T.interiorVertices U, ∀ w, T.adj v w →
      |hC (T.pos w) - hC (T.pos v) - (fderiv ℝ hC (T.pos v)) (T.pos w - T.pos v)| ≤
        M / 2 * ‖T.pos w - T.pos v‖ ^ 2)
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
    (harmonic_energy_bound_taylor hd T U hcellD hW hC2 hcells hharm hM hdiam hHcell
      hTaylor hD hsol).trans_eq (by rw [mul_pow, mul_pow, sq_abs]; ring)
  have hsolR := T.solvesDirichlet_restrict hsol
  have key := T.column_poincare_of_energy_bound hd e he (T.closedVertices U) (T.finiteInterior U)
    (fun v hv w hvw => T.neighbor_mem_closedVertices
      (show (v : T.V) ∈ T.interiorVertices U from hv) hvw)
    (fun v hv => hcellD (v : T.V) hv)
    (fun v => hD v - hC (T.pos v)) (fun w hw => sub_eq_zero.mpr (hsolR.2 w hw)) hC0 hk henergy
  have harg : 3 * k * M * |ε| * T.incidentMass (T.closedVertices U) (T.finiteInterior U) =
      k * (3 * M * |ε|) * T.incidentMass (T.closedVertices U) (T.finiteInterior U) := by
    ring
  rw [harg]
  exact key

/-- By Lemma 2.2 on the closed network, `∑ a(u, w) ⟪p, w - u⟫ = 0` at an interior vertex `u`. -/
private lemma sum_inner_eq_zero_taylor (hd : 1 ≤ d) (T : OrthogonalTiling d) (U : Set (Euc d))
    [Fintype (T.closedVertices U)] (u : T.closedVertices U) (hu : u ∈ T.finiteInterior U)
    (hcellD : (T.cell u).carrier ⊆ interior T.domain) (p : Euc d) :
    ∑ w : T.closedVertices U,
      (T.finiteNetwork (T.closedVertices U)).a u w * inner ℝ p (T.pos w - T.pos u) = 0 := by
  have hv := T.neighbors_finite (u : T.V) (hcellD.trans interior_subset)
  have h1 : (T.finiteNetwork (T.closedVertices U)).laplacian
      (fun w => inner ℝ p (T.pos w) + 0) u = 0 := by
    rw [T.closedNetwork_laplacian U (fun x => inner ℝ p (T.pos x) + 0) u hu hv]
    exact discreteLaplacian_affine_eq_zero hd T (u : T.V) hcellD p 0
  simp only [FiniteConductanceNetwork.laplacian, add_zero] at h1
  simp only [inner_sub_right]
  exact h1

/-- By Lemma 2.2 for a continuous linear functional `L`, `∑ a(u, w) L(w - u) = 0` at an interior
vertex `u`. -/
private lemma sum_clm_eq_zero_taylor (hd : 1 ≤ d) (T : OrthogonalTiling d) (U : Set (Euc d))
    [Fintype (T.closedVertices U)] (u : T.closedVertices U) (hu : u ∈ T.finiteInterior U)
    (hcellD : (T.cell u).carrier ⊆ interior T.domain) (L : Euc d →L[ℝ] ℝ) :
    ∑ w : T.closedVertices U,
      (T.finiteNetwork (T.closedVertices U)).a u w * L (T.pos w - T.pos u) = 0 := by
  obtain ⟨p, hp⟩ : ∃ p : Euc d, ∀ x, L x = inner ℝ p x :=
    ⟨(InnerProductSpace.toDual ℝ (Euc d)).symm L, fun x => InnerProductSpace.toDual_symm_apply.symm⟩
  simp only [hp]
  exact sum_inner_eq_zero_taylor hd T U u hu hcellD p

/-- The discrete Laplacian of `h` at an active vertex whose cell lies in the interior of the
ambient set, from the finite Taylor inequalities: `|Δ_a h(u)| ≤ (M/2) ∑ a(u, w) ‖w - u‖²`. -/
theorem abs_laplacian_le_taylor (hd : 1 ≤ d) (T : OrthogonalTiling d) (U : Set (Euc d))
    [Fintype (T.closedVertices U)] (u : T.closedVertices U) (hu : u ∈ T.finiteInterior U)
    (hcellD : (T.cell u).carrier ⊆ interior T.domain) {h : Euc d → ℝ} {M : ℝ}
    (htaylor : ∀ w : T.closedVertices U, T.adj (u : T.V) w →
      |h (T.pos w) - h (T.pos u) - (fderiv ℝ h (T.pos u)) (T.pos w - T.pos u)| ≤
        M / 2 * ‖T.pos w - T.pos u‖ ^ 2) :
    |(T.finiteNetwork (T.closedVertices U)).laplacian (fun w => h (T.pos w)) u| ≤
      M / 2 * ∑ w : T.closedVertices U,
        (T.finiteNetwork (T.closedVertices U)).a u w * ‖T.pos w - T.pos u‖ ^ 2 := by
  simp only [FiniteConductanceNetwork.laplacian]
  have hsplit : ∑ w : T.closedVertices U,
      (T.finiteNetwork (T.closedVertices U)).a u w * (h (T.pos w) - h (T.pos u)) =
      ∑ w : T.closedVertices U, (T.finiteNetwork (T.closedVertices U)).a u w *
        (h (T.pos w) - h (T.pos u) - fderiv ℝ h (T.pos u) (T.pos w - T.pos u)) := by
    have hlin := sum_clm_eq_zero_taylor hd T U u hu hcellD (fderiv ℝ h (T.pos u))
    calc ∑ w : T.closedVertices U, (T.finiteNetwork (T.closedVertices U)).a u w *
          (h (T.pos w) - h (T.pos u))
        = ∑ w : T.closedVertices U, ((T.finiteNetwork (T.closedVertices U)).a u w *
            (h (T.pos w) - h (T.pos u) - fderiv ℝ h (T.pos u) (T.pos w - T.pos u)) +
            (T.finiteNetwork (T.closedVertices U)).a u w *
              fderiv ℝ h (T.pos u) (T.pos w - T.pos u)) :=
          Finset.sum_congr rfl fun w _ => by ring
      _ = ∑ w : T.closedVertices U, (T.finiteNetwork (T.closedVertices U)).a u w *
            (h (T.pos w) - h (T.pos u) - fderiv ℝ h (T.pos u) (T.pos w - T.pos u)) +
          ∑ w : T.closedVertices U, (T.finiteNetwork (T.closedVertices U)).a u w *
            fderiv ℝ h (T.pos u) (T.pos w - T.pos u) := Finset.sum_add_distrib
      _ = ∑ w : T.closedVertices U, (T.finiteNetwork (T.closedVertices U)).a u w *
            (h (T.pos w) - h (T.pos u) - fderiv ℝ h (T.pos u) (T.pos w - T.pos u)) := by
          rw [hlin, add_zero]
  rw [hsplit]
  have hfd : ∀ w : T.closedVertices U, T.adj (u : T.V) w →
      |h (T.pos w) - h (T.pos u) - fderiv ℝ h (T.pos u) (T.pos w - T.pos u)| ≤
        M / 2 * ‖T.pos w - T.pos u‖ ^ 2 :=
    fun w hw => htaylor w hw
  calc |∑ w : T.closedVertices U, (T.finiteNetwork (T.closedVertices U)).a u w *
        (h (T.pos w) - h (T.pos u) - fderiv ℝ h (T.pos u) (T.pos w - T.pos u))|
      ≤ ∑ w : T.closedVertices U, |(T.finiteNetwork (T.closedVertices U)).a u w *
          (h (T.pos w) - h (T.pos u) - fderiv ℝ h (T.pos u) (T.pos w - T.pos u))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ w : T.closedVertices U, (T.finiteNetwork (T.closedVertices U)).a u w *
          (M / 2 * ‖T.pos w - T.pos u‖ ^ 2) := by
        refine Finset.sum_le_sum fun w _ => ?_
        have ha0 := (T.finiteNetwork (T.closedVertices U)).nonneg u w
        by_cases hadj : T.adj (u : T.V) w
        · rw [abs_mul, abs_of_nonneg ha0]
          exact mul_le_mul_of_nonneg_left (hfd w hadj) ha0
        · have hnpos : ¬ 0 < (T.finiteNetwork (T.closedVertices U)).a u w :=
            fun hp => hadj (T.conductanceReal_pos_iff.mp hp)
          have ha : (T.finiteNetwork (T.closedVertices U)).a u w = 0 :=
            le_antisymm (not_lt.mp hnpos) ha0
          rw [ha]
          simp
    _ = M / 2 * ∑ w : T.closedVertices U, (T.finiteNetwork (T.closedVertices U)).a u w *
          ‖T.pos w - T.pos u‖ ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun w _ => by ring

end SpherePackings
