module

-- Built on Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne (commit cf73d6e).
public import SpherePackings.Support.Section3.InternalTaylor
public import SpherePackings.Support.Section3.GeneralRateFull
public import SpherePackings.Support.Complete.Section3
public import BouRabeeGwynne.HypIIICorrectedRegions

@[expose] public section

/-!
# Theorem 3.6 as in the corrected paper

`rw-spheres-corrected.tex`, Theorem 3.6: for `ε < (C M)⁻¹`,
`sup_{V[U]} |h_D - h_C| ≤ C M K ε log(1/ε) + D L`, with `M = M_U°(h_C) ∨ 1`: the Hessian bound `M`
on the cells of `V̄[U]` and the finite Taylor inequality with `M` on the internal edges (both
endpoints in `V[U]`) only.  The cells of `V[U]` are complete; `h_C` is `C²` near the cells and
harmonic on the cells of `V[U]`; `L` bounds its gradient on the cells of `V̄[U]`.

Proof.  leobon12's corrected iteration (`correctedRegions`): each step costs at most
`K' M δ + √(ε δ) + 2 M δ²` (`δ ≤ ε` the largest cell diameter of the region) and halves the incident
mass; the initial boundary correction is at most `2 M ε²` by the cell Hessian alone.  After
`N ≈ C K log(1/ε)` steps every remaining cell has volume below `ε^K`; on a connected component `Q` of
the remaining region the error is bounded by the oscillation `L (D_Q + ε)` and, through the
corrected error of the last region (zero on the boundary of `Q`, with `|Δ| ≤ (M/2) Δ ‖· - v‖²`), by
`(M/2) ρ²`.
-/

namespace SpherePackings

open BouRabeeGwynne BouRabeeGwynne.OrthogonalTiling

open scoped BigOperators Classical MeasureTheory Laplacian

variable {d : ℕ}

/-- `exp (-(K log (1/ε))) = ε ^ K` for `ε > 0`. -/
private lemma exp_neg_mul_log_inv_internal {ε K : ℝ} (hε : 0 < ε) :
    Real.exp (-(K * Real.log (1 / ε))) = ε ^ K := by
  rw [Real.rpow_def_of_pos hε, one_div, Real.log_inv]
  congr 1
  ring

/-- The arithmetic step from the explicit iteration cost to the paper's form. -/
private lemma rate_factor_le_internal {K a b : ℝ} (hK : 1 ≤ K) (ha : 1 ≤ a) (hb : 0 ≤ b) :
    K * a + b + 2 ≤ (3 + b) * (K * a) := by
  have h1 : 1 ≤ K * a := one_le_mul_of_one_le_of_one_le hK ha
  nlinarith

/-- A function with gradient at most `L` on a convex subset of an open set where it is `C²` is
`L`-Lipschitz there. -/
private lemma lipschitz_on_convex_internal {W : Set (Euc d)} (hW : IsOpen W) {h : Euc d → ℝ}
    (hh : ContDiffOn ℝ 2 h W) {P : Set (Euc d)} (hPc : Convex ℝ P) (hPW : P ⊆ W) {L : ℝ}
    (hL : ∀ x ∈ P, ‖fderiv ℝ h x‖ ≤ L) :
    ∀ x ∈ P, ∀ y ∈ P, dist (h x) (h y) ≤ L * dist x y := by
  intro x hx y hy
  have := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hh.differentiableOn (by norm_num)).differentiableAt (hW.mem_nhds (hPW hz)))
    hL hPc hy hx
  rwa [← dist_eq_norm, ← dist_eq_norm] at this

/-- A sum over a duplicate-free list inside a finset is at most the sum over the finset. -/
private lemma list_sum_le_finset_sum_internal {α : Type*} {l : List α} (hl : l.Nodup) {F : Finset α}
    (hlF : ∀ x ∈ l, x ∈ F) {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    (l.map f).sum ≤ ∑ x ∈ F, f x := by
  rw [← List.sum_toFinset f hl]
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => hlF x (List.mem_toFinset.mp hx))
    (fun x _ _ => hf x)

/-- One step of leobon12's corrected iteration halves the incident mass of its region, with the
energy of the boundary-corrected error from the internal Taylor control. -/
private lemma correctedRegionStep_mass_le_half (hd : 1 ≤ d) (T : OrthogonalTiling d)
    (R : Set T.V) [Fintype R] (A : Set R) (hA : (T.finiteNetwork R).BoundaryAccessible A)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    (hcomplete : ∀ v ∈ A, CompleteCell T v)
    (h : Euc d → ℝ) (e : Euc d) (he : e ≠ 0) (a b : ℝ) (hab : a ≤ b)
    (hheight : ∀ v ∈ A, ∀ x ∈ (T.cell v).carrier, inner ℝ e x / inner ℝ e e ∈ Set.Icc a b)
    {K M ε : ℝ} (hK : 0 < K) (hM : 0 < M) (hε : 0 < ε)
    (hwidth : 12 * ((d : ℝ) * ‖e‖ * (b - a)) ≤ K)
    (hsmall : 144 * M ^ 2 * ε ^ 2 ≤ 1)
    (hlength : ∀ v w : R, T.adj v w → ‖T.pos w - T.pos v‖ ≤ 2 * ε)
    (hdiam : ∀ v ∈ A, Metric.diam (T.cell v).carrier ≤ ε)
    {W : Set (Euc d)} (hW : IsOpen W) (hh : ContDiffOn ℝ 2 h W)
    (hcellW : ∀ v ∈ A, (T.cell v.val).carrier ⊆ W)
    (hharm : ∀ v ∈ A, ∀ x ∈ (T.cell v.val).carrier, Δ h x = 0)
    (hHcell : ∀ v ∈ A, ∀ x ∈ (T.cell v.val).carrier, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M)
    (htaylor : ∀ v ∈ A, ∀ w ∈ A, T.adj v.val w.val →
      |T.surfaceTaylorRemainder h v w| ≤ M / 2 * ‖T.pos w - T.pos v‖ ^ 2)
    (S : {S : Set R // S ⊆ A}) :
    T.incidentMass R (T.correctedRegionStep R A hA h K M ε S).val ≤
      (1 / 2 : ℝ) * T.incidentMass R S.val := by
  obtain ⟨S, hS⟩ := S
  have hSacc := (T.finiteNetwork R).boundaryAccessible_mono hS hA
  by_cases hempty : S = ∅
  · have hsub0 : (T.correctedRegionStep R A hA h K M ε ⟨S, hS⟩).val ⊆ S :=
      (T.finiteNetwork R).trimmedErrorSet_subset _ _ _ _
    have hnext : (T.correctedRegionStep R A hA h K M ε ⟨S, hS⟩).val = ∅ :=
      Set.subset_empty_iff.mp (hsub0.trans hempty.subset)
    rw [hnext]
    show T.incidentMass R ∅ ≤ 1 / 2 * T.incidentMass R S
    rw [hempty]
    simp
  · have hδ : 0 < T.toTilingData.regionDiameter R S :=
      T.toTilingData.regionDiameter_pos hd R (Set.nonempty_iff_ne_empty.mpr hempty)
    have hδε : T.toTilingData.regionDiameter R S ≤ ε :=
      T.toTilingData.regionDiameter_le R S hε.le (fun v hv => hdiam v (hS hv))
    have henergy := energy_boundaryCorrected_le_internal hd T R S hSacc
      ((T.finiteNetwork R).dirichletSolution S hSacc (fun v => h (T.pos v))) h hM.le
      ((T.finiteNetwork R).dirichletSolution_spec S hSacc (fun v => h (T.pos v)))
      (fun v hv => T.toTilingData.cell_diam_le_regionDiameter R S hv)
      (fun v hv => hcomplete v (hS hv))
      (fun v hv => hneighbors v (hS hv))
      hW hh (fun v hv => hcellW v (hS hv)) (fun v hv => hharm v (hS hv))
      (fun v hv => hHcell v (hS hv))
      (fun v hv w hw hvw => htaylor v (hS hv) w (hS hw) hvw)
    exact correctedError_trimmed_mass_le_half_of_complete hd T R S
      (fun v hv => hneighbors v (hS hv)) (fun v hv => hcomplete v (hS hv))
      ((T.finiteNetwork R).boundaryCorrectedError S hSacc (fun v => h (T.pos v))
        (fun v w => T.surfaceTaylorRemainder h v w))
      (fun v hv => (T.finiteNetwork R).boundaryCorrectedError_boundary S hSacc _ _ hv)
      e he a b hab (fun v hv => hheight v (hS hv)) hK hM hε hδ hδε hwidth hsmall hlength henergy

/-- The mass of the corrected regions decays geometrically, with the internal Taylor control. -/
private lemma correctedRegions_mass_le_geometric_internal (hd : 1 ≤ d) (T : OrthogonalTiling d)
    (R : Set T.V) [Fintype R] (A : Set R) (hA : (T.finiteNetwork R).BoundaryAccessible A)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    (hcomplete : ∀ v ∈ A, CompleteCell T v)
    (h : Euc d → ℝ) (e : Euc d) (he : e ≠ 0) (a b : ℝ) (hab : a ≤ b)
    (hheight : ∀ v ∈ A, ∀ x ∈ (T.cell v).carrier, inner ℝ e x / inner ℝ e e ∈ Set.Icc a b)
    {K M ε : ℝ} (hK : 0 < K) (hM : 0 < M) (hε : 0 < ε)
    (hwidth : 12 * ((d : ℝ) * ‖e‖ * (b - a)) ≤ K)
    (hsmall : 144 * M ^ 2 * ε ^ 2 ≤ 1)
    (hlength : ∀ v w : R, T.adj v w → ‖T.pos w - T.pos v‖ ≤ 2 * ε)
    (hdiam : ∀ v ∈ A, Metric.diam (T.cell v).carrier ≤ ε)
    {W : Set (Euc d)} (hW : IsOpen W) (hh : ContDiffOn ℝ 2 h W)
    (hcellW : ∀ v ∈ A, (T.cell v.val).carrier ⊆ W)
    (hharm : ∀ v ∈ A, ∀ x ∈ (T.cell v.val).carrier, Δ h x = 0)
    (hHcell : ∀ v ∈ A, ∀ x ∈ (T.cell v.val).carrier, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M)
    (htaylor : ∀ v ∈ A, ∀ w ∈ A, T.adj v.val w.val →
      |T.surfaceTaylorRemainder h v w| ≤ M / 2 * ‖T.pos w - T.pos v‖ ^ 2) :
    ∀ n, T.incidentMass R (T.correctedRegions R A hA h K M ε n).val ≤
      T.incidentMass R A * (1 / 2 : ℝ) ^ n := by
  intro n
  induction n with
  | zero => simp only [correctedRegions, Nat.rec_zero, pow_zero, mul_one, le_refl]
  | succ n ih =>
    calc
      _ ≤ (1 / 2 : ℝ) * T.incidentMass R (T.correctedRegions R A hA h K M ε n).val :=
          correctedRegionStep_mass_le_half hd T R A hA hneighbors hcomplete h e he a b hab hheight
            hK hM hε hwidth hsmall hlength hdiam hW hh hcellW hharm hHcell htaylor
            (T.correctedRegions R A hA h K M ε n)
      _ ≤ (1 / 2 : ℝ) * (T.incidentMass R A * (1 / 2 : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; ring

/-- **Theorem 3.6** (`theorem:generaldim`), as in the corrected paper. -/
theorem generaldim_full_internal (hd : 1 ≤ d) (T : OrthogonalTiling d) (U : Set (Euc d))
    [Fintype (T.closedVertices U)]
    (hcomplete : ∀ v ∈ T.interiorVertices U, CompleteCell T v)
    {R₀ : ℝ} (hR₀ : 0 ≤ R₀) (hUR : ∀ x ∈ U, ‖x‖ ≤ R₀)
    {W : Set (Euc d)} (hW : IsOpen W) {hC : Euc d → ℝ} (hC2 : ContDiffOn ℝ 2 hC W)
    (hcells : ∀ v ∈ T.closedVertices U, (T.cell v).carrier ⊆ W)
    (hharm : ∀ v ∈ T.interiorVertices U, ∀ x ∈ (T.cell v).carrier, Δ hC x = 0)
    {M L ε K Dc : ℝ} (hM : 1 ≤ M) (hK : 1 ≤ K)
    (hdiam : ∀ v ∈ T.closedVertices U, Metric.diam (T.cell v).carrier ≤ ε)
    (hHcell : ∀ v ∈ T.closedVertices U, ∀ x ∈ (T.cell v).carrier,
      ‖fderiv ℝ (fderiv ℝ hC) x‖ ≤ M)
    (hTaylor : ∀ v ∈ T.interiorVertices U, ∀ w ∈ T.interiorVertices U, T.adj v w →
      |hC (T.pos w) - hC (T.pos v) - (fderiv ℝ hC (T.pos v)) (T.pos w - T.pos v)| ≤
        M / 2 * ‖T.pos w - T.pos v‖ ^ 2)
    (hLgrad : ∀ v ∈ T.closedVertices U, ∀ x ∈ (T.cell v).carrier, ‖fderiv ℝ hC x‖ ≤ L)
    (hDc : ∀ Q : Finset T.V,
      (∀ u ∈ Q, u ∈ T.closedVertices U ∧ (T.cell u).volume.toReal < ε ^ K) →
      (∀ a ∈ Q, ∀ b ∈ Q, (adjGraphIn T ↑Q).Reachable a b) →
      ∑ u ∈ Q, Metric.diam (T.cell u).carrier ≤ Dc)
    (hsmall : 12 * M * ε ≤ 1) (hε2 : ε ≤ 1 / 2)
    (hD : T.V → ℝ) (hsol : T.SolvesDirichlet U (fun v => hC (T.pos v)) hD) :
    ∀ v ∈ T.interiorVertices U, |hD v - hC (T.pos v)| ≤
      ((24 * d * (R₀ + 1) + 3) *
          (3 + Real.log (max (2 * d * (μHE[d] (Metric.closedBall (0 : Euc d) (R₀ + 1))).toReal) 1)
            / Real.log 2) / Real.log 2 + (4 * (R₀ + 1 + 1) + 1) / Real.log 2) *
        M * K * ε * Real.log (1 / ε) + Dc * L := by
  intro v hv
  obtain ⟨e, he, hnorm⟩ := exists_unit_euc hd
  set D₀ := R₀ + 1 with hD₀def
  have hD₀ : 0 ≤ D₀ := by linarith
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  let R := T.closedVertices U
  let A : Set R := T.finiteInterior U
  let N := T.finiteNetwork R
  let vR : R := ⟨v, T.interiorVertices_subset_closedVertices U hv⟩
  have hcellR : ∀ w : R, (T.cell w).carrier ⊆ Metric.closedBall (0 : Euc d) D₀ := fun w x hx =>
    mem_closedBall_zero_iff.mpr (cell_norm_le_of_closedVertices T U hUR hε2 hdiam w.property hx)
  have hneighbors : ∀ w : R, w ∈ A → ∀ x, T.adj w x → x ∈ R :=
    fun w hw x hwx => T.neighbor_mem_closedVertices hw hwx
  have hcompleteA : ∀ w ∈ A, CompleteCell T (w : T.V) := fun w hw => hcomplete w.1 hw
  have ha := finiteNetwork_boundaryAccessible_of_complete hd T e he R A hneighbors hcompleteA
  have hdiamR : ∀ w : R, Metric.diam (T.cell (w : T.V)).carrier ≤ ε := fun w =>
    hdiam _ w.property
  have hdistR : ∀ (w : R) {x y : Euc d}, x ∈ (T.cell (w : T.V)).carrier →
      y ∈ (T.cell (w : T.V)).carrier → dist x y ≤ ε := fun w _ _ hx hy =>
    (Metric.dist_le_diam_of_mem (T.cell _).compact.isBounded hx hy).trans (hdiamR w)
  have hposcell : ∀ u : T.V, T.pos u ∈ (T.cell u).carrier :=
    fun u => interior_subset (T.pos_mem_interior u)
  -- `ε > 0`: the cell of `v` has nonempty interior
  have hε : 0 < ε := by
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior (T.pos v) (T.pos_mem_interior v)
    have hy : T.pos v + (r / 2) • e ∈ Metric.ball (T.pos v) r := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hnorm, mul_one,
        Real.norm_eq_abs, abs_of_pos (half_pos hr)]
      linarith
    have hdist := hdistR vR (hposcell v) (interior_subset (hball hy))
    rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, hnorm, mul_one, Real.norm_eq_abs,
      abs_of_pos (half_pos hr)] at hdist
    linarith
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hLgrad v (Or.inl hv) (T.pos v) (hposcell v))
  have hDc0 : 0 ≤ Dc := by
    simpa using hDc ∅ (by simp) (by simp)
  have hsolR := T.solvesDirichlet_restrict hsol
  let g : R → ℝ := fun w => hC (T.pos w)
  let hDR : R → ℝ := fun w => hD w
  have hheight : ∀ w ∈ A, ∀ x ∈ (T.cell (w : T.V)).carrier,
      inner ℝ e x / inner ℝ e e ∈ Set.Icc (-D₀) D₀ := by
    intro w _ x hx
    rw [real_inner_self_eq_norm_sq, hnorm, one_pow, div_one]
    have hinner : |inner ℝ e x| ≤ D₀ := by
      calc
        _ ≤ ‖e‖ * ‖x‖ := abs_real_inner_le_norm _ _
        _ = ‖x‖ := by rw [hnorm, one_mul]
        _ ≤ D₀ := mem_closedBall_zero_iff.mp (hcellR w hx)
    exact abs_le.mp hinner
  have hlength : ∀ a b : R, T.adj a b → ‖T.pos b - T.pos a‖ ≤ 2 * ε := by
    intro a b hab
    obtain ⟨z, hza, hzb⟩ := hab.2.1
    have h := (dist_triangle (T.pos b) z (T.pos a)).trans
      (add_le_add (hdistR b (hposcell b) hzb) (hdistR a hza (hposcell a)))
    rw [dist_eq_norm] at h
    linarith
  have hQfinite : μHE[d] (Metric.closedBall (0 : Euc d) D₀) ≠ ⊤ := by
    have hm : (μHE[d] : MeasureTheory.Measure (Euc d)) = MeasureTheory.volume := by
      simpa using InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := Euc d)
    rw [hm]
    exact (isCompact_closedBall _ _).measure_lt_top.ne
  set K' := max (2 * (d : ℝ) * (μHE[d] (Metric.closedBall (0 : Euc d) D₀)).toReal) 1 with hK'def
  have hK' : 1 ≤ K' := le_max_right _ _
  have hmass : 2 * T.incidentMass R A ≤ K' := by
    calc
      _ ≤ 2 * ((d : ℝ) * (μHE[d] (Metric.closedBall (0 : Euc d) D₀)).toReal) :=
        mul_le_mul_of_nonneg_left (T.incidentMass_le_dim_mul_volume hd R A hQfinite hcellR)
          zero_le_two
      _ ≤ K' := by
        rw [hK'def]
        simpa only [mul_assoc] using
          (le_max_left (2 * (d : ℝ) * (μHE[d] (Metric.closedBall (0 : Euc d) D₀)).toReal) 1)
  set Kw := 12 * ((d : ℝ) * ‖e‖ * (D₀ - -D₀)) + 1 with hKwdef
  have hKw : Kw = 24 * d * D₀ + 1 := by rw [hKwdef, hnorm]; ring
  have hKw1 : 1 ≤ Kw := by
    rw [hKw]
    have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 24) (Nat.cast_nonneg d)) hD₀
    linarith
  have hKw0 : 0 ≤ Kw := zero_le_one.trans hKw1
  have hKwpos : 0 < Kw := zero_lt_one.trans_le hKw1
  have hwidth : 12 * ((d : ℝ) * ‖e‖ * (D₀ - -D₀)) ≤ Kw := by rw [hKwdef]; linarith
  have hsmall' : 144 * M ^ 2 * ε ^ 2 ≤ 1 := by
    have h0 : 0 ≤ 12 * M * ε := mul_nonneg (mul_nonneg (by norm_num) hM0) hε.le
    nlinarith
  have hε2' : 2 * ε ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hM) hε.le]
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hℓ2 : Real.log 2 ≤ Real.log (1 / ε) :=
    Real.log_le_log two_pos (by rw [le_div_iff₀ hε]; linarith)
  have hlogε : 0 ≤ Real.log (1 / ε) := hlog2.le.trans hℓ2
  set q := K * Real.log (1 / ε) with hqdef
  have hq : 0 ≤ q := mul_nonneg (zero_le_one.trans hK) hlogε
  set j := geometricVolumeCutoff K' q with hjdef
  -- the corrected iteration with the cost `Kw`
  let Sr := T.correctedRegions R A ha hC Kw M ε
  have hSacc : ∀ i, N.BoundaryAccessible (Sr i).val := fun i =>
    N.boundaryAccessible_mono (Sr i).property ha
  have htaylorA : ∀ v ∈ A, ∀ w ∈ A, T.adj v.val w.val →
      |T.surfaceTaylorRemainder hC v w| ≤ M / 2 * ‖T.pos w - T.pos v‖ ^ 2 :=
    fun v hv w hw hvw => hTaylor v.1 hv w.1 hw hvw
  have hmassdecay : ∀ n, T.incidentMass R (Sr n).val ≤ T.incidentMass R A * (1 / 2 : ℝ) ^ n :=
    correctedRegions_mass_le_geometric_internal hd T R A ha hneighbors hcompleteA hC e he (-D₀) D₀
      (by linarith) hheight hKwpos hMpos hε hwidth hsmall' hlength (fun w _ => hdiamR w) hW hC2
      (fun w _ => hcells w.1 w.2) (fun w hw => hharm w.1 hw) (fun w _ => hHcell w.1 w.2) htaylorA
  let δ : ℕ → ℝ := fun i => T.toTilingData.regionDiameter R (Sr i).val
  have hδ0 : ∀ i, 0 ≤ δ i := fun i => T.toTilingData.regionDiameter_nonneg R (Sr i).val
  have hδε : ∀ i, δ i ≤ ε := fun i =>
    T.toTilingData.regionDiameter_le R (Sr i).val hε.le (fun w _ => hdiamR w)
  let r : R → R → ℝ := fun u w => T.surfaceTaylorRemainder hC u w
  let f : ℕ → R → ℝ := fun i => N.boundaryCorrectedError (Sr i).val (hSacc i) g r
  let cost : ℕ → ℝ := fun i => Kw * M * δ i + Real.sqrt (ε * δ i) + 2 * M * δ i ^ 2
  have hqstep (i : ℕ) (u : R) (hu : u ∉ (Sr (i + 1)).val) :
      |N.boundaryCorrectedError (Sr i).val (hSacc i) g r u| ≤
        Kw * M * δ i + Real.sqrt (ε * δ i) :=
    N.abs_le_outside_trimmedErrorSet (mul_nonneg (mul_nonneg hKw0 hM0) (hδ0 i))
      (Real.sqrt_nonneg _)
      (fun z hz => N.boundaryCorrectedError_boundary (Sr i).val (hSacc i) g r hz) hu
  have hRstep (i : ℕ) (u : R) (hu : u ∈ (Sr i).val) (w : R) (hw : w ∈ (Sr i).val)
      (huw : 0 < N.a u w) : |r u w| ≤ 2 * M * δ i ^ 2 := by
    have hadj : T.adj u w := T.conductanceReal_pos_iff.mp huw
    have hdist := T.edge_dist_le_two_diam_bound hadj
      (T.toTilingData.cell_diam_le_regionDiameter R (Sr i).val hu)
      (T.toTilingData.cell_diam_le_regionDiameter R (Sr i).val hw)
    have hnorm2 : ‖T.pos w - T.pos u‖ ≤ 2 * δ i := by
      rw [← dist_eq_norm, dist_comm]; exact hdist
    calc |r u w| ≤ M / 2 * ‖T.pos w - T.pos u‖ ^ 2 :=
          htaylorA u ((Sr i).property hu) w ((Sr i).property hw) hadj
      _ ≤ M / 2 * (2 * δ i) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm2 2) (by linarith)
      _ = 2 * M * δ i ^ 2 := by ring
  have hstep (i : ℕ) (x : R) : |f i x - f (i + 1) x| ≤ cost i :=
    N.boundaryCorrectedError_step_bound (A := (Sr i).val) (B := (Sr (i + 1)).val)
      (T.correctedRegions_antitone R A ha hC Kw M ε (Nat.le_succ i)) (hSacc i) (hSacc (i + 1))
      g r (mul_nonneg (mul_nonneg (by norm_num) hM0) (sq_nonneg (δ i))) (hqstep i) (hRstep i) x
  have htele (n : ℕ) (x : R) : |f 0 x - f n x| ≤ ∑ i ∈ Finset.range n, cost i := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc |f 0 x - f (n + 1) x| ≤ |f 0 x - f n x| + |f n x - f (n + 1) x| := abs_sub_le _ _ _
        _ ≤ (∑ i ∈ Finset.range n, cost i) + cost n := add_le_add ih (hstep n x)
        _ = ∑ i ∈ Finset.range (n + 1), cost i := (Finset.sum_range_succ _ _).symm
  have hcost (i : ℕ) : cost i ≤ (24 * d * D₀ + 3) * M * ε := by
    show Kw * M * δ i + Real.sqrt (ε * δ i) + 2 * M * δ i ^ 2 ≤ _
    have h1 : Kw * M * δ i ≤ Kw * M * ε :=
      mul_le_mul_of_nonneg_left (hδε i) (mul_nonneg hKw0 hM0)
    have h2 : Real.sqrt (ε * δ i) ≤ ε := by
      have hεδ : ε * δ i ≤ ε ^ 2 := by
        rw [sq]; exact mul_le_mul_of_nonneg_left (hδε i) hε.le
      calc Real.sqrt (ε * δ i) ≤ Real.sqrt (ε ^ 2) := Real.sqrt_le_sqrt hεδ
        _ = ε := Real.sqrt_sq hε.le
    have h3 : ε ≤ M * ε := le_mul_of_one_le_left hε.le hM
    have h4 : 2 * M * δ i ^ 2 ≤ M * ε := by
      have hδ2 : δ i ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (hδ0 i) (hδε i) 2
      have h5 : 2 * M * δ i ^ 2 ≤ 2 * M * ε ^ 2 :=
        mul_le_mul_of_nonneg_left hδ2 (mul_nonneg zero_le_two hM0)
      nlinarith [mul_nonneg (mul_nonneg hM0 hε.le) (sub_nonneg.mpr hε2')]
    have h6 : Kw * M * ε + M * ε + M * ε = (24 * d * D₀ + 3) * M * ε := by
      rw [hKw]; ring
    linarith
  have hsum : ∑ i ∈ Finset.range j, cost i ≤ (j : ℝ) * ((24 * d * D₀ + 3) * M * ε) := by
    calc ∑ i ∈ Finset.range j, cost i ≤ ∑ _i ∈ Finset.range j, (24 * d * D₀ + 3) * M * ε :=
          Finset.sum_le_sum fun i _ => hcost i
      _ = (j : ℝ) * ((24 * d * D₀ + 3) * M * ε) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  set η := M * ε + (j : ℝ) * ((24 * d * D₀ + 3) * M * ε) with hηdef
  -- the region `S` of the iteration after `j` steps, and its small cells
  let S : Set R := (Sr j).val
  have hSA' : S ⊆ A := (Sr j).property
  have hcompleteS : ∀ w ∈ S, CompleteCell T (w : T.V) := fun w hw => hcompleteA w (hSA' hw)
  have htaylorS : ∀ v ∈ S, ∀ w ∈ S, T.adj v.val w.val →
      |T.surfaceTaylorRemainder hC v w| ≤ M / 2 * ‖T.pos w - T.pos v‖ ^ 2 :=
    fun v hv w hw hvw => htaylorA v (hSA' hv) w (hSA' hw) hvw
  have hSsmall : ∀ u ∈ S, (T.cell (u : T.V)).volume.toReal < ε ^ K := by
    intro u hu
    calc (T.cell (u : T.V)).volume.toReal ≤ 2 * T.incidentMass R S :=
          cellVolume_le_twice_incidentMass_of_complete hd T R S
            (fun w hw => hneighbors w (hSA' hw)) hu (hcompleteA u (hSA' hu))
      _ ≤ 2 * (T.incidentMass R A * (1 / 2 : ℝ) ^ j) :=
          mul_le_mul_of_nonneg_left (hmassdecay j) (by norm_num)
      _ = (2 * T.incidentMass R A) * (1 / 2 : ℝ) ^ j := by ring
      _ ≤ K' * (1 / 2 : ℝ) ^ j := mul_le_mul_of_nonneg_right hmass (by positivity)
      _ < Real.exp (-q) := geometric_mass_lt_exp_neg hK'
      _ = ε ^ K := exp_neg_mul_log_inv_internal hε
  -- the error splits into the boundary correction and the corrected error `f 0`
  have heq : hDR = N.dirichletSolution A ha g :=
    N.dirichlet_unique A ha hsolR (N.dirichletSolution_spec A ha g)
  have hsplit (x : R) : hDR x - g x = N.boundaryCorrection A ha r x + f 0 x := by
    have hx : hDR x = N.dirichletSolution A ha g x := congrFun heq x
    show hDR x - g x = N.boundaryCorrection A ha r x + N.boundaryCorrectedError A ha g r x
    rw [hx]
    simp only [FiniteConductanceNetwork.boundaryCorrectedError, Pi.sub_apply]
    ring
  have hb (x : R) : |N.boundaryCorrection A ha r x| ≤ M * ε := by
    have h2 : 2 * M * ε ^ 2 ≤ M * ε := by
      nlinarith [mul_nonneg (mul_nonneg hM0 hε.le) (sub_nonneg.mpr hε2')]
    exact (boundaryCorrection_abs_le_cells T R A ha hC hW hC2 (fun w => hcells w.1 w.2) hM0
      (fun w => hdiamR w) (fun w => hHcell w.1 w.2) x).trans h2
  have hout : ∀ w : R, w ∉ S → |hDR w - g w| ≤ η := by
    intro w hw
    have h0 : f j w = 0 := N.boundaryCorrectedError_boundary (Sr j).val (hSacc j) g r hw
    have h1 := htele j w
    rw [h0, sub_zero] at h1
    rw [hsplit w]
    calc |N.boundaryCorrection A ha r w + f 0 w| ≤
          |N.boundaryCorrection A ha r w| + |f 0 w| := abs_add_le _ _
      _ ≤ M * ε + ∑ i ∈ Finset.range j, cost i := add_le_add (hb w) h1
      _ ≤ η := by rw [hηdef]; linarith [hsum]
  -- the constant of the iteration
  set C₀ := (24 * d * D₀ + 3) * (3 + Real.log K' / Real.log 2) / Real.log 2 with hC₀def
  have hjP : (j : ℝ) * ((24 * d * D₀ + 3) * M * ε) ≤ C₀ * M * K * ε * Real.log (1 / ε) := by
    have hj : (j : ℝ) ≤ (q + Real.log K') / Real.log 2 + 2 :=
      (geometricVolumeCutoff_lt hK' hq).le
    have ha1 : 1 ≤ Real.log (1 / ε) / Real.log 2 := (one_le_div hlog2).mpr hℓ2
    have hb' : 0 ≤ Real.log K' / Real.log 2 := div_nonneg (Real.log_nonneg hK') hlog2.le
    have hfac := rate_factor_le_internal hK ha1 hb'
    have hB : (q + Real.log K') / Real.log 2 + 2 ≤
        (3 + Real.log K' / Real.log 2) * (K * (Real.log (1 / ε) / Real.log 2)) := by
      rw [hqdef]
      calc _ = K * (Real.log (1 / ε) / Real.log 2) + Real.log K' / Real.log 2 + 2 := by ring
        _ ≤ _ := hfac
    have hA0 : 0 ≤ (24 * d * D₀ + 3) * M := by
      have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 24) (Nat.cast_nonneg d)) hD₀
      exact mul_nonneg (by linarith) hM0
    calc (j : ℝ) * ((24 * d * D₀ + 3) * M * ε)
        = (24 * d * D₀ + 3) * M * ((j : ℝ) * ε) := by ring
      _ ≤ (24 * d * D₀ + 3) * M *
          (((3 + Real.log K' / Real.log 2) * (K * (Real.log (1 / ε) / Real.log 2))) * ε) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hj.trans hB) hε.le) hA0
      _ = C₀ * M * K * ε * Real.log (1 / ε) := by
          rw [hC₀def]; field_simp
  have hMP : M * ε ≤ 1 / Real.log 2 * (M * K * ε * Real.log (1 / ε)) := by
    have h1 : 1 ≤ Real.log (1 / ε) / Real.log 2 := (one_le_div hlog2).mpr hℓ2
    have h2 : 1 ≤ K * (Real.log (1 / ε) / Real.log 2) := one_le_mul_of_one_le_of_one_le hK h1
    calc M * ε = M * ε * 1 := (mul_one _).symm
      _ ≤ M * ε * (K * (Real.log (1 / ε) / Real.log 2)) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hM0 hε.le)
      _ = 1 / Real.log 2 * (M * K * ε * Real.log (1 / ε)) := by ring
  have hηP : η ≤ (C₀ + 1 / Real.log 2) * (M * K * ε * Real.log (1 / ε)) := by
    calc η = M * ε + (j : ℝ) * ((24 * d * D₀ + 3) * M * ε) := hηdef
      _ ≤ 1 / Real.log 2 * (M * K * ε * Real.log (1 / ε)) + C₀ * M * K * ε * Real.log (1 / ε) :=
          add_le_add hMP hjP
      _ = (C₀ + 1 / Real.log 2) * (M * K * ε * Real.log (1 / ε)) := by ring
  have hC1 : 0 ≤ 4 * (D₀ + 1) / Real.log 2 := div_nonneg (by linarith) hlog2.le
  have hnn : 0 ≤ Dc * L + 4 * (D₀ + 1) / Real.log 2 * M * K * ε * Real.log (1 / ε) :=
    add_nonneg (mul_nonneg hDc0 hL0)
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC1 hM0) (zero_le_one.trans hK)) hε.le)
        hlogε)
  have hid : (C₀ + (4 * (D₀ + 1) + 1) / Real.log 2) * M * K * ε * Real.log (1 / ε) =
      (C₀ + 1 / Real.log 2) * (M * K * ε * Real.log (1 / ε)) +
        4 * (D₀ + 1) / Real.log 2 * M * K * ε * Real.log (1 / ε) := by ring
  -- the error at `vR`, by the oscillation and the quadratic bound on its component
  have hkey : |hDR vR - g vR| ≤
      η + (Dc * L + 4 * (D₀ + 1) / Real.log 2 * M * K * ε * Real.log (1 / ε)) := by
    by_cases hvS : vR ∈ S
    swap
    · linarith [hout vR hvS, hnn]
    -- the component of `v` in the remaining region
    let S' : Set T.V := Subtype.val '' S
    let G := adjGraphIn T S'
    let Q' : Set T.V := {u | G.Reachable v u}
    let Q : Set R := {u | (u : T.V) ∈ Q'}
    have hvS' : v ∈ S' := ⟨vR, hvS, rfl⟩
    have hQ'S' : Q' ⊆ S' := by
      intro u hu
      have hrt := (SimpleGraph.reachable_iff_reflTransGen v u).mp hu
      induction hrt with
      | refl => exact hvS'
      | tail _ hbc _ => exact hbc.2.1
    have hQS : Q ⊆ S := by
      intro u hu
      obtain ⟨u', hu'S, hu'eq⟩ := hQ'S' hu
      have : u' = u := Subtype.ext hu'eq
      rw [← this]
      exact hu'S
    have hQA : Q ⊆ A := hQS.trans hSA'
    have hvQ : vR ∈ Q := SimpleGraph.Reachable.refl v
    have hQacc : N.BoundaryAccessible Q := N.boundaryAccessible_mono hQA ha
    have hext : ∀ w ∈ N.externalBoundary Q, w ∉ S ∧ ∃ u ∈ Q, T.adj (u : T.V) w := by
      rintro w ⟨hwQ, u, huQ, hauw⟩
      have hadj : T.adj (u : T.V) w := T.conductanceReal_pos_iff.mp hauw
      refine ⟨fun hwS => hwQ ?_, u, huQ, hadj⟩
      exact (show G.Reachable v u from huQ).trans
        (SimpleGraph.Adj.reachable ⟨hQ'S' huQ, ⟨w, hwS, rfl⟩, hadj⟩)
    have hQ'R : Q' ⊆ T.closedVertices U := fun u hu => by
      obtain ⟨u', -, rfl⟩ := hQ'S' hu
      exact u'.property
    have hQ'fin : Q'.Finite := (Set.toFinite (T.closedVertices U)).subset hQ'R
    set F := hQ'fin.toFinset with hFdef
    set Dq := ∑ u ∈ F, Metric.diam (T.cell u).carrier with hDqdef
    have hDq0 : 0 ≤ Dq := Finset.sum_nonneg fun _ _ => Metric.diam_nonneg
    -- the component is connected and small
    have hreachQ' : ∀ a ∈ Q', (adjGraphIn T Q').Reachable v a := by
      intro a ha'
      have hrt := (SimpleGraph.reachable_iff_reflTransGen v a).mp ha'
      induction hrt with
      | refl => exact SimpleGraph.Reachable.refl v
      | @tail b c hvb hbc ih =>
        have hb : b ∈ Q' := (SimpleGraph.reachable_iff_reflTransGen v b).mpr hvb
        exact (ih hb).trans (SimpleGraph.Adj.reachable ⟨hb, ha', hbc.2.2⟩)
    have hDq : Dq ≤ Dc := by
      apply hDc F
      · intro u hu
        have huQ' : u ∈ Q' := hQ'fin.mem_toFinset.mp hu
        refine ⟨hQ'R huQ', ?_⟩
        obtain ⟨u', hu'S, rfl⟩ := hQ'S' huQ'
        exact hSsmall u' hu'S
      · intro a ha' b hb'
        rw [hFdef, Set.Finite.coe_toFinset]
        have ha'' : a ∈ Q' := hQ'fin.mem_toFinset.mp ha'
        have hb'' : b ∈ Q' := hQ'fin.mem_toFinset.mp hb'
        exact (hreachQ' a ha'').symm.trans (hreachQ' b hb'')
    -- the distance and the oscillation to an exit vertex
    have hchain : ∀ w ∈ N.externalBoundary Q,
        dist (T.pos w) (T.pos v) ≤ Dq + ε ∧
          dist (hC (T.pos w)) (hC (T.pos v)) ≤ L * (Dq + ε) := by
      intro w hw
      obtain ⟨-, u, huQ, hadj⟩ := hext w hw
      obtain ⟨p⟩ := (show G.Reachable v u from huQ)
      let p' := p.toPath
      have hsupp : ∀ x ∈ (p' : G.Walk v (u : T.V)).support, x ∈ Q' := fun x hx =>
        ⟨(p' : G.Walk v (u : T.V)).takeUntil x hx⟩
      have hsum : ((p' : G.Walk v (u : T.V)).support.map
          fun x => Metric.diam (T.cell x).carrier).sum ≤ Dq :=
        list_sum_le_finset_sum_internal p'.property.support_nodup
          (fun x hx => hQ'fin.mem_toFinset.mpr (hsupp x hx)) (fun _ => Metric.diam_nonneg)
      obtain ⟨z, hzu, hzw⟩ := hadj.2.1
      have hzw' : dist z (T.pos w) ≤ ε := hdistR w hzw (hposcell w)
      have hcellQ' : ∀ x ∈ (p' : G.Walk v (u : T.V)).support, x ∈ T.closedVertices U :=
        fun x hx => hQ'R (hsupp x hx)
      constructor
      · have h1 := chain_dist_le T (fun x => x) zero_le_one (p' : G.Walk v (u : T.V))
          (fun x _ y _ z _ => by simp) (T.pos v) (hposcell v) z hzu
        have h1' : dist (T.pos v) z ≤ Dq := h1.trans (by linarith)
        calc dist (T.pos w) (T.pos v) ≤ dist (T.pos w) z + dist z (T.pos v) := dist_triangle _ _ _
          _ ≤ ε + Dq := add_le_add (by rw [dist_comm]; exact hzw') (by rw [dist_comm]; exact h1')
          _ = Dq + ε := add_comm _ _
      · have hlip : ∀ x ∈ T.closedVertices U, ∀ a ∈ (T.cell x).carrier, ∀ b ∈ (T.cell x).carrier,
            dist (hC a) (hC b) ≤ L * dist a b := fun x hx =>
          lipschitz_on_convex_internal hW hC2 (T.cell x).convex (hcells x hx) (hLgrad x hx)
        have h1 := chain_dist_le T hC hL0 (p' : G.Walk v (u : T.V))
          (fun x hx => hlip x (hcellQ' x hx)) (T.pos v) (hposcell v) z hzu
        have h2 := hlip w w.property z hzw (T.pos w) (hposcell w)
        calc dist (hC (T.pos w)) (hC (T.pos v))
            ≤ dist (hC (T.pos w)) (hC z) + dist (hC z) (hC (T.pos v)) := dist_triangle _ _ _
          _ ≤ L * ε + L * Dq := by
            gcongr
            · rw [dist_comm]
              exact h2.trans (mul_le_mul_of_nonneg_left hzw' hL0)
            · rw [dist_comm]
              exact h1.trans (mul_le_mul_of_nonneg_left hsum hL0)
          _ = L * (Dq + ε) := by ring
    -- the path bound
    have hpath : |hDR vR - g vR| ≤ η + L * (Dq + ε) :=
      N.harmonic_error_le_boundary_error_add_oscillation Q hQacc hDR g
        (fun u hu => hsolR.1 u (hQA hu)) (fun w hw => hout w (hext w hw).1) hvQ
        (fun w hw => by rw [← Real.dist_eq]; exact (hchain w hw).2)
    -- the quadratic bound
    set ρ := min (Dq + ε) (2 * D₀) with hρdef
    have hρ0 : 0 ≤ ρ := le_min (by linarith) (by linarith)
    have hρw : ∀ w ∈ N.externalBoundary Q, ‖T.pos w - T.pos v‖ ≤ ρ := by
      intro w hw
      refine le_min (by rw [← dist_eq_norm]; exact (hchain w hw).1) ?_
      have h1 : ‖T.pos (w : T.V)‖ ≤ D₀ := mem_closedBall_zero_iff.mp (hcellR w (hposcell w))
      have h2 : ‖T.pos v‖ ≤ D₀ := mem_closedBall_zero_iff.mp (hcellR vR (hposcell v))
      calc ‖T.pos w - T.pos v‖ ≤ ‖T.pos (w : T.V)‖ + ‖T.pos v‖ := norm_sub_le _ _
        _ ≤ 2 * D₀ := by linarith
    have hsq : ∀ u ∈ Q, N.laplacian (fun w : R => ‖T.pos w - T.pos v‖ ^ 2) u =
        ∑ w : R, N.a u w * ‖T.pos w - T.pos u‖ ^ 2 := fun u hu =>
      laplacian_sq_dist_of_complete hd T U u (hQA hu) (hcompleteA u (hQA hu)) (T.pos v)
    have hlapf : ∀ u ∈ Q, |N.laplacian (f j) u| ≤
        M / 2 * N.laplacian (fun w : R => ‖T.pos w - T.pos v‖ ^ 2) u := by
      intro u hu
      rw [hsq u hu]
      exact abs_laplacian_boundaryCorrected_le hd T U S hSA' (hSacc j)
        (N.dirichletSolution S (hSacc j) g) hC (N.dirichletSolution_spec S (hSacc j) g)
        hcompleteS hM0 htaylorS (hQS hu)
    have hbdry : ∀ w ∈ N.externalBoundary Q,
        |f j w| + M / 2 * (fun w : R => ‖T.pos w - T.pos v‖ ^ 2) w ≤ M / 2 * ρ ^ 2 := by
      intro w hw
      have h0 : f j w = 0 :=
        N.boundaryCorrectedError_boundary (Sr j).val (hSacc j) g r (hext w hw).1
      rw [h0, abs_zero, zero_add]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hρw w hw) 2)
        (by linarith)
    have hfj : |f j vR| ≤ M / 2 * ρ ^ 2 :=
      abs_le_of_abs_laplacian_le N Q hQacc (f j) (fun w : R => ‖T.pos w - T.pos v‖ ^ 2)
        (c := M / 2) hlapf hbdry hvQ (mul_nonneg (by linarith) (sq_nonneg _))
    have hρq : M / 2 * ρ ^ 2 ≤ M * ρ ^ 2 := by
      have := mul_nonneg hM0 (sq_nonneg ρ)
      linarith
    have hquad : |hDR vR - g vR| ≤ η + M * ρ ^ 2 := by
      have htri : |f 0 vR| ≤ |f 0 vR - f j vR| + |f j vR| := by
        have := abs_sub_le (f 0 vR) (f j vR) 0
        simpa only [sub_zero] using this
      rw [hsplit vR]
      calc |N.boundaryCorrection A ha r vR + f 0 vR|
          ≤ |N.boundaryCorrection A ha r vR| + |f 0 vR| := abs_add_le _ _
        _ ≤ M * ε + ((∑ i ∈ Finset.range j, cost i) + M / 2 * ρ ^ 2) :=
          add_le_add (hb vR) (htri.trans (add_le_add (htele j vR) hfj))
        _ ≤ η + M * ρ ^ 2 := by rw [hηdef]; linarith [hsum, hρq]
    -- the case analysis
    have hcase := component_case_bound (x := |hDR vR - g vR| - η) (R := D₀) hL0 hM0 hε hε2 hK
      hD₀ hDq0 hDq hρ0 (min_le_left _ _) (min_le_right _ _) (by linarith) (by linarith)
    linarith [hcase]
  have hgoal : |hDR vR - g vR| ≤
      (C₀ + (4 * (D₀ + 1) + 1) / Real.log 2) * M * K * ε * Real.log (1 / ε) + Dc * L := by
    linarith [hηP, hkey, hid]
  exact hgoal

end SpherePackings
