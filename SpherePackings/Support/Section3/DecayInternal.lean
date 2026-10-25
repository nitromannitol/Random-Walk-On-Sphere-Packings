module

-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (files `BouRabeeGwynne/HypIIIErrorBound.lean` and `BouRabeeGwynne/HypIIICorrectedTrimming.lean` at
-- commit cf73d6e): the corrected iteration of Theorem 3.7, for complete cells and Taylor control on
-- internal edges only.
public import SpherePackings.Support.Section3.InternalTaylor
public import SpherePackings.Support.Section3.GeneralDecayRate
public import SpherePackings.Support.Complete.Section3

@[expose] public section

/-!
# Theorem 3.7 as in the corrected paper

`rw-spheres-corrected.tex`, Theorem 3.7: `M = M_U°(h_C) ∨ 1`, i.e. the Hessian bound `M` on the
cells of `V̄[U]` and the finite Taylor inequality with `M` on the internal edges (both endpoints in
`V[U]`) only; the cells of `V[U]` are complete and `h_C` is `C²` near the cells and harmonic on the
cells of `V[U]`.  leobon12's corrected iteration (`correctedRegions`) needs Taylor remainders only on
edges inside a region (internal edges) and on the boundary edges of `V[U]` at the first step; the
latter are bounded by the cell Hessian alone (`surfaceTaylorRemainder_abs_le_cells`).
-/

namespace SpherePackings

open BouRabeeGwynne BouRabeeGwynne.OrthogonalTiling

open scoped Classical ENNReal MeasureTheory Laplacian

variable {d : ℕ}

/-- leobon12's trimming step of the corrected iteration, for complete cells, with the Taylor
inequality on the edges of the region and the Hessian bound on its cells. -/
theorem boundaryCorrected_trimmed_mass_le_half_internal (hd : 1 ≤ d) (T : OrthogonalTiling d)
    (R : Set T.V) [Fintype R] (A : Set R)
    (hA : (T.finiteNetwork R).BoundaryAccessible A)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    (hcomplete : ∀ v ∈ A, CompleteCell T v)
    (h : Euc d → ℝ) (e : Euc d) (he : e ≠ 0) (a b : ℝ) (hab : a ≤ b)
    (hheight : ∀ v ∈ A, ∀ x ∈ (T.cell v).carrier,
      inner ℝ e x / inner ℝ e e ∈ Set.Icc a b)
    {K M ε δ : ℝ} (hK : 0 < K) (hM : 0 < M) (hε : 0 < ε)
    (hδ : 0 < δ) (hδε : δ ≤ ε)
    (hwidth : 12 * ((d : ℝ) * ‖e‖ * (b - a)) ≤ K)
    (hsmall : 144 * M ^ 2 * ε ^ 2 ≤ 1)
    (hlength : ∀ v w : R, T.adj v w → ‖T.pos w - T.pos v‖ ≤ 2 * ε)
    (hdiam : ∀ v ∈ A, Metric.diam (T.cell v).carrier ≤ δ)
    {W : Set (Euc d)} (hW : IsOpen W) (hC2 : ContDiffOn ℝ 2 h W)
    (hcellW : ∀ v ∈ A, (T.cell v.val).carrier ⊆ W)
    (hHcell : ∀ v ∈ A, ∀ x ∈ (T.cell v.val).carrier, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M)
    (hharm : ∀ v ∈ A, ∀ x ∈ (T.cell v.val).carrier, Δ h x = 0)
    (htaylor : ∀ v ∈ A, ∀ w ∈ A, T.adj v.val w.val →
      |T.surfaceTaylorRemainder h v w| ≤ M / 2 * ‖T.pos w - T.pos v‖ ^ 2) :
    let f := (T.finiteNetwork R).boundaryCorrectedError A hA
      (fun v => h (T.pos v)) (fun v w => T.surfaceTaylorRemainder h v w)
    T.incidentMass R ((T.finiteNetwork R).trimmedErrorSet A f
      (K * M * δ) (Real.sqrt (ε * δ))) ≤ (1 / 2 : ℝ) * T.incidentMass R A := by
  dsimp only
  apply correctedError_trimmed_mass_le_half_of_complete hd T R A hneighbors hcomplete _
    (fun _ hv => (T.finiteNetwork R).boundaryCorrectedError_boundary A hA _ _ hv)
    e he a b hab hheight hK hM hε hδ hδε hwidth hsmall hlength
  exact energy_boundaryCorrected_le_internal hd T R A hA _ h hM.le
    ((T.finiteNetwork R).dirichletSolution_spec A hA _) hdiam hcomplete hneighbors
    hW hC2 hcellW hharm hHcell htaylor

/-- leobon12's geometric mass decay of the corrected regions, for complete cells and Taylor control
on the edges of the region. -/
theorem correctedRegions_mass_le_geometric_internal (hd : 1 ≤ d) (T : OrthogonalTiling d)
    (R : Set T.V) [Fintype R] (A : Set R)
    (hA : (T.finiteNetwork R).BoundaryAccessible A)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    (hcomplete : ∀ v ∈ A, CompleteCell T v)
    (h : Euc d → ℝ) (e : Euc d) (he : e ≠ 0) (a b : ℝ) (hab : a ≤ b)
    (hheight : ∀ v ∈ A, ∀ x ∈ (T.cell v).carrier,
      inner ℝ e x / inner ℝ e e ∈ Set.Icc a b)
    {K M ε : ℝ} (hK : 0 < K) (hM : 0 < M) (hε : 0 < ε)
    (hwidth : 12 * ((d : ℝ) * ‖e‖ * (b - a)) ≤ K)
    (hsmall : 144 * M ^ 2 * ε ^ 2 ≤ 1)
    (hlength : ∀ v w : R, T.adj v w → ‖T.pos w - T.pos v‖ ≤ 2 * ε)
    (hdiam : ∀ v ∈ A, Metric.diam (T.cell v).carrier ≤ ε)
    {W : Set (Euc d)} (hW : IsOpen W) (hC2 : ContDiffOn ℝ 2 h W)
    (hcellW : ∀ v ∈ A, (T.cell v.val).carrier ⊆ W)
    (hHcell : ∀ v ∈ A, ∀ x ∈ (T.cell v.val).carrier, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M)
    (hharm : ∀ v ∈ A, ∀ x ∈ (T.cell v.val).carrier, Δ h x = 0)
    (htaylor : ∀ v ∈ A, ∀ w ∈ A, T.adj v.val w.val →
      |T.surfaceTaylorRemainder h v w| ≤ M / 2 * ‖T.pos w - T.pos v‖ ^ 2) :
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
      exact boundaryCorrected_trimmed_mass_le_half_internal hd T R (S n).val
        ((T.finiteNetwork R).boundaryAccessible_mono (hsub n) hA)
        (fun v hv => hneighbors v (hsub n hv))
        (fun v hv => hcomplete v (hsub n hv)) h e he a b hab
        (fun v hv => hheight v (hsub n hv)) hK hM hε hδ hδε hwidth hsmall hlength
        (fun _ hv => T.toTilingData.cell_diam_le_regionDiameter R (S n).val hv)
        hW hC2 (fun v hv => hcellW v (hsub n hv)) (fun v hv => hHcell v (hsub n hv))
        (fun v hv => hharm v (hsub n hv))
        (fun v hv w hw hvw => htaylor v (hsub n hv) w (hsub n hw) hvw)
  intro n
  induction n with
  | zero => simp only [correctedRegions, Nat.rec_zero, pow_zero, mul_one, le_refl]
  | succ n ih =>
    calc
      _ ≤ (1 / 2 : ℝ) * T.incidentMass R (S n).val := hstep n
      _ ≤ (1 / 2 : ℝ) * (T.incidentMass R A * (1 / 2 : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; ring

/-- leobon12's bound of the Dirichlet error by the corrected cost series, given the mass decay.
The Taylor inequality is needed on the edges of the region `A`; the diameters, the Hessian bound
and the inclusion in `W` on all cells of `R` (the first step uses the cells of the boundary of
`A` in `R`). -/
theorem dirichlet_error_le_hypIIICost_of_mass_decay_internal (hd : 1 ≤ d) (T : OrthogonalTiling d)
    (R : Set T.V) [Fintype R] (A : Set R)
    (hA : (T.finiteNetwork R).BoundaryAccessible A)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    (h : Euc d → ℝ) {K M ε : ℝ} (hK : 0 ≤ K) (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hdiam : ∀ v : R, Metric.diam (T.cell v).carrier ≤ ε)
    {W : Set (Euc d)} (hW : IsOpen W) (hC2 : ContDiffOn ℝ 2 h W)
    (hcellW : ∀ v : R, (T.cell v.val).carrier ⊆ W)
    (hHcell : ∀ v : R, ∀ x ∈ (T.cell v.val).carrier, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M)
    (htaylor : ∀ v ∈ A, ∀ w ∈ A, T.adj v.val w.val →
      |T.surfaceTaylorRemainder h v w| ≤ M / 2 * ‖T.pos w - T.pos v‖ ^ 2)
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
    (fun u _ => hdiam u)
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
    have hdist := T.edge_dist_le_two_diam_bound ha
      (T.toTilingData.cell_diam_le_regionDiameter R (S i) hu)
      (T.toTilingData.cell_diam_le_regionDiameter R (S i) hw)
    have hnorm : ‖T.pos w - T.pos u‖ ≤ 2 * δ i := by
      rw [← dist_eq_norm, dist_comm]
      exact hdist
    have hsq : ‖T.pos w - T.pos u‖ ^ 2 ≤ (2 * δ i) ^ 2 := by gcongr
    calc |reward u w| ≤ M / 2 * ‖T.pos w - T.pos u‖ ^ 2 :=
          htaylor u (hsub i hu) w (hsub i hw) ha
      _ ≤ M / 2 * (2 * δ i) ^ 2 := mul_le_mul_of_nonneg_left hsq (by linarith)
      _ ≤ 6 * M * δ i ^ 2 := by nlinarith [mul_nonneg hM (sq_nonneg (δ i))]
  have hinitial (u : R) (_ : u ∈ S 0) (w : R) (_ : w ∉ S 0)
      (huw : 0 < N.a u w) : |reward u w| ≤ 6 * M * ε ^ 2 := by
    have ha : T.adj u w := T.conductanceReal_pos_iff.mp huw
    have hcell := surfaceTaylorRemainder_abs_le_cells T h ha hW hC2 (hcellW u) (hcellW w) hM
      (hdiam u) (hdiam w) (hHcell u) (hHcell w)
    have h2 : 2 * M * ε ^ 2 ≤ 6 * M * ε ^ 2 := by nlinarith [mul_nonneg hM (sq_nonneg ε)]
    exact hcell.trans h2
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

/-- leobon12's finite Case III estimate, for complete cells, with the Taylor inequality on the
edges of the region (`A`), the Hessian bound on the cells of `R`, and `h` `C²` on `W` with
harmonic cells in `A`. -/
theorem dirichlet_error_le_hypIIICost_internal (hd : 1 ≤ d) (T : OrthogonalTiling d)
    (R : Set T.V) [Fintype R] (A : Set R)
    (hA : (T.finiteNetwork R).BoundaryAccessible A)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    (hcomplete : ∀ v ∈ A, CompleteCell T v)
    (h : Euc d → ℝ) (e : Euc d) (he : e ≠ 0) (a b : ℝ) (hab : a ≤ b)
    (hheight : ∀ v ∈ A, ∀ x ∈ (T.cell v).carrier,
      inner ℝ e x / inner ℝ e e ∈ Set.Icc a b)
    {K M ε : ℝ} (hK : 0 < K) (hM : 0 < M) (hε : 0 < ε)
    (hwidth : 12 * ((d : ℝ) * ‖e‖ * (b - a)) ≤ K)
    (hsmall : 144 * M ^ 2 * ε ^ 2 ≤ 1)
    (hlength : ∀ v w : R, T.adj v w → ‖T.pos w - T.pos v‖ ≤ 2 * ε)
    (hdiam : ∀ v : R, Metric.diam (T.cell v).carrier ≤ ε)
    {W : Set (Euc d)} (hW : IsOpen W) (hC2 : ContDiffOn ℝ 2 h W)
    (hcellW : ∀ v : R, (T.cell v.val).carrier ⊆ W)
    (hHcell : ∀ v : R, ∀ x ∈ (T.cell v.val).carrier, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M)
    (hharm : ∀ v ∈ A, ∀ x ∈ (T.cell v.val).carrier, Δ h x = 0)
    (htaylor : ∀ v ∈ A, ∀ w ∈ A, T.adj v.val w.val →
      |T.surfaceTaylorRemainder h v w| ≤ M / 2 * ‖T.pos w - T.pos v‖ ^ 2)
    {α : ℝ} (hα : 0 < α) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hreg : ∀ v ∈ A, (T.cell v).diamENN ≤ C * T.incidentScale α v)
    {I : ℝ} (hI : 0 ≤ I) (hIbound : T.incidentMass R A ≤ I) (v : R) :
    |(T.finiteNetwork R).dirichletSolution A hA (fun v => h (T.pos v)) v - h (T.pos v)| ≤
      hypIIICost K (3 * M) ε
        (fun n => T.toTilingData.regionDiameter R
          (T.correctedRegions R A hA h K M ε n).val) := by
  apply dirichlet_error_le_hypIIICost_of_mass_decay_internal hd T R A hA hneighbors h
    hK.le hM.le hε.le hdiam hW hC2 hcellW hHcell htaylor hα hC hreg hI _ v
  intro n
  exact (correctedRegions_mass_le_geometric_internal hd T R A hA hneighbors hcomplete h e he a b
    hab hheight hK hM hε hwidth hsmall hlength (fun v _ => hdiam v) hW hC2
    (fun v _ => hcellW v) (fun v _ => hHcell v) hharm htaylor n).trans
    (mul_le_mul_of_nonneg_right hIbound (pow_nonneg (by norm_num) n))

/-- **Theorem 3.7** (`theorem:generaldim-decay`), as in the corrected paper. -/
theorem generaldim_decay_rate_internal (hd : 1 ≤ d) (T : OrthogonalTiling d) (U : Set (Euc d))
    [Fintype (T.closedVertices U)]
    (hcomplete : ∀ v ∈ T.interiorVertices U, CompleteCell T v)
    {R₀ : ℝ} (hR₀ : 0 ≤ R₀) (hUR : ∀ x ∈ U, ‖x‖ ≤ R₀)
    {W : Set (Euc d)} (hW : IsOpen W) {hC : Euc d → ℝ} (hC2 : ContDiffOn ℝ 2 hC W)
    (hcells : ∀ v ∈ T.closedVertices U, (T.cell v).carrier ⊆ W)
    (hharm : ∀ v ∈ T.interiorVertices U, ∀ x ∈ (T.cell v).carrier, Δ hC x = 0)
    {M ε : ℝ} (hM : 1 ≤ M)
    (hdiam : ∀ v ∈ T.closedVertices U, Metric.diam (T.cell v).carrier ≤ ε)
    (hHcell : ∀ v ∈ T.closedVertices U, ∀ x ∈ (T.cell v).carrier,
      ‖fderiv ℝ (fderiv ℝ hC) x‖ ≤ M)
    (hTaylor : ∀ v ∈ T.interiorVertices U, ∀ w ∈ T.interiorVertices U, T.adj v w →
      |hC (T.pos w) - hC (T.pos v) - (fderiv ℝ hC (T.pos v)) (T.pos w - T.pos v)| ≤
        M / 2 * ‖T.pos w - T.pos v‖ ^ 2)
    {α : ℝ} (hα : 0 < α) {F : ℝ≥0∞} (hF : F ≠ ⊤)
    (hreg : ∀ v ∈ T.interiorVertices U, (T.cell v).diamENN ≤ F * T.incidentScale α v)
    (hsmall : 12 * M * ε ≤ 1) (hε2 : ε ≤ 1 / 2)
    (hD : T.V → ℝ) (hsol : T.SolvesDirichlet U (fun v => hC (T.pos v)) hD) :
    ∀ v ∈ T.interiorVertices U, |hD v - hC (T.pos v)| ≤
      hypIIIRateConstant (12 * ((d : ℝ) * ((R₀ + 1) - -(R₀ + 1))) + 1)
          (F.toReal * (2 * ((d : ℝ) *
            (μHE[d] (Metric.closedBall (0 : Euc d) (R₀ + 1))).toReal)) ^ α) ((1 / 2 : ℝ) ^ α) *
        (3 * M) * ε * Real.log (1 / ε) := by
  intro v hv
  obtain ⟨e, he, hnorm⟩ := exists_unit_euc hd
  set D := R₀ + 1 with hDdef
  set Q := Metric.closedBall (0 : Euc d) D with hQdef
  let R := T.closedVertices U
  let A : Set R := T.finiteInterior U
  let vR : R := ⟨v, T.interiorVertices_subset_closedVertices U hv⟩
  have hvA : vR ∈ A := hv
  have hcellR : ∀ w : R, (T.cell w).carrier ⊆ Q := fun w x hx =>
    mem_closedBall_zero_iff.mpr (cell_norm_le_of_closedVertices T U hUR hε2 hdiam w.property hx)
  have hcompleteA : ∀ w ∈ A, CompleteCell T (w : T.V) :=
    fun w hw => hcomplete (w : T.V) hw
  have hneighbors : ∀ w : R, w ∈ A → ∀ x, T.adj w x → x ∈ R :=
    fun w hw x hwx => T.neighbor_mem_closedVertices hw hwx
  have ha := finiteNetwork_boundaryAccessible_of_complete hd T e he R A hneighbors hcompleteA
  have hdistR : ∀ (w : R) {x y : Euc d}, x ∈ (T.cell (w : T.V)).carrier →
      y ∈ (T.cell (w : T.V)).carrier → dist x y ≤ ε := fun w _ _ hx hy =>
    (Metric.dist_le_diam_of_mem (T.cell _).compact.isBounded hx hy).trans (hdiam w w.property)
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
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  have hheight : ∀ w ∈ A, ∀ x ∈ (T.cell (w : T.V)).carrier,
      inner ℝ e x / inner ℝ e e ∈ Set.Icc (-D) D := by
    intro w _ x hx
    rw [real_inner_self_eq_norm_sq, hnorm, one_pow, div_one]
    apply abs_le.mp
    calc
      |inner ℝ e x| ≤ ‖e‖ * ‖x‖ := abs_real_inner_le_norm _ _
      _ = ‖x‖ := by rw [hnorm, one_mul]
      _ ≤ D := mem_closedBall_zero_iff.mp (hcellR w hx)
  have hQfinite : μHE[d] Q ≠ ⊤ := by
    have hm : (μHE[d] : MeasureTheory.Measure (Euc d)) = MeasureTheory.volume := by
      simpa using InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := Euc d)
    rw [hm]
    exact (isCompact_closedBall _ _).measure_lt_top.ne
  set I := (d : ℝ) * (μHE[d] Q).toReal with hIdef
  have hI : 0 ≤ I := mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg
  have hmass : T.incidentMass R A ≤ I :=
    T.incidentMass_le_dim_mul_volume hd R A hQfinite hcellR
  have hlength : ∀ a b : R, T.adj a b → ‖T.pos b - T.pos a‖ ≤ 2 * ε := by
    intro a b hab
    obtain ⟨z, hza, hzb⟩ := hab.2.1
    have h := (dist_triangle (T.pos b) z (T.pos a)).trans
      (add_le_add (hdistR b (hposcell b) hzb) (hdistR a hza (hposcell a)))
    rw [dist_eq_norm] at h
    linarith
  have hdiamA : ∀ w ∈ A, Metric.diam (T.cell (w : T.V)).carrier ≤ ε :=
    fun w _ => hdiam w w.property
  have hdiamR : ∀ w : R, Metric.diam (T.cell (w : T.V)).carrier ≤ ε :=
    fun w => hdiam w w.property
  have hcellWA : ∀ w ∈ A, (T.cell (w : T.V)).carrier ⊆ W := fun w _ => hcells w w.property
  have hcellWR : ∀ w : R, (T.cell (w : T.V)).carrier ⊆ W := fun w => hcells w w.property
  have hHcellA : ∀ w ∈ A, ∀ x ∈ (T.cell (w : T.V)).carrier, ‖fderiv ℝ (fderiv ℝ hC) x‖ ≤ M :=
    fun w _ => hHcell w w.property
  have hHcellR : ∀ w : R, ∀ x ∈ (T.cell (w : T.V)).carrier, ‖fderiv ℝ (fderiv ℝ hC) x‖ ≤ M :=
    fun w => hHcell w w.property
  have hharmA : ∀ w ∈ A, ∀ x ∈ (T.cell (w : T.V)).carrier, Δ hC x = 0 :=
    fun w hw => hharm (w : T.V) hw
  have htaylorA : ∀ w ∈ A, ∀ x ∈ A, T.adj w.val x.val →
      |T.surfaceTaylorRemainder hC w x| ≤ M / 2 * ‖T.pos x - T.pos w‖ ^ 2 :=
    fun w hw x hx hwx => hTaylor (w : T.V) hw (x : T.V) hx hwx
  set H := (d : ℝ) * ‖e‖ * (D - -D) with hHdef
  have hH0 : 0 ≤ H := mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) (by linarith)
  set K := 12 * H + 1 with hKdef
  have hK : 0 < K := by positivity
  have hwidth : 12 * H ≤ K := by linarith
  have hsmall' : 144 * M ^ 2 * ε ^ 2 ≤ 1 := by
    have h0 : 0 ≤ 12 * M * ε := by positivity
    nlinarith
  set J := F.toReal * (2 * I) ^ α with hJdef
  have hJ : 0 ≤ J := mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (by positivity) α)
  set r := (1 / 2 : ℝ) ^ α with hrdef
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) α
  have hr1 : r < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα
  let S := T.correctedRegions R A ha hC K M ε
  let δ := fun i => T.toTilingData.regionDiameter R (S i).val
  have hsub (i : ℕ) : (S i).val ⊆ A := (S i).property
  have hdecay : ∀ i, T.incidentMass R (S i).val ≤ I * (1 / 2 : ℝ) ^ i := by
    intro i
    exact (correctedRegions_mass_le_geometric_internal hd T R A ha hneighbors hcompleteA hC e he
      (-D) D (by linarith) hheight hK hMpos hε hwidth hsmall' hlength hdiamA hW hC2 hcellWA
      hHcellA hharmA htaylorA i).trans
      (mul_le_mul_of_nonneg_right hmass (pow_nonneg (by norm_num) i))
  have hgeom : ∀ i, δ i ≤ J * r ^ i :=
    T.regionDiameter_le_geometric_of_mass R (fun i => (S i).val)
      (fun i w hw => hneighbors w (hsub i hw)) hα.le hF (fun i w hw => hreg w (hsub i hw)) hI hdecay
  have hδ0 : ∀ i, 0 ≤ δ i := fun i => T.toTilingData.regionDiameter_nonneg R (S i).val
  have hδε : ∀ i, δ i ≤ ε := fun i =>
    T.toTilingData.regionDiameter_le R (S i).val hε.le (fun w hw => hdiamA w (hsub i hw))
  have hcost := dirichlet_error_le_hypIIICost_internal hd T R A ha hneighbors hcompleteA hC e he
    (-D) D (by linarith) hheight hK hMpos hε hwidth hsmall' hlength hdiamR hW hC2 hcellWR
    hHcellR hharmA htaylorA hα hF (fun w hw => hreg w hw) hI hmass vR
  have hrate := hypIIICost_le_rate (A := K) (M := 3 * M) δ hK.le (by linarith) hε hε2
    hJ hr0 hr1 hδ0 hδε hgeom
  have heq := (T.finiteNetwork R).dirichlet_unique A ha
    (T.solvesDirichlet_restrict hsol)
    ((T.finiteNetwork R).dirichletSolution_spec A ha (fun w : R => hC (T.pos w)))
  have heqv := congrFun heq vR
  change hD v = _ at heqv
  rw [heqv]
  have hK' : K = 12 * ((d : ℝ) * (D - -D)) + 1 := by rw [hKdef, hHdef, hnorm, mul_one]
  rw [← hK']
  exact hcost.trans hrate

end SpherePackings
