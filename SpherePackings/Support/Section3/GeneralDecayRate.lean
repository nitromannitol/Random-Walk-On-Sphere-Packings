module

-- Built on Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne (commit cf73d6e).
public import SpherePackings.Support.Section3.DecayRateArith
public import SpherePackings.Support.Section3.DecaySegment
public import SpherePackings.Support.Section3.GeneralRateFull
public import BouRabeeGwynne.Section3CaseIIITarget
public import BouRabeeGwynne.Section3CaseIITarget

@[expose] public section

/-!
# Theorem 3.7 with its rate (intermediate result)

**Intermediate result**, under the earlier, stronger hypotheses (the cells of `V[U]` in the interior
of the ambient set, and the Hessian bound also on the edge segments of `E[Ū]`); it is not
registered. The registered Theorem 3.7 is the corrected paper's, `generaldim_decay_rate_internal`
(`DecayInternal.lean`).

`rw-spheres.tex:1314-1340` (label `theorem:generaldim-decay`): under the decay hypothesis
`diam(P_v) ≤ F sup_{e = (w, v)} vol_d(Q_e)^α` on `V[U]`, `sup_{V[U]} |h_D - h_C| ≤ C M ε log(1/ε)`
for `ε < (C M)⁻¹`, with `C = C(U, F, α)`.

The printed proof has a gap at `rw-spheres.tex:1371` (check G1 in `GAP-CHECKS.md`): the iteration
replaces `ε` by the diameter `δ_i` of the cells of the bad set, but its estimates involve the cells
of the boundary of the bad set.  leobon12's corrected iteration (`correctedRegions`) controls them
with a boundary-corrected energy and the trimming cutoff `√(ε δ_i)`, and bounds the error by
`hypIIICost`, with scales `δ_i ≤ ε` and `δ_i ≤ J r^i`, `r = 2^{-α}`; that cost is
`O(M ε log(1/ε))` (`hypIIICost_le_rate`).  This gives the printed rate.

The decay hypothesis is leobon12's form `diam(P_v) ≤ F · sup_w (‖w - v‖ vol_{d-1}(P_v ∩ P_w))^α`,
which is the printed one by Lemma 2.4 (`‖e‖ vol_{d-1}(H_e) = d vol_d(Q_e)`), with `F` scaled by
`d^α`.  The hypotheses on `h_C` are those of the edge-segment form of Proposition 2.6 (`EnergyMinimal.lean`),
as in Theorem 3.6: harmonic near the cells of `V̄[U]`, with the Hessian bound `M` on those cells and
on the edge segments of `E[Ū]`, the cells of `V[U]` in the interior of the ambient set; the estimates
of the iteration are the segment versions of `DecaySegment.lean`.  `C(U)` enters through a bound
`R₀` on `‖x‖` over `U`.
-/

namespace SpherePackings

open BouRabeeGwynne BouRabeeGwynne.OrthogonalTiling

open scoped Classical ENNReal MeasureTheory

variable {d : ℕ}

/-- Theorem 3.7 (`theorem:generaldim-decay`) with its rate, for one tiling, under the edge-segment
hypothesis (intermediate result, not registered). -/
theorem generaldim_decay_rate (hd : 1 ≤ d) (T : OrthogonalTiling d) (U : Set (Euc d))
    [Fintype (T.closedVertices U)]
    (hcellD : ∀ v ∈ T.interiorVertices U, (T.cell v).carrier ⊆ interior T.domain)
    {R₀ : ℝ} (hR₀ : 0 ≤ R₀) (hUR : ∀ x ∈ U, ‖x‖ ≤ R₀)
    {W : Set (Euc d)} (hW : IsOpen W) {hC : Euc d → ℝ} (hh : IsHarmonicOn hC W)
    (hcells : ∀ v ∈ T.closedVertices U, (T.cell v).carrier ⊆ W)
    {W' : Set (Euc d)} (hW' : IsOpen W') (hC2 : ContDiffOn ℝ 2 hC W')
    (hsegs : ∀ v ∈ T.closedVertices U, ∀ w ∈ T.closedVertices U, T.adj v w →
      v ∈ T.interiorVertices U ∨ w ∈ T.interiorVertices U →
      segment ℝ (T.pos v) (T.pos w) ⊆ W')
    {M ε : ℝ} (hM : 1 ≤ M)
    (hdiam : ∀ v ∈ T.closedVertices U, Metric.diam (T.cell v).carrier ≤ ε)
    (hHcell : ∀ v ∈ T.closedVertices U, ∀ x ∈ (T.cell v).carrier,
      ‖fderiv ℝ (fderiv ℝ hC) x‖ ≤ M)
    (hHseg : ∀ v ∈ T.closedVertices U, ∀ w ∈ T.closedVertices U, T.adj v w →
      v ∈ T.interiorVertices U ∨ w ∈ T.interiorVertices U →
      ∀ x ∈ segment ℝ (T.pos v) (T.pos w), ‖fderiv ℝ (fderiv ℝ hC) x‖ ≤ M)
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
  have hcellDA : ∀ w ∈ A, (T.cell (w : T.V)).carrier ⊆ interior T.domain :=
    fun w hw => hcellD w hw
  have hneighbors : ∀ w : R, w ∈ A → ∀ x, T.adj w x → x ∈ R :=
    fun w hw x hwx => T.neighbor_mem_closedVertices hw hwx
  have ha := T.finiteNetwork_boundaryAccessible_of_cell_interior hd e he R A hneighbors hcellDA
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
  have hcellW : ∀ w ∈ A, (T.cell (w : T.V)).carrier ⊆ W := fun w _ => hcells w w.property
  have hHcellA : ∀ w ∈ A, ∀ x ∈ (T.cell (w : T.V)).carrier, ‖fderiv ℝ (fderiv ℝ hC) x‖ ≤ M :=
    fun w _ => hHcell w w.property
  have hsegA : ∀ w ∈ A, ∀ x : R, T.adj w x → segment ℝ (T.pos w) (T.pos x) ⊆ W' :=
    fun w hw x hwx => hsegs w w.property x x.property hwx (Or.inl hw)
  have hHsegA : ∀ w ∈ A, ∀ x : R, T.adj w x → ∀ y ∈ segment ℝ (T.pos w) (T.pos x),
      ‖fderiv ℝ (fderiv ℝ hC) y‖ ≤ M :=
    fun w hw x hwx => hHseg w w.property x x.property hwx (Or.inl hw)
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
    exact (correctedRegions_mass_le_geometric_segment hd T R A ha hneighbors hcellDA hC e he
      (-D) D (by linarith) hheight hK hMpos hε hwidth hsmall' hlength hdiamA hW hh hcellW hHcellA
      hW' hC2 hsegA hHsegA i).trans
        (mul_le_mul_of_nonneg_right hmass (pow_nonneg (by norm_num) i))
  have hgeom : ∀ i, δ i ≤ J * r ^ i :=
    T.regionDiameter_le_geometric_of_mass R (fun i => (S i).val)
      (fun i w hw => hneighbors w (hsub i hw)) hα.le hF (fun i w hw => hreg w (hsub i hw)) hI hdecay
  have hδ0 : ∀ i, 0 ≤ δ i := fun i => T.toTilingData.regionDiameter_nonneg R (S i).val
  have hδε : ∀ i, δ i ≤ ε := fun i =>
    T.toTilingData.regionDiameter_le R (S i).val hε.le (fun w hw => hdiamA w (hsub i hw))
  have hcost := dirichlet_error_le_hypIIICost_segment hd T R A ha hneighbors hcellDA hC e he
    (-D) D (by linarith) hheight hK hMpos hε hwidth hsmall' hlength hdiamA hW hh hcellW hHcellA
    hW' hC2 hsegA hHsegA hα hF (fun w hw => hreg w hw) hI hmass vR
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
