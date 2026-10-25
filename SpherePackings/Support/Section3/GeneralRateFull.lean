module

-- Built on Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne (commit cf73d6e).
public import SpherePackings.Support.Section3.ComponentChain
public import SpherePackings.Support.Section3.ComponentLaplacian
public import SpherePackings.Support.Section3.ComponentArith
public import SpherePackings.Support.Section3.EnergyMinimal
public import BouRabeeGwynne.Section3CaseIITarget
public import BouRabeeGwynne.Section3LocalMaximum

@[expose] public section

/-!
# Theorem 3.6 with its full bound (intermediate result)

**Intermediate result**, under the earlier, stronger hypotheses (the cells of `V[U]` in the interior
of the ambient set, and the Hessian bound also on the edge segments of `E[Ū]`); it is not
registered. The registered Theorem 3.6 is the corrected paper's, `generaldim_full_internal`
(`GeneralInternal.lean`), which also uses the arithmetic lemmas of this module.

`rw-spheres.tex:1147-1176` (label `theorem:generaldim`): for `ε < (C M)⁻¹`,
`sup_{V[U]} |h_D - h_C| ≤ C M K ε log(1/ε) + D L`, where `ε` bounds the diameters of the cells of
`V̄[U]`, `M ≥ 1` the Hessian and `L` the gradient of `h_C` on `Û`, `K ≥ 1` is arbitrary, and `D`
bounds the total diameter of every connected set of cells of `V̄[U]` with volume below `ε^K`.

The proof follows the paper.  The harmonic-replacement iteration (Step 1, leobon12's
`harmonicIteration`) leaves, after `j ≈ C K log(1/ε)` steps, an error at most `j (A M + 2) ε` off a
region whose cells have volume below `ε^K` (Step 3, with the energy bound of the edge-segment form of
Proposition 2.6).  On a connected component `Q` of that region the paper bounds the error by the
oscillation of `h_C` along the cells of `Q` (Step 2).  Here the exit cell is accounted for: the
oscillation bound is `L (D_Q + ε)`, and a second bound `M ρ²`, with `ρ` the distance to the exit
vertices, comes from the discrete subharmonicity of `±(h_D - h_C) + M |· - v|²` (Lemma 2.2 and
Taylor's theorem on the edge segments).  Their minimum is at most `D L + C M K ε log(1/ε)`
(`component_case_bound`).

Hypotheses as in the edge-segment form of Proposition 2.6: the cells of `V[U]` lie in the interior of the
ambient set, and the Hessian bound `M` holds also on the edge segments of `E[Ū]`.  The constant
depends only on `d` and a bound `R₀` on `‖x‖` over `U`.
-/

namespace SpherePackings

open BouRabeeGwynne BouRabeeGwynne.OrthogonalTiling

open scoped BigOperators Classical MeasureTheory

variable {d : ℕ}

/-- `exp (-(K log (1/ε))) = ε ^ K` for `ε > 0`. -/
private lemma exp_neg_mul_log_inv_full {ε K : ℝ} (hε : 0 < ε) :
    Real.exp (-(K * Real.log (1 / ε))) = ε ^ K := by
  rw [Real.rpow_def_of_pos hε, one_div, Real.log_inv]
  congr 1
  ring

/-- The arithmetic step from the explicit iteration cost to the paper's form. -/
private lemma rate_factor_le_full {K a b : ℝ} (hK : 1 ≤ K) (ha : 1 ≤ a) (hb : 0 ≤ b) :
    K * a + b + 2 ≤ (3 + b) * (K * a) := by
  have h1 : 1 ≤ K * a := one_le_mul_of_one_le_of_one_le hK ha
  nlinarith

/-- Every point of a cell of `V̄[U]` is within `2 ε` of a point of `U`. -/
lemma cell_norm_le_of_closedVertices (T : OrthogonalTiling d) (U : Set (Euc d)) {R₀ ε : ℝ}
    (hUR : ∀ x ∈ U, ‖x‖ ≤ R₀) (hε2 : ε ≤ 1 / 2)
    (hdiam : ∀ v ∈ T.closedVertices U, Metric.diam (T.cell v).carrier ≤ ε)
    {w : T.V} (hw : w ∈ T.closedVertices U) {x : Euc d} (hx : x ∈ (T.cell w).carrier) :
    ‖x‖ ≤ R₀ + 1 := by
  have hcell : ∀ {u : T.V}, u ∈ T.closedVertices U → ∀ {y z : Euc d},
      y ∈ (T.cell u).carrier → z ∈ (T.cell u).carrier → dist y z ≤ ε :=
    fun hu _ _ hy hz =>
      (Metric.dist_le_diam_of_mem (T.cell _).compact.isBounded hy hz).trans (hdiam _ hu)
  rcases hw with hwi | ⟨-, u, hu, huw⟩
  · have h1 : dist x (T.pos w) ≤ ε :=
      hcell (Or.inl hwi) hx (interior_subset (T.pos_mem_interior w))
    have h2 : ‖T.pos w‖ ≤ R₀ := hUR _ hwi
    have h3 := norm_sub_norm_le x (T.pos w)
    rw [dist_eq_norm] at h1
    linarith
  · obtain ⟨z, hzu, hzw⟩ := huw.2.1
    have h1 : dist x z ≤ ε := hcell (T.neighbor_mem_closedVertices hu huw) hx hzw
    have h2 : dist z (T.pos u) ≤ ε :=
      hcell (Or.inl hu) hzu (interior_subset (T.pos_mem_interior u))
    have h3 : ‖T.pos u‖ ≤ R₀ := hUR _ hu
    have h4 := norm_sub_norm_le x (T.pos u)
    have h5 : dist x (T.pos u) ≤ ε + ε := (dist_triangle _ _ _).trans (add_le_add h1 h2)
    rw [dist_eq_norm] at h5
    linarith

/-- A function with gradient at most `L` on a convex subset of an open set where it is `C²` is
`L`-Lipschitz there. -/
private lemma lipschitz_on_convex {W : Set (Euc d)} (hW : IsOpen W) {h : Euc d → ℝ}
    (hh : ContDiffOn ℝ 2 h W) {P : Set (Euc d)} (hPc : Convex ℝ P) (hPW : P ⊆ W) {L : ℝ}
    (hL : ∀ x ∈ P, ‖fderiv ℝ h x‖ ≤ L) :
    ∀ x ∈ P, ∀ y ∈ P, dist (h x) (h y) ≤ L * dist x y := by
  intro x hx y hy
  have := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hh.differentiableOn (by norm_num)).differentiableAt (hW.mem_nhds (hPW hz)))
    hL hPc hy hx
  rwa [← dist_eq_norm, ← dist_eq_norm] at this

/-- A sum over a duplicate-free list inside a finset is at most the sum over the finset. -/
private lemma list_sum_le_finset_sum {α : Type*} {l : List α} (hl : l.Nodup) {F : Finset α}
    (hlF : ∀ x ∈ l, x ∈ F) {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    (l.map f).sum ≤ ∑ x ∈ F, f x := by
  rw [← List.sum_toFinset f hl]
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => hlF x (List.mem_toFinset.mp hx))
    (fun x _ _ => hf x)

/-- Theorem 3.6 (`theorem:generaldim`) with its full bound `C M K ε log(1/ε) + D L`, under the
edge-segment hypothesis (intermediate result, not registered). -/
theorem generaldim_full (hd : 1 ≤ d) (T : OrthogonalTiling d) (U : Set (Euc d))
    [Fintype (T.closedVertices U)]
    (hcellD : ∀ v ∈ T.interiorVertices U, (T.cell v).carrier ⊆ interior T.domain)
    {R₀ : ℝ} (hR₀ : 0 ≤ R₀) (hUR : ∀ x ∈ U, ‖x‖ ≤ R₀)
    {W : Set (Euc d)} (hW : IsOpen W) {hC : Euc d → ℝ} (hh : IsHarmonicOn hC W)
    (hcells : ∀ v ∈ T.closedVertices U, (T.cell v).carrier ⊆ W)
    {W' : Set (Euc d)} (hW' : IsOpen W') (hC2 : ContDiffOn ℝ 2 hC W')
    (hsegs : ∀ v ∈ T.closedVertices U, ∀ w ∈ T.closedVertices U, T.adj v w →
      v ∈ T.interiorVertices U ∨ w ∈ T.interiorVertices U →
      segment ℝ (T.pos v) (T.pos w) ⊆ W')
    {M L ε K Dc : ℝ} (hM : 1 ≤ M) (hK : 1 ≤ K)
    (hdiam : ∀ v ∈ T.closedVertices U, Metric.diam (T.cell v).carrier ≤ ε)
    (hHcell : ∀ v ∈ T.closedVertices U, ∀ x ∈ (T.cell v).carrier,
      ‖fderiv ℝ (fderiv ℝ hC) x‖ ≤ M)
    (hHseg : ∀ v ∈ T.closedVertices U, ∀ w ∈ T.closedVertices U, T.adj v w →
      v ∈ T.interiorVertices U ∨ w ∈ T.interiorVertices U →
      ∀ x ∈ segment ℝ (T.pos v) (T.pos w), ‖fderiv ℝ (fderiv ℝ hC) x‖ ≤ M)
    (hLgrad : ∀ v ∈ T.closedVertices U, ∀ x ∈ (T.cell v).carrier, ‖fderiv ℝ hC x‖ ≤ L)
    (hDc : ∀ Q : Finset T.V,
      (∀ u ∈ Q, u ∈ T.closedVertices U ∧ (T.cell u).volume.toReal < ε ^ K) →
      (∀ a ∈ Q, ∀ b ∈ Q, (adjGraphIn T ↑Q).Reachable a b) →
      ∑ u ∈ Q, Metric.diam (T.cell u).carrier ≤ Dc)
    (hsmall : 3 * M * ε < 1 / 2) (hε2 : ε ≤ 1 / 2)
    (hD : T.V → ℝ) (hsol : T.SolvesDirichlet U (fun v => hC (T.pos v)) hD) :
    ∀ v ∈ T.interiorVertices U, |hD v - hC (T.pos v)| ≤
      ((24 * d * (R₀ + 1) + 3) *
          (3 + Real.log (max (2 * d * (μHE[d] (Metric.closedBall (0 : Euc d) (R₀ + 1))).toReal) 1)
            / Real.log 2) / Real.log 2 + 4 * (R₀ + 1 + 1) / Real.log 2) *
        M * K * ε * Real.log (1 / ε) + Dc * L := by
  intro v hv
  obtain ⟨e, he, hnorm⟩ := exists_unit_euc hd
  set D₀ := R₀ + 1 with hD₀def
  have hD₀ : 0 ≤ D₀ := by linarith
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  let R := T.closedVertices U
  let A : Set R := T.finiteInterior U
  let N := T.finiteNetwork R
  let vR : R := ⟨v, T.interiorVertices_subset_closedVertices U hv⟩
  have hvA : vR ∈ A := hv
  have hcellR : ∀ w : R, (T.cell w).carrier ⊆ Metric.closedBall (0 : Euc d) D₀ := fun w x hx =>
    mem_closedBall_zero_iff.mpr (cell_norm_le_of_closedVertices T U hUR hε2 hdiam w.property hx)
  have hcellDA : ∀ w ∈ A, (T.cell (w : T.V)).carrier ⊆ interior T.domain :=
    fun w hw => hcellD w hw
  have hneighbors : ∀ w : R, w ∈ A → ∀ x, T.adj w x → x ∈ R :=
    fun w hw x hwx => T.neighbor_mem_closedVertices hw hwx
  have ha := T.finiteNetwork_boundaryAccessible_of_cell_interior hd e he R A hneighbors hcellDA
  have hdiamR : ∀ w : R, Metric.diam (T.cell (w : T.V)).carrier ≤ ε := fun w => hdiam w w.property
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
  -- the iteration
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
  let C := 3 * M
  have hC0 : 0 ≤ C := mul_nonneg (by norm_num) hM0
  let H := (d : ℝ) * ‖e‖ * (D₀ - -D₀)
  have hH0 : 0 ≤ H := mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) (by linarith)
  let Z := caseIIThresholdCoefficient H C
  have hZ : 0 < Z := caseIIThresholdCoefficient_pos hH0 hC0
  have hZeq : Z + 2 = 24 * (d : ℝ) * D₀ * M + 3 := by
    dsimp only [Z, H, C, caseIIThresholdCoefficient]
    rw [hnorm]
    ring
  have hfactor : (d : ℝ) * ‖e‖ * (D₀ - -D₀) * (3 * M * ε) / (Z * ε) +
      ((2 * ε) ^ 2 / (2 * ε) ^ 2) * (3 * M * ε) ^ 2 ≤ 1 / 2 :=
    caseII_mesh_scaled_contraction hH0 hC0 hε hsmall.le
  have hlength : ∀ a b : R, T.adj a b → ‖T.pos b - T.pos a‖ ≤ 2 * ε := by
    intro a b hab
    obtain ⟨z, hza, hzb⟩ := hab.2.1
    have h := (dist_triangle (T.pos b) z (T.pos a)).trans
      (add_le_add (hdistR b (hposcell b) hzb) (hdistR a hza (hposcell a)))
    rw [dist_eq_norm] at h
    linarith
  have henergy : ∀ S ⊆ A, ∀ h' : R → ℝ, N.SolvesDirichlet S g h' →
      N.energy (h' - g) ≤ (3 * M * ε) ^ 2 * T.incidentMass R S := by
    intro S hS h' hsol'
    have := energy_error_le_hessian_segment hd T R S h' hC hM0 hsol'
      (fun w hw => hcellDA w (hS hw)) (fun w hw x hwx => hneighbors w (hS hw) x hwx) hW hh
      (fun w => hcells w w.property) hW' hC2
      (fun a b hinc hab => hsegs a a.property b b.property hab
        (hinc.symm.imp (fun h => hS h) (fun h => hS h)))
      hdiamR (fun w => hHcell w w.property)
      (fun a b hinc hab => hHseg a a.property b b.property hab
        (hinc.symm.imp (fun h => hS h) (fun h => hS h)))
    calc _ ≤ _ := this
      _ = (3 * M * ε) ^ 2 * T.incidentMass R S := by ring
  have hdecay := T.harmonicIteration_mass_le_geometric hd R A ha hneighbors hcellDA g e he
    (-D₀) D₀ (by linarith) hheight (C := 3 * M * ε) (τ := Z * ε) (L := 2 * ε) (ℓ := 2 * ε)
    (by positivity) (mul_pos hZ hε) (by positivity) hlength henergy hfactor
  set q := K * Real.log (1 / ε) with hqdef
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hℓ2 : Real.log 2 ≤ Real.log (1 / ε) :=
    Real.log_le_log two_pos (by rw [le_div_iff₀ hε]; linarith)
  have hq : 0 ≤ q := mul_nonneg (zero_le_one.trans hK) (hlog2.le.trans hℓ2)
  set j := geometricVolumeCutoff K' q with hjdef
  let S := (N.harmonicIteration A ha g (fun _ => Z * ε) (fun _ => 2 * ε) j).region
  have hSA : S ⊆ A := N.harmonicIteration_region_antitone A ha g _ _ (Nat.zero_le j)
  have hSsmall : ∀ u ∈ S, (T.cell (u : T.V)).volume.toReal < ε ^ K := by
    intro u hu
    calc
      _ ≤ 2 * T.incidentMass R S := T.cellVolume_le_twice_incidentMass hd R S
        (fun w hw => hneighbors w (hSA hw)) hu (hcellDA u (hSA hu))
      _ ≤ 2 * (T.incidentMass R A * (1 / 2 : ℝ) ^ j) :=
        mul_le_mul_of_nonneg_left (hdecay j) (by norm_num)
      _ = (2 * T.incidentMass R A) * (1 / 2 : ℝ) ^ j := by ring
      _ ≤ K' * (1 / 2 : ℝ) ^ j := mul_le_mul_of_nonneg_right hmass (by positivity)
      _ < Real.exp (-q) := geometric_mass_lt_exp_neg hK'
      _ = ε ^ K := exp_neg_mul_log_inv_full hε
  set η := (j : ℝ) * (Z * ε + 2 * ε) with hηdef
  have hout : ∀ w : R, w ∉ S → |hDR w - g w| ≤ η := by
    intro w hw
    have := N.harmonicIteration_error_outside_of_solves A ha g hDR hsolR (fun _ => Z * ε)
      (fun _ => 2 * ε) (fun _ => by positivity) (fun _ => by positivity) j hw
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using this
  -- the cost of the iteration in the paper's form
  set C₀ := (24 * d * D₀ + 3) * (3 + Real.log K' / Real.log 2) / Real.log 2 with hC₀def
  have hη : η ≤ C₀ * M * K * ε * Real.log (1 / ε) := by
    have hj : (j : ℝ) ≤ (q + Real.log K') / Real.log 2 + 2 :=
      (geometricVolumeCutoff_lt hK' hq).le
    have ha1 := (one_le_div hlog2).mpr hℓ2
    have hb : 0 ≤ Real.log K' / Real.log 2 :=
      div_nonneg (Real.log_nonneg hK') hlog2.le
    have hfac := rate_factor_le_full hK ha1 hb
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hA : 24 * d * D₀ * M + 3 ≤ (24 * d * D₀ + 3) * M := by nlinarith
    have hB : (q + Real.log K') / Real.log 2 + 2 ≤
        (3 + Real.log K' / Real.log 2) * (K * (Real.log (1 / ε) / Real.log 2)) := by
      rw [hqdef]
      calc _ = K * (Real.log (1 / ε) / Real.log 2) + Real.log K' / Real.log 2 + 2 := by ring
        _ ≤ _ := hfac
    have hA0 : 0 ≤ 24 * d * D₀ * M + 3 := by
      have : 0 ≤ 24 * d * D₀ * M := by positivity
      linarith
    calc η = (j : ℝ) * ((Z + 2) * ε) := by rw [hηdef]; ring
      _ = (24 * d * D₀ * M + 3) * ((j : ℝ) * ε) := by rw [hZeq]; ring
      _ ≤ ((24 * d * D₀ + 3) * M) *
          ((3 + Real.log K' / Real.log 2) * (K * (Real.log (1 / ε) / Real.log 2)) * ε) := by
        gcongr
        exact hj.trans hB
      _ = C₀ * M * K * ε * Real.log (1 / ε) := by
        rw [hC₀def]
        field_simp
  set C₁ := 4 * (D₀ + 1) / Real.log 2 with hC₁def
  have hlogε : 0 ≤ Real.log (1 / ε) := hlog2.le.trans hℓ2
  have hC₁0 : 0 ≤ C₁ := div_nonneg (by linarith) hlog2.le
  have hfinal : ∀ x : ℝ, x ≤ η + (Dc * L + C₁ * M * K * ε * Real.log (1 / ε)) →
      x ≤ (C₀ + C₁) * M * K * ε * Real.log (1 / ε) + Dc * L := by
    intro x hx
    have := hη
    linarith
  apply hfinal
  by_cases hvS : vR ∈ S
  swap
  · have h1 := hout vR hvS
    have h2 : 0 ≤ Dc * L + C₁ * M * K * ε * Real.log (1 / ε) := by
      have : 0 ≤ C₁ * M * K * ε * Real.log (1 / ε) := by
        have := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC₁0 hM0)
          (zero_le_one.trans hK)) hε.le) hlogε
        linarith
      linarith [mul_nonneg hDc0 hL0]
    change |hDR vR - g vR| ≤ _
    linarith
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
  have hQA : Q ⊆ A := hQS.trans hSA
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
      list_sum_le_finset_sum p'.property.support_nodup
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
        lipschitz_on_convex hW hh.contDiffOn (T.cell x).convex (hcells x hx) (hLgrad x hx)
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
    have h1 : ‖T.pos (w : T.V)‖ ≤ D₀ :=
      mem_closedBall_zero_iff.mp (hcellR w (hposcell w))
    have h2 : ‖T.pos v‖ ≤ D₀ := mem_closedBall_zero_iff.mp (hcellR vR (hposcell v))
    calc ‖T.pos w - T.pos v‖ ≤ ‖T.pos (w : T.V)‖ + ‖T.pos v‖ := norm_sub_le _ _
      _ ≤ 2 * D₀ := by linarith
  have hlapQ : ∀ u ∈ Q, |N.laplacian g u| ≤
      M * ∑ w : R, N.a u w * ‖T.pos w - T.pos u‖ ^ 2 := by
    intro u hu
    exact abs_laplacian_le hd T U u (hQA hu) (hcellD u (hQA hu)) hW' hC2 hM0
      (fun w hw => hsegs u u.property w w.property hw (Or.inl (hQA hu)))
      (fun w hw => hHseg u u.property w w.property hw (Or.inl (hQA hu)))
  have hsq : ∀ u ∈ Q, N.laplacian (fun w : R => ‖T.pos w - T.pos v‖ ^ 2) u =
      ∑ w : R, N.a u w * ‖T.pos w - T.pos u‖ ^ 2 := fun u hu =>
    laplacian_sq_dist hd T U u (hQA hu) (hcellD u (hQA hu)) (T.pos v)
  have hbdry : ∀ w ∈ N.externalBoundary Q,
      |hDR w - g w| + M * ‖T.pos w - T.pos v‖ ^ 2 ≤ η + M * ρ ^ 2 := by
    intro w hw
    have h1 := hout w (hext w hw).1
    have h2 : ‖T.pos w - T.pos v‖ ^ 2 ≤ ρ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hρw w hw) 2
    exact add_le_add h1 (mul_le_mul_of_nonneg_left h2 hM0)
  have hup : hDR vR - g vR ≤ η + M * ρ ^ 2 := by
    have := N.local_maximum_principle Q hQacc
      (fun w : R => (hDR w - g w) + M * ‖T.pos w - T.pos v‖ ^ 2) (η + M * ρ ^ 2)
      (fun u hu => by
        have hL := N.laplacian_add (hDR - g) (fun w : R => M * ‖T.pos w - T.pos v‖ ^ 2) u
        have hS := N.laplacian_sub hDR g u
        have hcm : N.laplacian (fun w : R => M * ‖T.pos w - T.pos v‖ ^ 2) u =
            M * N.laplacian (fun w : R => ‖T.pos w - T.pos v‖ ^ 2) u :=
          N.laplacian_smul M (fun w : R => ‖T.pos w - T.pos v‖ ^ 2) u
        have h0 : N.laplacian hDR u = 0 := hsolR.1 u (hQA hu)
        have habs := abs_le.mp (hlapQ u hu)
        change 0 ≤ N.laplacian ((hDR - g) + fun w : R => M * ‖T.pos w - T.pos v‖ ^ 2) u
        rw [hL, hS, h0, hcm, hsq u hu]
        linarith [habs.2])
      (fun w hw => by
        have := hbdry w hw
        have := le_abs_self (hDR w - g w)
        linarith) vR hvQ
    have h0 : ‖T.pos (vR : T.V) - T.pos v‖ ^ 2 = 0 := by
      show ‖T.pos v - T.pos v‖ ^ 2 = 0
      simp
    simp only [h0, mul_zero, add_zero] at this
    exact this
  have hlow : -(hDR vR - g vR) ≤ η + M * ρ ^ 2 := by
    have := N.local_maximum_principle Q hQacc
      (fun w : R => -(hDR w - g w) + M * ‖T.pos w - T.pos v‖ ^ 2) (η + M * ρ ^ 2)
      (fun u hu => by
        have hL := N.laplacian_add (-(hDR - g)) (fun w : R => M * ‖T.pos w - T.pos v‖ ^ 2) u
        have hN := N.laplacian_neg (hDR - g) u
        have hS := N.laplacian_sub hDR g u
        have hcm : N.laplacian (fun w : R => M * ‖T.pos w - T.pos v‖ ^ 2) u =
            M * N.laplacian (fun w : R => ‖T.pos w - T.pos v‖ ^ 2) u :=
          N.laplacian_smul M (fun w : R => ‖T.pos w - T.pos v‖ ^ 2) u
        have h0 : N.laplacian hDR u = 0 := hsolR.1 u (hQA hu)
        have habs := abs_le.mp (hlapQ u hu)
        change 0 ≤ N.laplacian ((-(hDR - g)) + fun w : R => M * ‖T.pos w - T.pos v‖ ^ 2) u
        rw [hL, hN, hS, h0, hcm, hsq u hu]
        linarith [habs.1])
      (fun w hw => by
        have := hbdry w hw
        have := neg_abs_le (hDR w - g w)
        linarith) vR hvQ
    have h0 : ‖T.pos (vR : T.V) - T.pos v‖ ^ 2 = 0 := by
      show ‖T.pos v - T.pos v‖ ^ 2 = 0
      simp
    simp only [h0, mul_zero, add_zero] at this
    exact this
  have hquad : |hDR vR - g vR| ≤ η + M * ρ ^ 2 := abs_le.mpr ⟨by linarith, hup⟩
  -- the case analysis
  have hcase := component_case_bound (x := |hDR vR - g vR| - η) (R := D₀) hL0 hM0 hε hε2 hK hD₀
    hDq0 hDq hρ0 (min_le_left _ _) (min_le_right _ _) (by linarith) (by linarith)
  change |hDR vR - g vR| ≤ _
  rw [hC₁def]
  linarith

end SpherePackings
