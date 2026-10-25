module

-- Built on Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne (commit cf73d6e).
public import SpherePackings.Support.Section3.InternalTaylor
public import SpherePackings.Support.Section3.PlanarQuadratic
public import SpherePackings.Support.Complete.Section3

@[expose] public section

/-!
# Theorem 3.3 as in the corrected paper

`rw-spheres-corrected.tex`, Theorem 3.3: in the plane, with `ε` the maximal cell diameter, `M₀` the
Hessian bound of `h_C` on the cells of `V̄[U]` and `M ≥ M₀` the finite Taylor constant of the
internal edges (both endpoints in `V[U]`),
`sup_{V[U]} |h_D - h_C| ≤ 3 M₀ ε² + inf_{k > 0} (6 k M ε vol(Û) + (M/2)(√2 k⁻¹ + ε)²)`, and for
`ε ≤ 1/2` the rate `C ε^{2/3}` (hence `C ε^{1/2}`), `C = M (3 + 6 vol(B_{R₀+1}) + (√2 + 1)²/2)`.
No local oscillation or Lipschitz condition.  The cells of `V[U]` are complete; `h_C` is `C²` near
the cells and harmonic on the cells of `V[U]`.

Proof.  Split `h_D - h_C = b + f₀` (`InternalTaylor.lean`): `|b| ≤ 2 M₀ ε²`; the energy of `f₀`
gives good rectangles through the column bound (Lemma 3.1); `±f₀ + (M/2) ‖· - v‖²` is
subharmonic on the cells inside a good rectangle, whose boundary values are at most the threshold.
-/

namespace SpherePackings

open BouRabeeGwynne BouRabeeGwynne.OrthogonalTiling

open scoped Classical MeasureTheory ENNReal Laplacian

/-- The incident mass of the interior is at most twice the volume of `Û`. -/
theorem incidentMass_le_two_volume (T : OrthogonalTiling 2) (U : Set (Euc 2))
    [Fintype (T.closedVertices U)] :
    T.incidentMass (T.closedVertices U) (T.finiteInterior U) ≤
      2 * (MeasureTheory.volume (⋃ w ∈ T.closedVertices U, (T.cell w).carrier)).toReal := by
  have hUhat_eq : (⋃ w ∈ T.closedVertices U, (T.cell w).carrier) =
      ⋃ w : T.closedVertices U, (T.cell (w : T.V)).carrier := by
    rw [Set.biUnion_eq_iUnion]
  have hUhatc : IsCompact (⋃ w ∈ T.closedVertices U, (T.cell w).carrier) := by
    rw [hUhat_eq]
    exact isCompact_iUnion fun w => (T.cell (w : T.V)).compact
  have hm : (μHE[2] : MeasureTheory.Measure (Euc 2)) = MeasureTheory.volume := by
    simpa using InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := Euc 2)
  have hUfinite : μHE[2] (⋃ w ∈ T.closedVertices U, (T.cell w).carrier) ≠ ⊤ := by
    rw [hm]
    exact hUhatc.measure_lt_top.ne
  have hmass := T.incidentMass_le_dim_mul_volume (d := 2) (by norm_num) (T.closedVertices U)
    (T.finiteInterior U) hUfinite
    (fun w => by
      rw [hUhat_eq]
      exact Set.subset_iUnion (fun w : T.closedVertices U => (T.cell (w : T.V)).carrier) w)
  rw [hm] at hmass
  simpa using hmass

/-- Letting the slack `δ` go to zero: a bound `x ≤ η + c (ε + √2 (1/k + δ))²` for every `δ > 0`
gives it at `δ = 0`. -/
theorem le_of_slack_sq {x η c ε k : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε) (hk : 0 < k)
    (h : ∀ δ : ℝ, 0 < δ → x ≤ η + c * (ε + Real.sqrt 2 * (1 / k + δ)) ^ 2) :
    x ≤ η + c * (ε + Real.sqrt 2 * (1 / k)) ^ 2 := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  -- the slack `d ≤ 1` with `c (2 √2 a + 2) d ≤ δ`, where `a = ε + √2 / k`
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = c * (2 * Real.sqrt 2 * (ε + Real.sqrt 2 * (1 / k)) + 2) :=
    ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by rw [hCdef]; positivity
  obtain ⟨d, hd0, hd1, hdδ⟩ : ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ C * d ≤ δ := by
    have hc1 : 0 < C + 1 := by linarith
    have h1 := (le_div_iff₀ hc1).mp (min_le_right 1 (δ / (C + 1)))
    refine ⟨min 1 (δ / (C + 1)), lt_min one_pos (div_pos hδ hc1), min_le_left _ _, ?_⟩
    have h2 : 0 ≤ min 1 (δ / (C + 1)) := le_min zero_le_one (div_nonneg hδ.le hc1.le)
    nlinarith
  have hmain := h d hd0
  have hsq : (ε + Real.sqrt 2 * (1 / k + d)) ^ 2 =
      (ε + Real.sqrt 2 * (1 / k)) ^ 2 + 2 * (ε + Real.sqrt 2 * (1 / k)) * Real.sqrt 2 * d +
        2 * d ^ 2 := by
    linear_combination d ^ 2 * hs2
  have hd2 : d ^ 2 ≤ d := by nlinarith
  have hineq : (ε + Real.sqrt 2 * (1 / k + d)) ^ 2 ≤
      (ε + Real.sqrt 2 * (1 / k)) ^ 2 +
        d * (2 * Real.sqrt 2 * (ε + Real.sqrt 2 * (1 / k)) + 2) := by
    rw [hsq]
    nlinarith
  have hcm := mul_le_mul_of_nonneg_left hineq hc
  rw [hCdef] at hdδ
  nlinarith

/-- The box step of Theorem 3.3 for a corrected error `φ` whose Laplacian is bounded by
`(M/2) ∑ a(u, w) ‖w - u‖²` on `V[U]`: at `v` in a good box, `|φ v|` is at most the threshold `η`
plus `(M/2) (ε + D)²`, `D` bounding the diameter of the box. -/
theorem abs_le_box_internal (T : OrthogonalTiling 2) (U : Set (Euc 2))
    [Fintype (T.closedVertices U)]
    (hcomplete : ∀ v ∈ T.interiorVertices U, CompleteCell T v)
    {M : ℝ} (hM : 0 ≤ M)
    (ha : (T.finiteNetwork (T.closedVertices U)).BoundaryAccessible (T.finiteInterior U))
    (φ : T.closedVertices U → ℝ)
    (hφ : ∀ u ∈ T.finiteInterior U,
      |(T.finiteNetwork (T.closedVertices U)).laplacian φ u| ≤
        M / 2 * ∑ w : T.closedVertices U,
          (T.finiteNetwork (T.closedVertices U)).a u w * ‖T.pos w - T.pos u‖ ^ 2)
    (hzero : ∀ w : T.closedVertices U, w ∉ T.finiteInterior U → φ w = 0)
    {I : Type*} (L : I → Euc 2 →L[ℝ] ℝ) (lower upper : I → ℝ) {η D ε : ℝ} (hη : 0 ≤ η)
    (hgood : ∀ w ∈ T.finiteInterior U, (∃ i, ∃ x ∈ (T.cell (w : T.V)).carrier,
      L i x = lower i ∨ L i x = upper i) → |φ w| ≤ η)
    (hdiamR : ∀ w : T.closedVertices U, Metric.diam (T.cell (w : T.V)).carrier ≤ ε)
    (hdiam : ∀ x ∈ slabIntersection L lower upper, ∀ y ∈ slabIntersection L lower upper,
      dist x y ≤ D)
    {v : T.closedVertices U} (hvA : v ∈ T.finiteInterior U)
    (hvS : T.pos v ∈ slabIntersection L lower upper) :
    |φ v| ≤ η + M / 2 * (ε + D) ^ 2 := by
  let R := T.closedVertices U
  let A : Set R := T.finiteInterior U
  let N := T.finiteNetwork R
  let B := T.cellsContainedInterior R A (slabIntersection L lower upper)
  by_cases hvB : v ∈ B
  · have hBA : B ⊆ A := T.cellsContainedInterior_subset R A _
    have hdistB : ∀ w ∈ N.externalBoundary B, ‖T.pos w - T.pos v‖ ≤ ε + D := by
      intro w hw
      obtain ⟨u, hu, hau⟩ := hw.2
      have huw : T.adj u w := T.conductanceReal_pos_iff.mp hau
      obtain ⟨z, hzu, hzw⟩ := huw.2.1
      rw [← dist_eq_norm]
      calc
        _ ≤ dist (T.pos w) z + dist z (T.pos v) := dist_triangle _ _ _
        _ ≤ ε + D := add_le_add
          ((Metric.dist_le_diam_of_mem (T.cell _).compact.isBounded
            (interior_subset (T.pos_mem_interior _)) hzw).trans (hdiamR w))
          (hdiam z (hu.2 hzu) (T.pos v) hvS)
    have hbdry : ∀ w ∈ N.externalBoundary B,
        |φ w| + M / 2 * ‖T.pos w - T.pos v‖ ^ 2 ≤ η + M / 2 * (ε + D) ^ 2 := by
      intro w hw
      have hsq : ‖T.pos w - T.pos v‖ ^ 2 ≤ (ε + D) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hdistB w hw) 2
      have hφw : |φ w| ≤ η := by
        by_cases hwA : w ∈ A
        · exact hgood w hwA (T.boundary_cell_meets_cut R A L lower upper hw hwA)
        · rw [hzero w hwA, abs_zero]
          exact hη
      exact add_le_add hφw (mul_le_mul_of_nonneg_left hsq (div_nonneg hM zero_le_two))
    have hlap : ∀ u ∈ B, |N.laplacian φ u| ≤
        M / 2 * N.laplacian (fun w : R => ‖T.pos w - T.pos v‖ ^ 2) u := by
      intro u hu
      have hq := laplacian_sq_dist_of_complete (by norm_num) T U u (hBA hu)
        (hcomplete u (hBA hu)) (T.pos v)
      rw [hq]
      exact hφ u (hBA hu)
    have hB : N.BoundaryAccessible B := N.boundaryAccessible_mono hBA ha
    have hqv : 0 ≤ M / 2 * (fun w : R => ‖T.pos w - T.pos v‖ ^ 2) v :=
      mul_nonneg (div_nonneg hM zero_le_two) (sq_nonneg _)
    exact abs_le_of_abs_laplacian_le N B hB φ (fun w : R => ‖T.pos w - T.pos v‖ ^ 2) hlap hbdry
      hvB hqv
  · have hcut := (T.cell v).exists_cut_of_not_subset L lower upper
      (interior_subset (T.pos_mem_interior v)) hvS (fun hsub => hvB ⟨hvA, hsub⟩)
    exact (hgood v hvA hcut).trans
      (le_add_of_nonneg_right (mul_nonneg (div_nonneg hM zero_le_two) (sq_nonneg _)))

/-- The slack step of Theorem 3.3: for every `δ > 0`, the corrected error `φ` at `v ∈ A` is at most
`η + (M/2) (ε + √2 (1/k + δ))²`, when every column of the lift of `φ` is good at the threshold `η`
outside a set of measure `≤ 1/k`. -/
theorem abs_le_slack_internal (T : OrthogonalTiling 2) (U : Set (Euc 2))
    [Fintype (T.closedVertices U)]
    (hcomplete : ∀ v ∈ T.interiorVertices U, CompleteCell T v)
    {M ε k η : ℝ} (hM : 0 ≤ M) (hk : 0 < k) (hη : 0 ≤ η)
    (hdiam : ∀ v ∈ T.closedVertices U, Metric.diam (T.cell v).carrier ≤ ε)
    (ha : (T.finiteNetwork (T.closedVertices U)).BoundaryAccessible (T.finiteInterior U))
    (φ : T.closedVertices U → ℝ)
    (hφ : ∀ u ∈ T.finiteInterior U,
      |(T.finiteNetwork (T.closedVertices U)).laplacian φ u| ≤
        M / 2 * ∑ w : T.closedVertices U,
          (T.finiteNetwork (T.closedVertices U)).a u w * ‖T.pos w - T.pos u‖ ^ 2)
    (hzero : ∀ w : T.closedVertices U, w ∉ T.finiteInterior U → φ w = 0)
    (hbad : ∀ i : Fin 2, μHE[1] (T.columnBadSet (T.closedVertices U) (T.finiteInterior U)
      (coordinateAxis i.rev) (coordinateAxis_ne_zero i.rev)
      (T.finiteAmbientFunction (T.closedVertices U) φ) η) ≤ ENNReal.ofReal (1 / k))
    {v : T.closedVertices U} (hvA : v ∈ T.finiteInterior U) (δ : ℝ) (hδ : 0 < δ) :
    |φ v| ≤ η + M / 2 * (ε + Real.sqrt 2 * (1 / k + δ)) ^ 2 := by
  let R := T.closedVertices U
  let A : Set R := T.finiteInterior U
  have hdiamR : ∀ w : R, Metric.diam (T.cell (w : T.V)).carrier ≤ ε :=
    fun w => hdiam w w.property
  have hcuts : ∀ i : Fin 2, ∃ a b : ℝ, a ≤ T.pos v i ∧ T.pos v i ≤ b ∧ b - a ≤ 1 / k + δ ∧
      a • coordinateAxis i ∉ T.columnBadSet R A (coordinateAxis i.rev)
        (coordinateAxis_ne_zero i.rev) (T.finiteAmbientFunction R φ) η ∧
      b • coordinateAxis i ∉ T.columnBadSet R A (coordinateAxis i.rev)
        (coordinateAxis_ne_zero i.rev) (T.finiteAmbientFunction R φ) η := fun i =>
    exists_unitLine_cuts_around (norm_coordinateAxis i) _ (by positivity) hδ (hbad i) _
  choose lower upper hlo hhi hlen hlgood hugood using hcuts
  have hω : 0 ≤ M / 2 * (ε + Real.sqrt 2 * (1 / k + δ)) ^ 2 :=
    mul_nonneg (div_nonneg hM zero_le_two) (sq_nonneg _)
  -- a cut through the cell of `v`
  by_cases hdeg : ∃ i, lower i = T.pos v i ∨ upper i = T.pos v i
  · obtain ⟨i, hi | hi⟩ := hdeg
    · have := T.abs_le_of_good_planar_cut R A (T.finiteAmbientFunction R φ) η i (lower i)
        (hlgood i) hvA (interior_subset (T.pos_mem_interior v)) hi.symm
      rw [T.finiteAmbientFunction_apply] at this
      linarith
    · have := T.abs_le_of_good_planar_cut R A (T.finiteAmbientFunction R φ) η i (upper i)
        (hugood i) hvA (interior_subset (T.pos_mem_interior v)) hi.symm
      rw [T.finiteAmbientFunction_apply] at this
      linarith
  push Not at hdeg
  have hvbox : T.pos v ∈
      slabIntersection (fun i => innerSL ℝ (coordinateAxis i)) lower upper := by
    intro i
    change lower i < inner ℝ (coordinateAxis i) (T.pos v) ∧
      inner ℝ (coordinateAxis i) (T.pos v) < upper i
    rw [inner_coordinateAxis]
    exact ⟨lt_of_le_of_ne (hlo i) (hdeg i).1, lt_of_le_of_ne (hhi i) (fun h => (hdeg i).2 h.symm)⟩
  have hgoodF : ∀ w ∈ A, (∃ i, ∃ x ∈ (T.cell (w : T.V)).carrier,
      (fun i => innerSL ℝ (coordinateAxis i)) i x = lower i ∨
        (fun i => innerSL ℝ (coordinateAxis i)) i x = upper i) → |φ w| ≤ η := by
    rintro w hw ⟨i, x, hx, hcut | hcut⟩
    · simp only [innerSL_apply_apply, inner_coordinateAxis] at hcut
      have := T.abs_le_of_good_planar_cut R A (T.finiteAmbientFunction R φ) η i (lower i)
        (hlgood i) hw hx hcut
      rwa [T.finiteAmbientFunction_apply] at this
    · simp only [innerSL_apply_apply, inner_coordinateAxis] at hcut
      have := T.abs_le_of_good_planar_cut R A (T.finiteAmbientFunction R φ) η i (upper i)
        (hugood i) hw hx hcut
      rwa [T.finiteAmbientFunction_apply] at this
  have hdistbox := planar_box_dist_le lower upper (s := 1 / k + δ) (by positivity) hlen
  exact abs_le_box_internal T U hcomplete hM ha φ hφ hzero (fun i => innerSL ℝ (coordinateAxis i))
    lower upper hη hgoodF hdiamR hdistbox hvA hvbox

/-- **Theorem 3.3** (`theorem:2d`), the displayed bound, as in the corrected paper. -/
theorem planar_dirichlet_bound_internal (T : OrthogonalTiling 2) (U : Set (Euc 2))
    [Fintype (T.closedVertices U)]
    (hcomplete : ∀ v ∈ T.interiorVertices U, CompleteCell T v)
    {W : Set (Euc 2)} (hW : IsOpen W) {hC : Euc 2 → ℝ} (hC2 : ContDiffOn ℝ 2 hC W)
    (hcells : ∀ v ∈ T.closedVertices U, (T.cell v).carrier ⊆ W)
    (hharm : ∀ v ∈ T.interiorVertices U, ∀ x ∈ (T.cell v).carrier, Δ hC x = 0)
    {M₀ M ε : ℝ} (hM₀ : 0 ≤ M₀) (hM₀M : M₀ ≤ M) (hε : 0 ≤ ε)
    (hdiam : ∀ v ∈ T.closedVertices U, Metric.diam (T.cell v).carrier ≤ ε)
    (hHcell : ∀ v ∈ T.closedVertices U, ∀ x ∈ (T.cell v).carrier,
      ‖fderiv ℝ (fderiv ℝ hC) x‖ ≤ M₀)
    (hTaylor : ∀ v ∈ T.interiorVertices U, ∀ w ∈ T.interiorVertices U, T.adj v w →
      |hC (T.pos w) - hC (T.pos v) - (fderiv ℝ hC (T.pos v)) (T.pos w - T.pos v)| ≤
        M / 2 * ‖T.pos w - T.pos v‖ ^ 2)
    (hD : T.V → ℝ) (hsol : T.SolvesDirichlet U (fun v => hC (T.pos v)) hD) :
    ∀ k : ℝ, 0 < k → ∀ v ∈ T.interiorVertices U, |hD v - hC (T.pos v)| ≤
      3 * M₀ * ε ^ 2 + (6 * k * M * ε * (MeasureTheory.volume (⋃ w ∈ T.closedVertices U,
        (T.cell w).carrier)).toReal + M / 2 * (Real.sqrt 2 / k + ε) ^ 2) := by
  intro k hk v hv
  have hMnn : 0 ≤ M := hM₀.trans hM₀M
  let R := T.closedVertices U
  let A : Set R := T.finiteInterior U
  let vR : R := ⟨v, T.interiorVertices_subset_closedVertices U hv⟩
  have hvA : vR ∈ A := hv
  have hneighborsA : ∀ w ∈ A, ∀ x, T.adj (w : T.V) x → x ∈ R := fun w hw x hwx =>
    T.neighbor_mem_closedVertices (show (w : T.V) ∈ T.interiorVertices U from hw) hwx
  have hcompleteA : ∀ w ∈ A, CompleteCell T (w : T.V) := fun w hw => hcomplete (w : T.V) hw
  have ha : (T.finiteNetwork R).BoundaryAccessible A :=
    finiteNetwork_boundaryAccessible_of_complete (by norm_num) T (coordinateAxis 0)
      (coordinateAxis_ne_zero 0) R A hneighborsA hcompleteA
  have hsolR := T.solvesDirichlet_restrict hsol
  have htaylorA : ∀ x ∈ A, ∀ y ∈ A, T.adj (x : T.V) (y : T.V) →
      |T.surfaceTaylorRemainder hC x y| ≤ M / 2 * ‖T.pos y - T.pos x‖ ^ 2 :=
    fun x hx y hy hxy => hTaylor (x : T.V) hx (y : T.V) hy hxy
  have hHcellM : ∀ x : R, ∀ y ∈ (T.cell (x : T.V)).carrier,
      ‖fderiv ℝ (fderiv ℝ hC) y‖ ≤ M :=
    fun x y hy => (hHcell (x : T.V) x.property y hy).trans hM₀M
  have hHcellR : ∀ x : R, ∀ y ∈ (T.cell (x : T.V)).carrier,
      ‖fderiv ℝ (fderiv ℝ hC) y‖ ≤ M₀ :=
    fun x y hy => hHcell (x : T.V) x.property y hy
  have hdiamR : ∀ x : R, Metric.diam (T.cell (x : T.V)).carrier ≤ ε :=
    fun x => hdiam (x : T.V) x.property
  have hcellR : ∀ x : R, (T.cell (x : T.V)).carrier ⊆ W :=
    fun x => hcells (x : T.V) x.property
  -- the corrected error `f₀ = (h_D - h_C) - b`, with `b` the boundary correction
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : R → ℝ, f₀ = ((fun w : R => hD w) - fun w : R => hC (T.pos w)) -
      (T.finiteNetwork R).boundaryCorrection A ha (fun v w => T.surfaceTaylorRemainder hC v w) :=
    ⟨_, rfl⟩
  have hEn : (T.finiteNetwork R).energy f₀ ≤ 9 * M ^ 2 * ε ^ 2 * T.incidentMass R A := by
    rw [hf₀]
    exact energy_boundaryCorrected_le_internal (by norm_num) T R A ha (fun w : R => hD w) hC
      hMnn hsolR (fun x _ => hdiamR x) hcompleteA hneighborsA hW hC2 (fun x _ => hcellR x)
      (fun x hx y hy => hharm (x : T.V) hx y hy) (fun x _ y hy => hHcellM x y hy) htaylorA
  have hlap : ∀ u ∈ A, |(T.finiteNetwork R).laplacian f₀ u| ≤
      M / 2 * ∑ w : R, (T.finiteNetwork R).a u w * ‖T.pos w - T.pos u‖ ^ 2 := by
    intro u hu
    rw [hf₀]
    exact abs_laplacian_boundaryCorrected_le (by norm_num) T U A subset_rfl ha
      (fun w : R => hD w) hC hsolR hcompleteA hMnn htaylorA hu
  have hzeroA : ∀ w : R, w ∉ A → f₀ w = 0 := by
    intro w hw
    have hw' : hD (w : T.V) = hC (T.pos w) := hsolR.2 w hw
    rw [hf₀]
    simp only [Pi.sub_apply]
    rw [hw', sub_self, (T.finiteNetwork R).boundaryCorrection_boundary A ha _ hw, sub_zero]
  -- the bad columns of the lift of `f₀`, at the threshold `η = 3 k M ε K`
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = 3 * k * M * ε * T.incidentMass R A := ⟨_, rfl⟩
  have hη0 : 0 ≤ η := by
    rw [hη]
    exact mul_nonneg (by positivity) (T.incidentMass_nonneg R A)
  have hbad : ∀ i : Fin 2, μHE[1] (T.columnBadSet R A (coordinateAxis i.rev)
      (coordinateAxis_ne_zero i.rev) (T.finiteAmbientFunction R f₀) η) ≤
      ENNReal.ofReal (1 / k) := by
    intro i
    have hzeroF : ∀ w : R, w ∉ A → T.finiteAmbientFunction R f₀ (w : T.V) = 0 := fun w hw => by
      rw [T.finiteAmbientFunction_apply]
      exact hzeroA w hw
    have henF : T.incidentEnergy R A (T.finiteAmbientFunction R f₀) ≤
        (3 * M * ε) ^ 2 * T.incidentMass R A := by
      rw [T.incidentEnergy_eq_networkEnergy R A (T.finiteAmbientFunction R f₀) hzeroF]
      have hfun : (fun w : R => T.finiteAmbientFunction R f₀ (w : T.V)) = f₀ :=
        funext fun w => T.finiteAmbientFunction_apply R f₀ w
      rw [hfun]
      calc (T.finiteNetwork R).energy f₀ ≤ 9 * M ^ 2 * ε ^ 2 * T.incidentMass R A := hEn
        _ = (3 * M * ε) ^ 2 * T.incidentMass R A := by ring
    have hcol := column_poincare_of_energy_bound_of_complete (by norm_num) T
      (coordinateAxis i.rev) (coordinateAxis_ne_zero i.rev) R A hneighborsA hcompleteA
      (T.finiteAmbientFunction R f₀) hzeroF (by positivity : (0 : ℝ) ≤ 3 * M * ε) hk henF
    rw [show k * (3 * M * ε) * T.incidentMass R A = η by rw [hη]; ring] at hcol
    exact hcol
  have hslack : ∀ δ : ℝ, 0 < δ →
      |f₀ vR| ≤ η + M / 2 * (ε + Real.sqrt 2 * (1 / k + δ)) ^ 2 :=
    fun δ hδ => abs_le_slack_internal T U hcomplete hMnn hk hη0 hdiam ha f₀ hlap hzeroA hbad
      hvA δ hδ
  have hlim := le_of_slack_sq (x := |f₀ vR|) (c := M / 2) (η := η) (ε := ε) (k := k)
    (by positivity) hε hk hslack
  have hsqrt : Real.sqrt 2 / k + ε = ε + Real.sqrt 2 * (1 / k) := by ring
  have hlim' : |f₀ vR| ≤ η + M / 2 * (Real.sqrt 2 / k + ε) ^ 2 := by
    rw [hsqrt]
    exact hlim
  -- the volume of `Û` and the boundary correction
  have hηvol : η ≤ 6 * k * M * ε *
      (MeasureTheory.volume (⋃ w ∈ T.closedVertices U, (T.cell w).carrier)).toReal := by
    have h0 : 0 ≤ 3 * k * M * ε := by positivity
    calc η = 3 * k * M * ε * T.incidentMass R A := hη
      _ ≤ 3 * k * M * ε * (2 * (MeasureTheory.volume
            (⋃ w ∈ T.closedVertices U, (T.cell w).carrier)).toReal) :=
          mul_le_mul_of_nonneg_left (incidentMass_le_two_volume T U) h0
      _ = 6 * k * M * ε * (MeasureTheory.volume
            (⋃ w ∈ T.closedVertices U, (T.cell w).carrier)).toReal := by ring
  obtain ⟨bv, hbv⟩ : ∃ bv : ℝ, bv = (T.finiteNetwork R).boundaryCorrection A ha
      (fun v w => T.surfaceTaylorRemainder hC v w) vR := ⟨_, rfl⟩
  have hsplit : hD v - hC (T.pos v) = f₀ vR + bv := by
    rw [hf₀, hbv]
    simp only [Pi.sub_apply]
    ring
  have htri : |hD v - hC (T.pos v)| ≤ |f₀ vR| + |bv| := by
    rw [hsplit]
    exact abs_add_le _ _
  have hb : |bv| ≤ 2 * M₀ * ε ^ 2 := by
    rw [hbv]
    exact boundaryCorrection_abs_le_cells T R A ha hC hW hC2 hcellR hM₀ hdiamR hHcellR vR
  have hM0ε : 0 ≤ M₀ * ε ^ 2 := mul_nonneg hM₀ (sq_nonneg _)
  linarith [htri, hlim', hηvol, hb, hM0ε]

/-- **Theorem 3.3** (`theorem:2d`), the rate, as in the corrected paper: for `ε ≤ 1/2`,
`sup_{V[U]} |h_D - h_C| ≤ C ε^{2/3}` with `C = M (3 + 6 vol(B_{R₀+1}) + (√2 + 1)²/2)`. -/
theorem planar_rate_internal (T : OrthogonalTiling 2) (U : Set (Euc 2))
    [Fintype (T.closedVertices U)]
    (hcomplete : ∀ v ∈ T.interiorVertices U, CompleteCell T v)
    {R₀ : ℝ} (hUR : ∀ x ∈ U, ‖x‖ ≤ R₀)
    {W : Set (Euc 2)} (hW : IsOpen W) {hC : Euc 2 → ℝ} (hC2 : ContDiffOn ℝ 2 hC W)
    (hcells : ∀ v ∈ T.closedVertices U, (T.cell v).carrier ⊆ W)
    (hharm : ∀ v ∈ T.interiorVertices U, ∀ x ∈ (T.cell v).carrier, Δ hC x = 0)
    {M₀ M ε : ℝ} (hM₀ : 0 ≤ M₀) (hM₀M : M₀ ≤ M) (hε : 0 ≤ ε) (hε2 : ε ≤ 1 / 2)
    (hdiam : ∀ v ∈ T.closedVertices U, Metric.diam (T.cell v).carrier ≤ ε)
    (hHcell : ∀ v ∈ T.closedVertices U, ∀ x ∈ (T.cell v).carrier,
      ‖fderiv ℝ (fderiv ℝ hC) x‖ ≤ M₀)
    (hTaylor : ∀ v ∈ T.interiorVertices U, ∀ w ∈ T.interiorVertices U, T.adj v w →
      |hC (T.pos w) - hC (T.pos v) - (fderiv ℝ hC (T.pos v)) (T.pos w - T.pos v)| ≤
        M / 2 * ‖T.pos w - T.pos v‖ ^ 2)
    (hD : T.V → ℝ) (hsol : T.SolvesDirichlet U (fun v => hC (T.pos v)) hD) :
    ∀ v ∈ T.interiorVertices U, |hD v - hC (T.pos v)| ≤
      M * (3 + 6 * (MeasureTheory.volume (Metric.closedBall (0 : Euc 2) (R₀ + 1))).toReal +
        (Real.sqrt 2 + 1) ^ 2 / 2) * ε ^ ((2 : ℝ) / 3) := by
  intro v hv
  -- `ε > 0`, since the cell of `v` has nonempty interior
  have hεpos : 0 < ε := by
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior (T.pos v) (T.pos_mem_interior v)
    let e := coordinateAxis (0 : Fin 2)
    have hnorm : ‖e‖ = 1 := norm_coordinateAxis 0
    have hy : T.pos v + (r / 2) • e ∈ Metric.ball (T.pos v) r := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hnorm, mul_one,
        Real.norm_eq_abs, abs_of_pos (half_pos hr)]
      linarith
    have hdist := (Metric.dist_le_diam_of_mem (T.cell v).compact.isBounded
      (interior_subset (T.pos_mem_interior v)) (interior_subset (hball hy))).trans
        (hdiam v (T.interiorVertices_subset_closedVertices U hv))
    rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, hnorm, mul_one, Real.norm_eq_abs,
      abs_of_pos (half_pos hr)] at hdist
    linarith
  -- the parameter `t = ε^{1/3}`, so `k = t⁻¹`, `ε = t³` and `ε^{2/3} = t²`
  set t : ℝ := ε ^ ((1 : ℝ) / 3) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hεpos _
  have ht3 : t ^ 3 = ε := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hε]
    norm_num
  have ht1 : t ≤ 1 := by
    by_contra h
    push Not at h
    have h3 : 1 < t ^ 3 := one_lt_pow₀ h (by norm_num)
    linarith
  have hε23 : ε ^ ((2 : ℝ) / 3) = t ^ 2 := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hε]
    norm_num
  have hεt : ε ≤ t := by
    have ht2 : t ^ 2 ≤ 1 := by nlinarith
    calc ε = t * t ^ 2 := by rw [← ht3]; ring
      _ ≤ t * 1 := mul_le_mul_of_nonneg_left ht2 ht0.le
      _ = t := mul_one t
  have hk' : 0 < t⁻¹ := inv_pos.mpr ht0
  have hbound := planar_dirichlet_bound_internal T U hcomplete hW hC2 hcells hharm hM₀ hM₀M hε
    hdiam hHcell hTaylor hD hsol t⁻¹ hk' v hv
  have e1 : t⁻¹ * ε = t ^ 2 := by
    rw [← ht3]
    calc t⁻¹ * t ^ 3 = t ^ 2 * (t⁻¹ * t) := by ring
      _ = t ^ 2 := by rw [inv_mul_cancel₀ ht0.ne', mul_one]
  have e2 : Real.sqrt 2 / t⁻¹ = Real.sqrt 2 * t := by rw [div_inv_eq_mul]
  rw [e2] at hbound
  -- `vol(Û) ≤ vol(B_{R₀+1})`
  have hsub : (⋃ w ∈ T.closedVertices U, (T.cell w).carrier) ⊆
      Metric.closedBall (0 : Euc 2) (R₀ + 1) := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨w, hw, hxw⟩ := hx
    exact mem_closedBall_zero_iff.mpr (cell_norm_le_of_closedVertices T U hUR hε2 hdiam hw hxw)
  have hvol : (MeasureTheory.volume (⋃ w ∈ T.closedVertices U, (T.cell w).carrier)).toReal ≤
      (MeasureTheory.volume (Metric.closedBall (0 : Euc 2) (R₀ + 1))).toReal :=
    ENNReal.toReal_mono (MeasureTheory.measure_closedBall_lt_top).ne
      (MeasureTheory.measure_mono hsub)
  have hMnn : 0 ≤ M := hM₀.trans hM₀M
  have hM0 : M₀ * ε ^ 2 ≤ M * t ^ 2 := by
    have h2 : ε ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hε hεt 2
    exact mul_le_mul hM₀M h2 (sq_nonneg _) hMnn
  have hterm1 : 6 * t⁻¹ * M * ε * (MeasureTheory.volume
      (⋃ w ∈ T.closedVertices U, (T.cell w).carrier)).toReal =
      6 * M * t ^ 2 * (MeasureTheory.volume
      (⋃ w ∈ T.closedVertices U, (T.cell w).carrier)).toReal := by
    rw [← e1]
    ring
  have hterm2 : 6 * M * t ^ 2 * (MeasureTheory.volume
      (⋃ w ∈ T.closedVertices U, (T.cell w).carrier)).toReal ≤
      6 * M * t ^ 2 * (MeasureTheory.volume
      (Metric.closedBall (0 : Euc 2) (R₀ + 1))).toReal :=
    mul_le_mul_of_nonneg_left hvol (by positivity)
  have hsq : (Real.sqrt 2 * t + ε) ^ 2 ≤ (Real.sqrt 2 + 1) ^ 2 * t ^ 2 := by
    have h1 : Real.sqrt 2 * t + ε ≤ (Real.sqrt 2 + 1) * t := by linarith
    have h0 : 0 ≤ Real.sqrt 2 * t + ε := by positivity
    calc (Real.sqrt 2 * t + ε) ^ 2 ≤ ((Real.sqrt 2 + 1) * t) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = (Real.sqrt 2 + 1) ^ 2 * t ^ 2 := by ring
  have hterm3 : M / 2 * (Real.sqrt 2 * t + ε) ^ 2 ≤ M / 2 * ((Real.sqrt 2 + 1) ^ 2 * t ^ 2) :=
    mul_le_mul_of_nonneg_left hsq (by positivity)
  have hfinal : M * (3 + 6 * (MeasureTheory.volume (Metric.closedBall (0 : Euc 2) (R₀ + 1))).toReal +
      (Real.sqrt 2 + 1) ^ 2 / 2) * t ^ 2 =
      3 * M * t ^ 2 + 6 * M * t ^ 2 * (MeasureTheory.volume
        (Metric.closedBall (0 : Euc 2) (R₀ + 1))).toReal +
      M / 2 * ((Real.sqrt 2 + 1) ^ 2 * t ^ 2) := by
    ring
  rw [hε23]
  linarith [hbound, hM0, hterm1, hterm2, hterm3, hfinal]

end SpherePackings
