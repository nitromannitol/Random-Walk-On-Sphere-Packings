-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/Section3Boxes.lean` at commit cf73d6e): the maximum principle on a good box,
-- with a subharmonic comparison in place of the oscillation of `h_C`.
import SpherePackings.Support.Section3.PlanarRateFull

/-!
# Theorem 3.3 without a Lipschitz hypothesis (intermediate result)

**Intermediate result**, under the earlier, stronger hypotheses (the cells of `V[U]` in the interior
of the ambient set, and the Hessian bound also on the edge segments of `E[Ū]`); it is not
registered. The registered Theorem 3.3 is the corrected paper's, `planar_dirichlet_bound_internal`
and `planar_rate_internal` (`PlanarInternal.lean`).

The printed proof of Theorem 3.3 (`rw-spheres.tex:1055-1082`) ends with the maximum principle on
the cells inside a good rectangle `S ∋ v` and the mean value theorem for `h_C` between `v` and the
boundary vertices of `S`, on segments that can leave `Û`.  Here the last step is replaced by the
comparison used for Theorem 3.6: `±(h_D - h_C) + M |· - v|²` is discrete subharmonic at the
vertices of `V[U]` (Lemma 2.2 and Taylor's theorem on the edge segments, `abs_laplacian_le`,
`laplacian_sq_dist`), so its value at `v` is at most its maximum on the boundary of the cells
inside `S`.  This needs only the hypotheses of the edge-segment form of Proposition 2.6 and gives, for every
`k > 0`, `|h_D - h_C| ≤ 6 k M ε vol(Û) + M (ε + √2 k⁻¹)²` on `V[U]`, and with `k = ε^{-1/2}` the
printed rate `C(U, M) ε^{1/2}` of the "in particular" clause.  The printed bound
`inf_k (6 k M ε vol(Û) + 2 (√2 k⁻¹ + ε) L)` itself is not obtained this way.
-/

namespace SpherePackings

open BouRabeeGwynne BouRabeeGwynne.OrthogonalTiling

open scoped Classical MeasureTheory ENNReal

/-- The maximum principle on the cells inside a box, with the oscillation of `h_C` replaced by the
subharmonic comparison `±(h_D - h_C) + M |· - v|²`: the error at `v` is at most the boundary error
plus `M (ε + D)²`, `D` bounding the diameter of the box. -/
theorem error_le_of_good_box_quadratic {d : ℕ} (hd : 1 ≤ d) (T : OrthogonalTiling d)
    (U : Set (Euc d)) [Fintype (T.closedVertices U)]
    (haccess : (T.finiteNetwork (T.closedVertices U)).BoundaryAccessible (T.finiteInterior U))
    (hcellD : ∀ v ∈ T.interiorVertices U, (T.cell v).carrier ⊆ interior T.domain)
    {W' : Set (Euc d)} (hW' : IsOpen W') {hC : Euc d → ℝ} (hC2 : ContDiffOn ℝ 2 hC W')
    (hsegs : ∀ v ∈ T.closedVertices U, ∀ w ∈ T.closedVertices U, T.adj v w →
      v ∈ T.interiorVertices U ∨ w ∈ T.interiorVertices U →
      segment ℝ (T.pos v) (T.pos w) ⊆ W')
    {M : ℝ} (hM : 0 ≤ M)
    (hHseg : ∀ v ∈ T.closedVertices U, ∀ w ∈ T.closedVertices U, T.adj v w →
      v ∈ T.interiorVertices U ∨ w ∈ T.interiorVertices U →
      ∀ x ∈ segment ℝ (T.pos v) (T.pos w), ‖fderiv ℝ (fderiv ℝ hC) x‖ ≤ M)
    (h : T.closedVertices U → ℝ)
    (hsol : (T.finiteNetwork (T.closedVertices U)).SolvesDirichlet (T.finiteInterior U)
      (fun w => hC (T.pos w)) h)
    {I : Type*} (L : I → Euc d →L[ℝ] ℝ) (lower upper : I → ℝ)
    {η D ε : ℝ} (hη : 0 ≤ η) (hD0 : 0 ≤ D) (hε : 0 ≤ ε)
    (hgood : ∀ w ∈ T.finiteInterior U, (∃ i, ∃ x ∈ (T.cell (w : T.V)).carrier,
      L i x = lower i ∨ L i x = upper i) → |h w - hC (T.pos w)| ≤ η)
    (hdiamR : ∀ w : T.closedVertices U, Metric.diam (T.cell (w : T.V)).carrier ≤ ε)
    (hdiam : ∀ x ∈ slabIntersection L lower upper,
      ∀ y ∈ slabIntersection L lower upper, dist x y ≤ D)
    {v : T.closedVertices U} (hvA : v ∈ T.finiteInterior U)
    (hvS : T.pos v ∈ slabIntersection L lower upper) :
    |h v - hC (T.pos v)| ≤ η + M * (ε + D) ^ 2 := by
  let R := T.closedVertices U
  let A : Set R := T.finiteInterior U
  let N := T.finiteNetwork R
  let B := T.cellsContainedInterior R A (slabIntersection L lower upper)
  by_cases hvB : v ∈ B
  · have hBA : B ⊆ A := T.cellsContainedInterior_subset R A _
    have hboundary : ∀ w ∈ N.externalBoundary B, |h w - hC (T.pos w)| ≤ η := by
      intro w hw
      by_cases hwA : w ∈ A
      · exact hgood w hwA (T.boundary_cell_meets_cut R A L lower upper hw hwA)
      · simpa only [hsol.2 w hwA, sub_self, abs_zero] using hη
    -- the distance bound on the external boundary, as in `error_le_of_good_box_local`
    have hdistB : ∀ w ∈ N.externalBoundary B, dist (T.pos w) (T.pos v) ≤ ε + D := by
      intro w hw
      obtain ⟨u, hu, ha⟩ := hw.2
      have huw : T.adj u w := T.conductanceReal_pos_iff.mp ha
      obtain ⟨z, hzu, hzw⟩ := huw.2.1
      calc
        _ ≤ dist (T.pos w) z + dist z (T.pos v) := dist_triangle _ _ _
        _ ≤ ε + D := add_le_add
          ((Metric.dist_le_diam_of_mem (T.cell _).compact.isBounded
            (interior_subset (T.pos_mem_interior _)) hzw).trans (hdiamR w))
          (hdiam z (hu.2 hzu) (T.pos v) hvS)
    have hρw : ∀ w ∈ N.externalBoundary B, ‖T.pos w - T.pos v‖ ≤ ε + D := fun w hw => by
      rw [← dist_eq_norm]
      exact hdistB w hw
    have hlapB : ∀ u ∈ B, |N.laplacian (fun w => hC (T.pos w)) u| ≤
        M * ∑ w : R, N.a u w * ‖T.pos w - T.pos u‖ ^ 2 := fun u hu =>
      abs_laplacian_le hd T U u (hBA hu) (hcellD u (hBA hu)) hW' hC2 hM
        (fun w hw => hsegs u u.property w w.property hw (Or.inl (hBA hu)))
        (fun w hw => hHseg u u.property w w.property hw (Or.inl (hBA hu)))
    have hsqB : ∀ u ∈ B, N.laplacian (fun w : R => ‖T.pos w - T.pos v‖ ^ 2) u =
        ∑ w : R, N.a u w * ‖T.pos w - T.pos u‖ ^ 2 := fun u hu =>
      laplacian_sq_dist hd T U u (hBA hu) (hcellD u (hBA hu)) (T.pos v)
    have hbdry : ∀ w ∈ N.externalBoundary B,
        |h w - hC (T.pos w)| + M * ‖T.pos w - T.pos v‖ ^ 2 ≤ η + M * (ε + D) ^ 2 := by
      intro w hw
      have h2 : ‖T.pos w - T.pos v‖ ^ 2 ≤ (ε + D) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hρw w hw) 2
      exact add_le_add (hboundary w hw) (mul_le_mul_of_nonneg_left h2 hM)
    -- the maximum principle for `(h - g) + M |· - v|²`
    have hup : h v - hC (T.pos v) ≤ η + M * (ε + D) ^ 2 := by
      have := N.local_maximum_principle B ((T.finiteNetwork R).boundaryAccessible_mono hBA haccess)
        (fun w : R => (h w - hC (T.pos w)) + M * ‖T.pos w - T.pos v‖ ^ 2) (η + M * (ε + D) ^ 2)
        (fun u hu => by
          have hL := N.laplacian_add (h - fun w : R => hC (T.pos w))
            (fun w : R => M * ‖T.pos w - T.pos v‖ ^ 2) u
          have hS := N.laplacian_sub h (fun w : R => hC (T.pos w)) u
          have hcm : N.laplacian (fun w : R => M * ‖T.pos w - T.pos v‖ ^ 2) u =
              M * N.laplacian (fun w : R => ‖T.pos w - T.pos v‖ ^ 2) u :=
            N.laplacian_smul M (fun w : R => ‖T.pos w - T.pos v‖ ^ 2) u
          have h0 : N.laplacian h u = 0 := hsol.1 u (hBA hu)
          have habs := abs_le.mp (hlapB u hu)
          change 0 ≤ N.laplacian ((h - fun w : R => hC (T.pos w)) +
            fun w : R => M * ‖T.pos w - T.pos v‖ ^ 2) u
          rw [hL, hS, h0, hcm, hsqB u hu]
          linarith [habs.2])
        (fun w hw => by
          have := hbdry w hw
          have := le_abs_self (h w - hC (T.pos w))
          linarith) v hvB
      have h0 : ‖T.pos v - T.pos v‖ ^ 2 = 0 := by simp
      simp only [h0, mul_zero, add_zero] at this
      exact this
    -- the same for `-(h - g) + M |· - v|²`
    have hlow : -(h v - hC (T.pos v)) ≤ η + M * (ε + D) ^ 2 := by
      have := N.local_maximum_principle B ((T.finiteNetwork R).boundaryAccessible_mono hBA haccess)
        (fun w : R => -(h w - hC (T.pos w)) + M * ‖T.pos w - T.pos v‖ ^ 2) (η + M * (ε + D) ^ 2)
        (fun u hu => by
          have hL := N.laplacian_add (-(h - fun w : R => hC (T.pos w)))
            (fun w : R => M * ‖T.pos w - T.pos v‖ ^ 2) u
          have hN := N.laplacian_neg (h - fun w : R => hC (T.pos w)) u
          have hS := N.laplacian_sub h (fun w : R => hC (T.pos w)) u
          have hcm : N.laplacian (fun w : R => M * ‖T.pos w - T.pos v‖ ^ 2) u =
              M * N.laplacian (fun w : R => ‖T.pos w - T.pos v‖ ^ 2) u :=
            N.laplacian_smul M (fun w : R => ‖T.pos w - T.pos v‖ ^ 2) u
          have h0 : N.laplacian h u = 0 := hsol.1 u (hBA hu)
          have habs := abs_le.mp (hlapB u hu)
          change 0 ≤ N.laplacian ((-(h - fun w : R => hC (T.pos w))) +
            fun w : R => M * ‖T.pos w - T.pos v‖ ^ 2) u
          rw [hL, hN, hS, h0, hcm, hsqB u hu]
          linarith [habs.1])
        (fun w hw => by
          have := hbdry w hw
          have := neg_abs_le (h w - hC (T.pos w))
          linarith) v hvB
      have h0 : ‖T.pos v - T.pos v‖ ^ 2 = 0 := by simp
      simp only [h0, mul_zero, add_zero] at this
      exact this
    have hquad : |h v - hC (T.pos v)| ≤ η + M * (ε + D) ^ 2 := abs_le.mpr ⟨by linarith, hup⟩
    exact hquad
  · have hcut := (T.cell v).exists_cut_of_not_subset L lower upper
      (interior_subset (T.pos_mem_interior v)) hvS (fun hsub => hvB ⟨hvA, hsub⟩)
    exact (hgood v hvA hcut).trans
      (le_add_of_nonneg_right (mul_nonneg hM (pow_nonneg (add_nonneg hε hD0) 2)))

/-- Theorem 3.3 (`theorem:2d`) without a Lipschitz hypothesis, under the edge-segment hypothesis
(intermediate result, not registered): for every `k > 0`, the error on
`V[U]` is at most `6 k M ε vol(Û) + M (ε + √2 k⁻¹)²`, under the hypotheses of the edge-segment form of
Proposition 2.6. -/
theorem planar_dirichlet_bound_quadratic (T : OrthogonalTiling 2) (U : Set (Euc 2))
    [Fintype (T.closedVertices U)]
    (hcellD : ∀ v ∈ T.interiorVertices U, (T.cell v).carrier ⊆ interior T.domain)
    {W : Set (Euc 2)} (hW : IsOpen W) {hC : Euc 2 → ℝ} (hh : IsHarmonicOn hC W)
    (hcells : ∀ v ∈ T.closedVertices U, (T.cell v).carrier ⊆ W)
    {W' : Set (Euc 2)} (hW' : IsOpen W') (hC2 : ContDiffOn ℝ 2 hC W')
    (hsegs : ∀ v ∈ T.closedVertices U, ∀ w ∈ T.closedVertices U, T.adj v w →
      v ∈ T.interiorVertices U ∨ w ∈ T.interiorVertices U →
      segment ℝ (T.pos v) (T.pos w) ⊆ W')
    {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hdiam : ∀ v ∈ T.closedVertices U, Metric.diam (T.cell v).carrier ≤ ε)
    (hHcell : ∀ v ∈ T.closedVertices U, ∀ x ∈ (T.cell v).carrier,
      ‖fderiv ℝ (fderiv ℝ hC) x‖ ≤ M)
    (hHseg : ∀ v ∈ T.closedVertices U, ∀ w ∈ T.closedVertices U, T.adj v w →
      v ∈ T.interiorVertices U ∨ w ∈ T.interiorVertices U →
      ∀ x ∈ segment ℝ (T.pos v) (T.pos w), ‖fderiv ℝ (fderiv ℝ hC) x‖ ≤ M)
    (hD : T.V → ℝ) (hsol : T.SolvesDirichlet U (fun v => hC (T.pos v)) hD) :
    ∀ k : ℝ, 0 < k → ∀ v ∈ T.interiorVertices U, |hD v - hC (T.pos v)| ≤
      6 * k * M * ε * (MeasureTheory.volume (⋃ w ∈ T.closedVertices U,
        (T.cell w).carrier)).toReal + M * (ε + Real.sqrt 2 / k) ^ 2 := by
  intro k hk v hv
  let R := T.closedVertices U
  let A : Set R := T.finiteInterior U
  let vR : R := ⟨v, T.interiorVertices_subset_closedVertices U hv⟩
  have hvA : vR ∈ A := hv
  have hcellA : ∀ w ∈ A, (T.cell (w : T.V)).carrier ⊆ interior T.domain :=
    fun w hw => hcellD (w : T.V) hw
  have hneighborsA : ∀ w ∈ A, ∀ x, T.adj (w : T.V) x → x ∈ R :=
    fun w hw x hwx => T.neighbor_mem_closedVertices (show (w : T.V) ∈ T.interiorVertices U from hw) hwx
  have ha := T.finiteNetwork_boundaryAccessible_of_cell_interior (by norm_num)
    (coordinateAxis (0 : Fin 2)) (coordinateAxis_ne_zero 0) R A hneighborsA hcellA
  have hsolR := T.solvesDirichlet_restrict hsol
  let f : T.V → ℝ := fun w => hD w - hC (T.pos w)
  set K := T.incidentMass R A with hKdef
  have hK0 : 0 ≤ K := T.incidentMass_nonneg R A
  set η := 3 * k * M * ε * K with hηdef
  have hη0 : 0 ≤ η := by positivity
  -- the region `Û` and the mass bound `K ≤ 2 vol(Û)`
  set Uhat := ⋃ w ∈ T.closedVertices U, (T.cell w).carrier with hUhatdef
  have hUhat_eq : Uhat = ⋃ w : R, (T.cell (w : T.V)).carrier := by
    rw [hUhatdef, Set.biUnion_eq_iUnion]
  have hUhatc : IsCompact Uhat := by
    rw [hUhat_eq]
    exact isCompact_iUnion fun w => (T.cell (w : T.V)).compact
  have hm : (μHE[2] : MeasureTheory.Measure (Euc 2)) = MeasureTheory.volume := by
    simpa using InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := Euc 2)
  have hUfinite : μHE[2] Uhat ≠ ⊤ := by
    rw [hm]
    exact hUhatc.measure_lt_top.ne
  have hKvol : K ≤ 2 * (MeasureTheory.volume Uhat).toReal := by
    have := T.incidentMass_le_dim_mul_volume (d := 2) (by norm_num) R A hUfinite
      (fun w => by
        rw [hUhat_eq]
        exact Set.subset_iUnion (fun w : R => (T.cell (w : T.V)).carrier) w)
    rw [hm] at this
    simpa using this
  -- the bad columns
  have hbad : ∀ i : Fin 2, μHE[1] (T.columnBadSet R A (coordinateAxis i.rev)
      (coordinateAxis_ne_zero i.rev) f η) ≤ ENNReal.ofReal (1 / k) := by
    intro i
    have := harmonic_column_bound_segment (by norm_num) T U hcellD hW hh hcells hW' hC2 hsegs hM hε
      hdiam hHcell hHseg hD hsol (coordinateAxis i.rev) (coordinateAxis_ne_zero i.rev) hk
    simpa only [hηdef, hKdef] using this
  -- the error at `v`, for every slack `δ > 0`
  have hdelta : ∀ δ : ℝ, 0 < δ →
      |f v| ≤ η + M * (ε + Real.sqrt 2 * (1 / k + δ)) ^ 2 := by
    intro δ hδ
    have hcuts : ∀ i : Fin 2, ∃ a b : ℝ, a ≤ T.pos v i ∧ T.pos v i ≤ b ∧ b - a ≤ 1 / k + δ ∧
        a • coordinateAxis i ∉ T.columnBadSet R A (coordinateAxis i.rev)
          (coordinateAxis_ne_zero i.rev) f η ∧
        b • coordinateAxis i ∉ T.columnBadSet R A (coordinateAxis i.rev)
          (coordinateAxis_ne_zero i.rev) f η := fun i =>
      exists_unitLine_cuts_around (norm_coordinateAxis i) _ (by positivity) hδ (hbad i) _
    choose lower upper hlo hhi hlen hlgood hugood using hcuts
    have hω : 0 ≤ M * (ε + Real.sqrt 2 * (1 / k + δ)) ^ 2 := mul_nonneg hM (sq_nonneg _)
    -- a cut through the cell of `v`
    by_cases hdeg : ∃ i, lower i = T.pos v i ∨ upper i = T.pos v i
    · obtain ⟨i, hi | hi⟩ := hdeg
      · have := T.abs_le_of_good_planar_cut R A f η i (lower i) (hlgood i) hvA
          (interior_subset (T.pos_mem_interior v)) hi.symm
        linarith
      · have := T.abs_le_of_good_planar_cut R A f η i (upper i) (hugood i) hvA
          (interior_subset (T.pos_mem_interior v)) hi.symm
        linarith
    push Not at hdeg
    have hvbox : T.pos v ∈
        slabIntersection (fun i => innerSL ℝ (coordinateAxis i)) lower upper := by
      intro i
      change lower i < inner ℝ (coordinateAxis i) (T.pos v) ∧
        inner ℝ (coordinateAxis i) (T.pos v) < upper i
      rw [inner_coordinateAxis]
      exact ⟨lt_of_le_of_ne (hlo i) (hdeg i).1, lt_of_le_of_ne (hhi i) (fun h => (hdeg i).2 h.symm)⟩
    have hgood : ∀ w ∈ A, (∃ i, ∃ x ∈ (T.cell (w : T.V)).carrier,
        (fun i => innerSL ℝ (coordinateAxis i)) i x = lower i ∨
          (fun i => innerSL ℝ (coordinateAxis i)) i x = upper i) →
        |(fun w : R => hD w) w - (fun w : R => hC (T.pos w)) w| ≤ η := by
      rintro w hw ⟨i, x, hx, hcut | hcut⟩
      · simp only [innerSL_apply_apply, inner_coordinateAxis] at hcut
        exact T.abs_le_of_good_planar_cut R A f η i (lower i) (hlgood i) hw hx hcut
      · simp only [innerSL_apply_apply, inner_coordinateAxis] at hcut
        exact T.abs_le_of_good_planar_cut R A f η i (upper i) (hugood i) hw hx hcut
    exact error_le_of_good_box_quadratic (by norm_num) T U ha hcellD hW' hC2 hsegs hM hHseg
      (fun w => hD w) hsolR (fun i => innerSL ℝ (coordinateAxis i)) lower upper hη0
      (D := Real.sqrt 2 * (1 / k + δ)) (by positivity) hε hgood
      (fun w => hdiam w w.property)
      (planar_box_dist_le lower upper (s := 1 / k + δ) (by positivity)
        (fun i => by linarith [hlen i]))
      hvA hvbox
  -- let the slack go to zero
  have hlim : |f v| ≤ η + M * (ε + Real.sqrt 2 * (1 / k)) ^ 2 := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    have hC0 : 0 ≤ M * (2 * Real.sqrt 2 * (ε + Real.sqrt 2 * (1 / k)) + 2) := by positivity
    -- the slack `d ≤ 1` with `M (2 √2 a + 2) d ≤ δ`, where `a = ε + √2 / k`
    obtain ⟨d, hd0, hd1, hdδ⟩ : ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧
        M * (2 * Real.sqrt 2 * (ε + Real.sqrt 2 * (1 / k)) + 2) * d ≤ δ := by
      have hc1 : 0 < M * (2 * Real.sqrt 2 * (ε + Real.sqrt 2 * (1 / k)) + 2) + 1 := by linarith
      refine ⟨min 1 (δ / (M * (2 * Real.sqrt 2 * (ε + Real.sqrt 2 * (1 / k)) + 2) + 1)),
        lt_min one_pos (div_pos hδ hc1), min_le_left _ _, ?_⟩
      have h1 := (le_div_iff₀ hc1).mp
        (min_le_right 1 (δ / (M * (2 * Real.sqrt 2 * (ε + Real.sqrt 2 * (1 / k)) + 2) + 1)))
      have h2 : 0 ≤ min 1 (δ / (M * (2 * Real.sqrt 2 * (ε + Real.sqrt 2 * (1 / k)) + 2) + 1)) :=
        le_min zero_le_one (div_nonneg hδ.le hc1.le)
      nlinarith
    have hmain := hdelta d hd0
    have hsq : (ε + Real.sqrt 2 * (1 / k + d)) ^ 2 =
        (ε + Real.sqrt 2 * (1 / k)) ^ 2 + 2 * (ε + Real.sqrt 2 * (1 / k)) * Real.sqrt 2 * d +
          2 * d ^ 2 := by
      have h2 : (Real.sqrt 2 * d) ^ 2 = 2 * d ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num)]
      linear_combination h2
    have hd2 : d ^ 2 ≤ d := by nlinarith [mul_le_mul_of_nonneg_left hd1 hd0.le]
    have hineq : (ε + Real.sqrt 2 * (1 / k + d)) ^ 2 ≤
        (ε + Real.sqrt 2 * (1 / k)) ^ 2 +
          d * (2 * Real.sqrt 2 * (ε + Real.sqrt 2 * (1 / k)) + 2) := by
      rw [hsq]
      linarith [hd2]
    have hM' := mul_le_mul_of_nonneg_left hineq hM
    linarith
  have hηvol : η ≤ 6 * k * M * ε * (MeasureTheory.volume Uhat).toReal := by
    rw [hηdef]
    have h0 : 0 ≤ 3 * k * M * ε := by positivity
    calc 3 * k * M * ε * K ≤ 3 * k * M * ε * (2 * (MeasureTheory.volume Uhat).toReal) :=
          mul_le_mul_of_nonneg_left hKvol h0
      _ = _ := by ring
  have hsqrt : Real.sqrt 2 * (1 / k) = Real.sqrt 2 / k := by ring
  change |f v| ≤ _
  rw [hsqrt] at hlim
  linarith

/-- Theorem 3.3 (`theorem:2d`), the "in particular" clause, under the edge-segment hypothesis
(intermediate result, not registered): `sup_{V[U]} |h_D - h_C| ≤ C ε^{1/2}`
with `C = 6 M vol(B_{R₀+1}) + (1 + √2)² M`, `R₀` a bound on `‖x‖` over `U`, for `ε ≤ 1/2`, under
the hypotheses of the edge-segment form of Proposition 2.6. -/
theorem planar_dirichlet_rate_half (T : OrthogonalTiling 2) (U : Set (Euc 2))
    [Fintype (T.closedVertices U)]
    (hcellD : ∀ v ∈ T.interiorVertices U, (T.cell v).carrier ⊆ interior T.domain)
    {R₀ : ℝ} (hUR : ∀ x ∈ U, ‖x‖ ≤ R₀)
    {W : Set (Euc 2)} (hW : IsOpen W) {hC : Euc 2 → ℝ} (hh : IsHarmonicOn hC W)
    (hcells : ∀ v ∈ T.closedVertices U, (T.cell v).carrier ⊆ W)
    {W' : Set (Euc 2)} (hW' : IsOpen W') (hC2 : ContDiffOn ℝ 2 hC W')
    (hsegs : ∀ v ∈ T.closedVertices U, ∀ w ∈ T.closedVertices U, T.adj v w →
      v ∈ T.interiorVertices U ∨ w ∈ T.interiorVertices U →
      segment ℝ (T.pos v) (T.pos w) ⊆ W')
    {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε) (hε2 : ε ≤ 1 / 2)
    (hdiam : ∀ v ∈ T.closedVertices U, Metric.diam (T.cell v).carrier ≤ ε)
    (hHcell : ∀ v ∈ T.closedVertices U, ∀ x ∈ (T.cell v).carrier,
      ‖fderiv ℝ (fderiv ℝ hC) x‖ ≤ M)
    (hHseg : ∀ v ∈ T.closedVertices U, ∀ w ∈ T.closedVertices U, T.adj v w →
      v ∈ T.interiorVertices U ∨ w ∈ T.interiorVertices U →
      ∀ x ∈ segment ℝ (T.pos v) (T.pos w), ‖fderiv ℝ (fderiv ℝ hC) x‖ ≤ M)
    (hD : T.V → ℝ) (hsol : T.SolvesDirichlet U (fun v => hC (T.pos v)) hD) :
    ∀ v ∈ T.interiorVertices U, |hD v - hC (T.pos v)| ≤
      (6 * M * (MeasureTheory.volume (Metric.closedBall (0 : Euc 2) (R₀ + 1))).toReal +
        (1 + Real.sqrt 2) ^ 2 * M) * Real.sqrt ε := by
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
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hεpos
  have hk := planar_dirichlet_bound_quadratic T U hcellD hW hh hcells hW' hC2 hsegs hM hε hdiam
    hHcell hHseg hD hsol
  have hb := hk (1 / Real.sqrt ε) (by positivity) v hv
  -- `vol(Û) ≤ vol(B_{R₀ + 1})`
  have hsub : (⋃ w ∈ T.closedVertices U, (T.cell w).carrier) ⊆
      Metric.closedBall (0 : Euc 2) (R₀ + 1) := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨w, hw, hxw⟩ := hx
    exact mem_closedBall_zero_iff.mpr (cell_norm_le_of_closedVertices T U hUR hε2 hdiam hw hxw)
  have hvol : (MeasureTheory.volume (⋃ w ∈ T.closedVertices U, (T.cell w).carrier)).toReal ≤
      (MeasureTheory.volume (Metric.closedBall (0 : Euc 2) (R₀ + 1))).toReal :=
    ENNReal.toReal_mono (MeasureTheory.measure_closedBall_lt_top).ne (MeasureTheory.measure_mono hsub)
  have hsq : Real.sqrt ε * Real.sqrt ε = ε := Real.mul_self_sqrt hε
  have hr1 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have h1 : 6 * (1 / Real.sqrt ε) * M * ε = 6 * M * Real.sqrt ε := by
    field_simp
    nlinarith [hsq]
  have h2 : Real.sqrt 2 / (1 / Real.sqrt ε) = Real.sqrt 2 * Real.sqrt ε := by
    field_simp
  rw [h1, h2] at hb
  -- the new term: `(ε + √2 √ε)² = √ε² (√ε + √2)² ≤ √ε (1 + √2)²`
  have hkey : (ε + Real.sqrt 2 * Real.sqrt ε) ^ 2 ≤ (1 + Real.sqrt 2) ^ 2 * Real.sqrt ε := by
    have hfac : ε + Real.sqrt 2 * Real.sqrt ε = Real.sqrt ε * (Real.sqrt ε + Real.sqrt 2) := by
      linear_combination -hsq
    have hq : (Real.sqrt ε + Real.sqrt 2) ^ 2 ≤ (1 + Real.sqrt 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    have hu2 : Real.sqrt ε * Real.sqrt ε ≤ Real.sqrt ε := mul_le_of_le_one_left hs.le hr1
    rw [hfac, mul_pow]
    calc Real.sqrt ε ^ 2 * (Real.sqrt ε + Real.sqrt 2) ^ 2
        ≤ Real.sqrt ε * (Real.sqrt ε + Real.sqrt 2) ^ 2 :=
          mul_le_mul_of_nonneg_right (by rw [sq]; exact hu2) (sq_nonneg _)
      _ ≤ Real.sqrt ε * (1 + Real.sqrt 2) ^ 2 := mul_le_mul_of_nonneg_left hq hs.le
      _ = (1 + Real.sqrt 2) ^ 2 * Real.sqrt ε := by ring
  have hMkey : M * (ε + Real.sqrt 2 * Real.sqrt ε) ^ 2 ≤
      M * ((1 + Real.sqrt 2) ^ 2 * Real.sqrt ε) := mul_le_mul_of_nonneg_left hkey hM
  have h3 : 6 * M * Real.sqrt ε *
      (MeasureTheory.volume (⋃ w ∈ T.closedVertices U, (T.cell w).carrier)).toReal ≤
      6 * M * Real.sqrt ε * (MeasureTheory.volume (Metric.closedBall (0 : Euc 2) (R₀ + 1))).toReal :=
    mul_le_mul_of_nonneg_left hvol (by positivity)
  linarith

end SpherePackings
