-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (files `BouRabeeGwynne/Section3Boxes.lean` and `BouRabeeGwynne/Section3PlanarEstimate.lean` at
-- commit cf73d6e): the maximum principle on a good box, with cell diameters in place of the mesh.
import SpherePackings.Support.Section3.PlanarCuts
import SpherePackings.Support.Section3.EnergyMinimal
import SpherePackings.Support.Section3.GeneralRateFull
import BouRabeeGwynne.Section3PlanarEstimate

/-!
# Theorem 3.3 with its printed constant (intermediate result)

**Intermediate result**, under the earlier, stronger hypotheses (the cells of `V[U]` in the interior
of the ambient set, and the Hessian bound also on the edge segments of `E[Ū]`) and a Lipschitz
hypothesis between vertices; it is not registered. The registered Theorem 3.3 is the corrected
paper's, `planar_dirichlet_bound_internal` and `planar_rate_internal` (`PlanarInternal.lean`).

`rw-spheres.tex:1030-1082` (label `theorem:2d`): in the plane,
`sup_{V[U]} |h_D - h_C| ≤ inf_{k > 0} (6 k M ε vol(Û) + 2 (√2 k⁻¹ + ε) L)`.

The proof is the printed one.  For every `k > 0` the bad columns in each coordinate direction have
measure at most `k⁻¹` at the threshold `3 k M ε ∑ d vol(Q_e) ≤ 6 k M ε vol(Û)` (Proposition 3.2,
corrected, and `∑ d vol(Q_e) ≤ d vol(Û)`); the maximal bad interval around each coordinate of `v`
then has length at most `k⁻¹` (`exists_unitLine_cuts_around`), which gives a rectangle `S ∋ v` of
diameter at most `√2 k⁻¹` whose boundary cells carry error below the threshold, and the maximum
principle on the cells inside `S` bounds the error at `v` by the threshold plus the oscillation of
`h_C` over vertices within `ε + √2 k⁻¹`.

Hypotheses as in the edge-segment form of Proposition 2.6 (`EnergyMinimal.lean`: cells of `V[U]` in
the interior of the ambient set, Hessian bound also on the edge segments); `L` bounds the oscillation of `h_C` between vertices of
`V̄[U]` (`|h_C(w) - h_C(v)| ≤ L |w - v|`).  The printed proof derives that from the gradient bound
`L = sup_Û |∇ h_C|` on the segment `[v, w]`, a step that fails when the segment leaves `Û`; this
hypothesis is therefore an addition, not known to be needed.  `ε` bounds the diameters of the cells of `V̄[U]`.
-/

namespace SpherePackings

open BouRabeeGwynne BouRabeeGwynne.OrthogonalTiling

open scoped Classical MeasureTheory ENNReal

/-- A planar box with sides at most `s` has diameter at most `√2 s`. -/
theorem planar_box_dist_le (lower upper : Fin 2 → ℝ) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : ∀ i, upper i - lower i ≤ s) :
    ∀ x ∈ slabIntersection (fun i => innerSL ℝ (coordinateAxis i)) lower upper,
    ∀ y ∈ slabIntersection (fun i => innerSL ℝ (coordinateAxis i)) lower upper,
      dist x y ≤ Real.sqrt 2 * s := by
  intro x hx y hy
  have hcoord (i : Fin 2) : |x i - y i| ≤ s := by
    have hx' := hx i
    have hy' := hy i
    change lower i < inner ℝ (coordinateAxis i) x ∧
      inner ℝ (coordinateAxis i) x < upper i at hx'
    change lower i < inner ℝ (coordinateAxis i) y ∧
      inner ℝ (coordinateAxis i) y < upper i at hy'
    simp only [inner_coordinateAxis] at hx' hy'
    have := hs i
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hsq (i : Fin 2) : (x i - y i) ^ 2 ≤ s ^ 2 := by
    simpa only [← pow_two, sq_abs] using mul_self_le_mul_self (abs_nonneg _) (hcoord i)
  have hnorm : ‖x - y‖ ^ 2 ≤ 2 * s ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin 2, s ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [PiLp.sub_apply] using hsq i
      _ = _ := by simp
  rw [dist_eq_norm]
  have h2 : (Real.sqrt 2 * s) ^ 2 = 2 * s ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
  have hpos : 0 ≤ Real.sqrt 2 * s := mul_nonneg (Real.sqrt_nonneg 2) hs0
  nlinarith [norm_nonneg (x - y)]

/-- The maximum principle on the cells inside a box, with cell diameters at most `ε` in place of
the global mesh. -/
theorem error_le_of_good_box_local {d : ℕ} (T : OrthogonalTiling d) (R : Set T.V) [Fintype R]
    (A : Set R) (haccess : (T.finiteNetwork R).BoundaryAccessible A)
    (h g : R → ℝ) (hsol : (T.finiteNetwork R).SolvesDirichlet A g h)
    {I : Type*} (L : I → Euc d →L[ℝ] ℝ) (lower upper : I → ℝ)
    {η ω D ε : ℝ} (hη : 0 ≤ η) (hω : 0 ≤ ω)
    (hgood : ∀ w ∈ A, (∃ i, ∃ x ∈ (T.cell w).carrier,
      L i x = lower i ∨ L i x = upper i) → |h w - g w| ≤ η)
    (hdiamR : ∀ w : R, Metric.diam (T.cell (w : T.V)).carrier ≤ ε)
    (hdiam : ∀ x ∈ slabIntersection L lower upper,
      ∀ y ∈ slabIntersection L lower upper, dist x y ≤ D)
    {v : R} (hvA : v ∈ A) (hvS : T.pos v ∈ slabIntersection L lower upper)
    (hmod : ∀ w : R, dist (T.pos w) (T.pos v) ≤ ε + D → |g w - g v| ≤ ω) :
    |h v - g v| ≤ η + ω := by
  let B := T.cellsContainedInterior R A (slabIntersection L lower upper)
  by_cases hvB : v ∈ B
  · have hBA : B ⊆ A := T.cellsContainedInterior_subset R A _
    have hboundary : ∀ w ∈ (T.finiteNetwork R).externalBoundary B,
        |h w - g w| ≤ η := by
      intro w hw
      by_cases hwA : w ∈ A
      · exact hgood w hwA (T.boundary_cell_meets_cut R A L lower upper hw hwA)
      · simpa only [hsol.2 w hwA, sub_self, abs_zero] using hη
    refine (T.finiteNetwork R).harmonic_error_le_boundary_error_add_oscillation B
      ((T.finiteNetwork R).boundaryAccessible_mono hBA haccess) h g
      (fun w hw => hsol.1 w (hBA hw)) hboundary hvB (fun w hw => hmod w ?_)
    obtain ⟨u, hu, ha⟩ := hw.2
    have huw : T.adj u w := T.conductanceReal_pos_iff.mp ha
    obtain ⟨z, hzu, hzw⟩ := huw.2.1
    calc
      _ ≤ dist (T.pos w) z + dist z (T.pos v) := dist_triangle _ _ _
      _ ≤ ε + D := add_le_add
        ((Metric.dist_le_diam_of_mem (T.cell _).compact.isBounded
          (interior_subset (T.pos_mem_interior _)) hzw).trans (hdiamR w))
        (hdiam z (hu.2 hzu) (T.pos v) hvS)
  · have hcut := (T.cell v).exists_cut_of_not_subset L lower upper
      (interior_subset (T.pos_mem_interior v)) hvS
      (fun hsub => hvB ⟨hvA, hsub⟩)
    exact (hgood v hvA hcut).trans (le_add_of_nonneg_right hω)

/-- Theorem 3.3 (`theorem:2d`) with the printed constant, under the edge-segment and Lipschitz
hypotheses (intermediate result, not registered). -/
theorem planar_dirichlet_rate_printed (T : OrthogonalTiling 2) (U : Set (Euc 2))
    [Fintype (T.closedVertices U)]
    (hcellD : ∀ v ∈ T.interiorVertices U, (T.cell v).carrier ⊆ interior T.domain)
    {W : Set (Euc 2)} (hW : IsOpen W) {hC : Euc 2 → ℝ} (hh : IsHarmonicOn hC W)
    (hcells : ∀ v ∈ T.closedVertices U, (T.cell v).carrier ⊆ W)
    {W' : Set (Euc 2)} (hW' : IsOpen W') (hC2 : ContDiffOn ℝ 2 hC W')
    (hsegs : ∀ v ∈ T.closedVertices U, ∀ w ∈ T.closedVertices U, T.adj v w →
      v ∈ T.interiorVertices U ∨ w ∈ T.interiorVertices U →
      segment ℝ (T.pos v) (T.pos w) ⊆ W')
    {M L ε : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hdiam : ∀ v ∈ T.closedVertices U, Metric.diam (T.cell v).carrier ≤ ε)
    (hHcell : ∀ v ∈ T.closedVertices U, ∀ x ∈ (T.cell v).carrier,
      ‖fderiv ℝ (fderiv ℝ hC) x‖ ≤ M)
    (hHseg : ∀ v ∈ T.closedVertices U, ∀ w ∈ T.closedVertices U, T.adj v w →
      v ∈ T.interiorVertices U ∨ w ∈ T.interiorVertices U →
      ∀ x ∈ segment ℝ (T.pos v) (T.pos w), ‖fderiv ℝ (fderiv ℝ hC) x‖ ≤ M)
    (hLip : ∀ v ∈ T.closedVertices U, ∀ w ∈ T.closedVertices U,
      |hC (T.pos w) - hC (T.pos v)| ≤ L * dist (T.pos w) (T.pos v))
    (hD : T.V → ℝ) (hsol : T.SolvesDirichlet U (fun v => hC (T.pos v)) hD) :
    ∀ k : ℝ, 0 < k → ∀ v ∈ T.interiorVertices U, |hD v - hC (T.pos v)| ≤
      6 * k * M * ε * (MeasureTheory.volume (⋃ w ∈ T.closedVertices U,
        (T.cell w).carrier)).toReal + 2 * (Real.sqrt 2 / k + ε) * L := by
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
      |f v| ≤ η + L * (ε + Real.sqrt 2 * (1 / k + δ)) := by
    intro δ hδ
    have hcuts : ∀ i : Fin 2, ∃ a b : ℝ, a ≤ T.pos v i ∧ T.pos v i ≤ b ∧ b - a ≤ 1 / k + δ ∧
        a • coordinateAxis i ∉ T.columnBadSet R A (coordinateAxis i.rev)
          (coordinateAxis_ne_zero i.rev) f η ∧
        b • coordinateAxis i ∉ T.columnBadSet R A (coordinateAxis i.rev)
          (coordinateAxis_ne_zero i.rev) f η := fun i =>
      exists_unitLine_cuts_around (norm_coordinateAxis i) _ (by positivity) hδ (hbad i) _
    choose lower upper hlo hhi hlen hlgood hugood using hcuts
    have hω : 0 ≤ L * (ε + Real.sqrt 2 * (1 / k + δ)) := by positivity
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
    exact error_le_of_good_box_local T R A ha (fun w => hD w) (fun w => hC (T.pos w)) hsolR
      (fun i => innerSL ℝ (coordinateAxis i)) lower upper hη0 hω hgood
      (fun w => hdiam w w.property)
      (planar_box_dist_le lower upper (by positivity) (fun i => by linarith [hlen i]))
      hvA hvbox
      (fun w hw => (hLip vR vR.property w w.property).trans
        (mul_le_mul_of_nonneg_left hw hL))
  -- let the slack go to zero
  have hlim : |f v| ≤ η + L * (ε + Real.sqrt 2 * (1 / k)) := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    have hc : 0 < L * Real.sqrt 2 + 1 := by positivity
    have := hdelta (δ / (L * Real.sqrt 2 + 1)) (div_pos hδ hc)
    have hsmall : L * (Real.sqrt 2 * (δ / (L * Real.sqrt 2 + 1))) ≤ δ := by
      rw [← mul_assoc, mul_div_assoc']
      rw [div_le_iff₀ hc]
      nlinarith [mul_nonneg hL (Real.sqrt_nonneg 2)]
    nlinarith
  have hηvol : η ≤ 6 * k * M * ε * (MeasureTheory.volume Uhat).toReal := by
    rw [hηdef]
    have h0 : 0 ≤ 3 * k * M * ε := by positivity
    calc 3 * k * M * ε * K ≤ 3 * k * M * ε * (2 * (MeasureTheory.volume Uhat).toReal) :=
          mul_le_mul_of_nonneg_left hKvol h0
      _ = _ := by ring
  have hsqrt : Real.sqrt 2 * (1 / k) = Real.sqrt 2 / k := by ring
  have hfinal : L * (ε + Real.sqrt 2 / k) ≤ 2 * (Real.sqrt 2 / k + ε) * L := by
    have : 0 ≤ L * (ε + Real.sqrt 2 / k) := by positivity
    nlinarith
  change |f v| ≤ _
  rw [hsqrt] at hlim
  linarith

end SpherePackings
