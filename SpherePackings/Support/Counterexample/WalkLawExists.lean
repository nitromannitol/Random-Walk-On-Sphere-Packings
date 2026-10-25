module

public import SpherePackings.Support.Counterexample.Tangency
public import SpherePackings.Support.Counterexample.WalkLaw
public import BouRabeeGwynne.FiniteExit
public import BouRabeeGwynne.StoppedCurveMeasurable

@[expose] public section

/-!
# The stopped simple random walk laws of Theorem 6.1 exist
-/

open MeasureTheory Metric

namespace SpherePackings.Counterexample

open BouRabeeGwynne

variable {k : ℕ}

/-- The unit vector in the zeroth coordinate. -/
private def unitZero : Fin (k + 3) → ℤ := fun j => if j = 0 then 1 else 0

/-- A nonnegative square root of `7` lies between `2` and `3`. -/
private lemma bounds_of_sq (s : ℝ) (h0 : 0 ≤ s) (h : s ^ 2 = 7) : 2 ≤ s ∧ s ≤ 3 := by
  constructor <;> nlinarith

private lemma sqrt_seven_bounds : 2 ≤ Real.sqrt 7 ∧ Real.sqrt 7 ≤ 3 :=
  bounds_of_sq _ (Real.sqrt_nonneg 7) (Real.sq_sqrt (by norm_num))

private lemma two_ne_zero_fin : (2 : Fin (k + 3)) ≠ 0 := by
  intro h
  have h2 : ((2 : Fin (k + 3)) : ℕ) = 2 := Nat.mod_eq_of_lt (show 2 < k + 3 by omega)
  rw [h] at h2
  simp at h2

private lemma smallOffset_zero_val : smallOffset k 0 = Real.sqrt 7 / 2 := by
  simp [smallOffset]

private lemma abs_smallOffset_le (j : Fin (k + 3)) : |smallOffset k j| ≤ 2 := by
  have h := sqrt_seven_bounds
  have h0 := Real.sqrt_nonneg 7
  simp only [smallOffset, PiLp.toLp_apply]
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

private lemma center_inl_apply (x : BigIdx k) (j : Fin (k + 3)) :
    center k (.inl x) j = 2 * (x.1 j : ℝ) := by
  simp [center]

private lemma center_inr_apply (y : SmallIdx k) (j : Fin (k + 3)) :
    center k (.inr y) j = smallOffset k j + (y.1 j : ℝ) := by
  simp [center]

/-- Moving a big index one step up in the zeroth coordinate, while it stays big. -/
private def bigStep (x : BigIdx k) (h : x.1 0 < 0) : BigIdx k :=
  ⟨x.1 + unitZero, by simp [unitZero]; omega⟩

/-- The small index `(0, 2x₁, 2x₂, …)` attached to a big index with zeroth coordinate `0`. -/
private def zeroLift (x : BigIdx k) : SmallIdx k :=
  ⟨fun j => if j = 0 then 0 else 2 * x.1 j, by
    refine ⟨by simp, fun j hj => ?_⟩
    have hj0 : j ≠ 0 := by
      rintro rfl
      simp at hj
    simp [hj0]⟩

/-- Moving a small index one step up in the zeroth coordinate. -/
private def smallStep (y : SmallIdx k) : SmallIdx k :=
  ⟨y.1 + unitZero, by
    have h0 := y.2.1
    refine ⟨by simp [unitZero]; omega, fun j hj => ?_⟩
    have hj0 : j ≠ 0 := by
      rintro rfl
      simp at hj
    simpa [unitZero, hj0] using y.2.2 j hj⟩

/-- The successor of a sphere: a neighbour whose zeroth level rises by at least one. -/
private def stepIdx : Idx k → Idx k
  | .inl x => if h : x.1 0 < 0 then .inl (bigStep x h) else .inr (zeroLift x)
  | .inr y => .inr (smallStep y)

private lemma sum_sq_unitZero (x : Fin (k + 3) → ℤ) :
    ∑ j, (x j - (x + (unitZero : Fin (k + 3) → ℤ)) j) ^ 2 = 1 := by
  simp [unitZero, ite_pow]

private lemma stepIdx_inl_pos (x : BigIdx k) (h : x.1 0 < 0) :
    stepIdx (.inl x) = .inl (bigStep x h) := by
  simp [stepIdx, h]

private lemma stepIdx_inl_neg (x : BigIdx k) (h : ¬x.1 0 < 0) :
    stepIdx (.inl x) = .inr (zeroLift x) := by
  simp [stepIdx, h]

/-- The successor of every sphere touches it. -/
private lemma tangent_stepIdx (i : Idx k) : (packing k).Tangent i (stepIdx i) := by
  rcases i with x | y
  · by_cases h : x.1 0 < 0
    · rw [stepIdx_inl_pos x h, tangent_inl_inl]
      exact sum_sq_unitZero x.1
    · have hx0 : x.1 0 = 0 := by
        have := x.2
        omega
      rw [stepIdx_inl_neg x h, tangent_inl_inr]
      refine ⟨hx0, by simp [zeroLift], Or.inl (by simp [zeroLift]),
        Or.inl (by simp [zeroLift, two_ne_zero_fin]), fun j hj => ?_⟩
      have hj0 : j ≠ 0 := by
        rintro rfl
        simp at hj
      simp [zeroLift, hj0]
  · simp only [stepIdx]
    rw [tangent_inr_inr]
    exact sum_sq_unitZero y.1

/-- The successor of every sphere has zeroth centre coordinate at least one more. -/
private lemma center_stepIdx (i : Idx k) : center k i 0 + 1 ≤ center k (stepIdx i) 0 := by
  rcases i with x | y
  · by_cases h : x.1 0 < 0
    · have hb : (bigStep x h).1 0 = x.1 0 + 1 := by simp [bigStep, unitZero]
      rw [stepIdx_inl_pos x h, center_inl_apply, center_inl_apply, hb]
      push_cast
      linarith
    · have hx0 : x.1 0 = 0 := by
        have := x.2
        omega
      have hz : (zeroLift x).1 0 = 0 := by simp [zeroLift]
      rw [stepIdx_inl_neg x h, center_inl_apply, center_inr_apply, hz, hx0,
        smallOffset_zero_val]
      have := sqrt_seven_bounds.1
      push_cast
      linarith
  · have hb : (smallStep y).1 0 = y.1 0 + 1 := by simp [smallStep, unitZero]
    rw [stepIdx, center_inr_apply, center_inr_apply, hb]
    push_cast
    linarith

/-- The successor of an interior sphere lies in the closed region. -/
private lemma stepIdx_mem_closedRegion {c ρ : ℝ} {i : Idx k}
    (hi : c • center k i ∈ ball 0 ρ) :
    stepIdx i ∈ (packing k).closedRegion c (ball 0 ρ) := by
  by_cases h : c • center k (stepIdx i) ∈ ball 0 ρ
  · exact Or.inl h
  · exact Or.inr ⟨h, i, hi, tangent_stepIdx i⟩

/-- The norm of a centre bounds each of its coordinates. -/
private lemma abs_coord_le_norm (v : Euc (k + 3)) (j : Fin (k + 3)) : |v j| ≤ ‖v‖ := by
  have := PiLp.norm_apply_le v j
  rwa [Real.norm_eq_abs] at this

/-- An interior sphere has centre norm below `ρ / c`. -/
private lemma norm_center_lt_of_mem {c : ℝ} (hc : 0 < c) {ρ : ℝ} {i : Idx k}
    (hi : c • center k i ∈ ball (0 : Euc (k + 3)) ρ) : ‖center k i‖ < ρ / c := by
  rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hc.le] at hi
  exact (lt_div_iff₀ hc).2 (by linarith [mul_comm c ‖center k i‖])

/-- An interior sphere has zeroth centre coordinate below `ρ / c`. -/
private lemma center_zero_lt_of_mem {c : ℝ} (hc : 0 < c) {ρ : ℝ} {i : Idx k}
    (hi : c • center k i ∈ ball (0 : Euc (k + 3)) ρ) : center k i 0 < ρ / c :=
  lt_of_le_of_lt ((le_abs_self _).trans (abs_coord_le_norm _ 0))
    (norm_center_lt_of_mem hc hi)

/-- The integer vectors whose coordinates are bounded by `⌈T + 2⌉`. -/
private noncomputable def box (T : ℝ) : Finset (Fin (k + 3) → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-⌈T + 2⌉) ⌈T + 2⌉

private lemma mem_box {T : ℝ} {z : Fin (k + 3) → ℤ} (hz : ∀ j, |(z j : ℝ)| ≤ T + 2) :
    z ∈ box T := by
  rw [box, Fintype.mem_piFinset]
  intro j
  rw [Finset.mem_Icc]
  obtain ⟨h1, h2⟩ := abs_le.1 (hz j)
  have hc := Int.le_ceil (T + 2)
  constructor
  · have : ((-⌈T + 2⌉ : ℤ) : ℝ) ≤ (z j : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  · have : (z j : ℝ) ≤ ((⌈T + 2⌉ : ℤ) : ℝ) := by linarith
    exact_mod_cast this

/-- The coordinates of a big centre are bounded by its norm plus `2`. -/
private lemma abs_inl_coord_le (x : BigIdx k) (j : Fin (k + 3)) :
    |(x.1 j : ℝ)| ≤ ‖center k (.inl x)‖ + 2 := by
  have h := abs_le.1 (abs_coord_le_norm (center k (.inl x)) j)
  rw [center_inl_apply] at h
  have := norm_nonneg (center k (.inl x))
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

/-- The coordinates of a small centre are bounded by its norm plus `2`. -/
private lemma abs_inr_coord_le (y : SmallIdx k) (j : Fin (k + 3)) :
    |(y.1 j : ℝ)| ≤ ‖center k (.inr y)‖ + 2 := by
  have h := abs_le.1 (abs_coord_le_norm (center k (.inr y)) j)
  have ho := abs_le.1 (abs_smallOffset_le j)
  rw [center_inr_apply] at h
  have := norm_nonneg (center k (.inr y))
  rw [abs_le]
  constructor <;> linarith [h.1, h.2, ho.1, ho.2]

/-- Only finitely many spheres have centre norm below any bound. -/
private lemma finite_norm_lt (T : ℝ) : {i : Idx k | ‖center k i‖ < T}.Finite := by
  have hF := ((box T).finite_toSet.image
      (Sum.inl : (Fin (k + 3) → ℤ) → (Fin (k + 3) → ℤ) ⊕ (Fin (k + 3) → ℤ))).union
    ((box T).finite_toSet.image
      (Sum.inr : (Fin (k + 3) → ℤ) → (Fin (k + 3) → ℤ) ⊕ (Fin (k + 3) → ℤ)))
  have hinj : Function.Injective
      (Sum.map (fun x : BigIdx k => x.1) (fun y : SmallIdx k => y.1)) :=
    Sum.map_injective.2 ⟨Subtype.val_injective, Subtype.val_injective⟩
  refine (hF.preimage hinj.injOn).subset ?_
  rintro (x | y) hi
  · have hx : ‖center k (.inl x)‖ < T := hi
    exact Or.inl ⟨x.1, Finset.mem_coe.2 (mem_box fun j =>
      (abs_inl_coord_le x j).trans (by linarith)), rfl⟩
  · have hy : ‖center k (.inr y)‖ < T := hi
    exact Or.inr ⟨y.1, Finset.mem_coe.2 (mem_box fun j =>
      (abs_inr_coord_le y j).trans (by linarith)), rfl⟩

private lemma radius_le_one_idx (i : Idx k) : radius k i ≤ 1 := by
  rcases i with x | y <;> norm_num [radius]

/-- Finitely many spheres have scaled centre in a ball, together with their neighbours. -/
theorem closedRegion_finite {c : ℝ} (hc : 0 < c) (ρ : ℝ) :
    ((packing k).closedRegion c (ball 0 ρ)).Finite := by
  refine (finite_norm_lt (ρ / c + 2)).subset ?_
  rintro j (hj | ⟨-, i, hi, hadj⟩)
  · have := norm_center_lt_of_mem hc hj
    show ‖center k j‖ < ρ / c + 2
    linarith
  · have hd : dist (center k i) (center k j) = radius k i + radius k j := hadj.2
    have htri := dist_triangle (center k j) (center k i) 0
    rw [dist_comm (center k j) (center k i), hd, dist_zero_right, dist_zero_right] at htri
    have := norm_center_lt_of_mem hc hi
    have h1 := radius_le_one_idx i
    have h2 := radius_le_one_idx j
    show ‖center k j‖ < ρ / c + 2
    linarith

/-- Membership of a tangent pair in the unit network. -/
private lemma unitNetwork_pos_iff (R : Set (packing k).ι) [Fintype R] (v w : R) :
    0 < ((packing k).unitNetwork R).a v w ↔ (packing k).Tangent v w := by
  unfold SpherePacking.unitNetwork
  dsimp only
  split_ifs with h <;> simp [h]

/-- From an interior sphere, `k` steps of `stepIdx` through the closed region reach a sphere
outside the interior, adjacent along a path inside the network. -/
private lemma exists_chain {c ρ : ℝ} (hc : 0 < c) (R : Finset (packing k).ι)
    (hR : (packing k).closedRegion c (ball 0 ρ) ⊆ (R : Set (packing k).ι)) :
    ∀ n : ℕ, ∀ v : R, c • center k v.val ∈ ball 0 ρ →
      ρ / c - center k v.val 0 ≤ n → ∃ w : R, c • center k w.val ∉ ball 0 ρ ∧
        Relation.ReflTransGen
          (fun a b : R => 0 < ((packing k).unitNetwork (R : Set (packing k).ι)).a a b) v w := by
  intro n
  induction n with
  | zero =>
    intro v hv hn
    exfalso
    have h0 := center_zero_lt_of_mem hc hv
    push_cast at hn
    linarith
  | succ n ih =>
    intro v hv hn
    have hmem : stepIdx v.val ∈ (R : Set (packing k).ι) := hR (stepIdx_mem_closedRegion hv)
    have hadj : 0 < ((packing k).unitNetwork (R : Set (packing k).ι)).a v
        ⟨stepIdx v.val, hmem⟩ :=
      (unitNetwork_pos_iff _ _ _).2 (tangent_stepIdx v.val)
    by_cases hu : c • center k (stepIdx v.val) ∈ ball 0 ρ
    · have hstep := center_stepIdx v.val
      have hn' : ρ / c - center k (stepIdx v.val) 0 ≤ n := by
        push_cast at hn
        linarith
      obtain ⟨w, hw, hpath⟩ := ih ⟨stepIdx v.val, hmem⟩ hu hn'
      exact ⟨w, hw, Relation.ReflTransGen.head hadj hpath⟩
    · exact ⟨⟨stepIdx v.val, hmem⟩, hu, Relation.ReflTransGen.single hadj⟩

/-- From every sphere with scaled centre in the ball, the walk can leave the ball within any finite
set of spheres containing the closed region. -/
theorem boundaryAccessible_unitNetwork {c : ℝ} (hc : 0 < c) (ρ : ℝ) (R : Finset (packing k).ι)
    (hR : (packing k).closedRegion c (ball 0 ρ) ⊆ (R : Set (packing k).ι)) :
    ((packing k).unitNetwork (R : Set (packing k).ι)).BoundaryAccessible
      {v : R | c • center k v.val ∈ ball 0 ρ} := by
  intro v hv
  exact exists_chain hc R hR ⌈ρ / c - center k v.val 0⌉₊ v hv (Nat.le_ceil _)

theorem exists_isStoppedSRWLaw {c : ℝ} (hc : 0 < c) (ρ : ℝ) :
    ∃ μ : Measure (CurveSpace (k + 3)),
      (packing k).IsStoppedSRWLaw c (ball 0 ρ) (origin k) μ := by
  let S : Set (packing k).ι := (packing k).closedRegion c (ball 0 ρ) ∪ {origin k}
  have hS : S.Finite := (closedRegion_finite (k := k) hc ρ).union (Set.finite_singleton _)
  let R : Finset (packing k).ι := hS.toFinset
  have hR : (R : Set (packing k).ι) = S := hS.coe_toFinset
  have hsub : (packing k).closedRegion c (ball 0 ρ) ⊆ (R : Set (packing k).ι) := by
    rw [hR]
    exact Set.subset_union_left
  let _ : MeasurableSpace R := ⊤
  let A : Set R := {v | c • center k v.val ∈ ball 0 ρ}
  let N := (packing k).unitNetwork (R : Set (packing k).ι)
  have haccess : N.BoundaryAccessible A := by
    intro v hv
    obtain ⟨w, hw, hpath⟩ :=
      exists_chain hc R hsub ⌈ρ / c - center k v.val 0⌉₊ v hv (Nat.le_ceil _)
    exact ⟨w, hw, hpath⟩
  let hpos := N.totalConductance_pos_of_boundaryAccessible A haccess
  let start : R := ⟨origin k, hS.mem_toFinset.2 (Or.inr (Set.mem_singleton _))⟩
  refine ⟨(N.trajectoryLaw A hpos start).map
    (stoppedPolygonalCurve (fun v : R => c • (packing k).center v.val) A), ?_⟩
  unfold SpherePacking.IsStoppedSRWLaw
  refine ⟨R, hR, hpos, start, rfl, ?_, ?_, ?_, rfl⟩
  · exact aemeasurable_stoppedPolygonalCurve _ _ _
  · exact N.trajectoryLaw_ae_finiteExit A hpos haccess start
  · exact stoppedPolygonalCurve_map_isProbabilityMeasure _ _ _

end SpherePackings.Counterexample
