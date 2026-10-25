module

public import SpherePackings.Support.Counterexample.Construction

@[expose] public section

/-!
# Disjointness and tangency in the packing of Theorem 6.1
-/

open Metric

namespace SpherePackings.Counterexample

variable (k : ℕ)

/-- The squared distance is the sum of squared coordinate differences. -/
private lemma dist_sq_eq_sum {n : ℕ} (a b : EuclideanSpace ℝ (Fin n)) :
    dist a b ^ 2 = ∑ j, (a j - b j) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp [Real.dist_eq, sq_abs]

/-- Splitting off the first three coordinates of a sum over `Fin (n + 3)`. -/
private lemma sum_fin_add_three {n : ℕ} (f : Fin (n + 3) → ℝ) :
    ∑ j, f j = f 0 + f 1 + f 2 + ∑ i : Fin n, f i.succ.succ.succ := by
  simp [Fin.sum_univ_succ, add_assoc]

/-- A property of the coordinates `j ≥ 3` is a property of the tail indices. -/
private lemma forall_fin_three_iff {P : Fin (k + 3) → Prop} :
    (∀ i : Fin k, P i.succ.succ.succ) ↔ ∀ j : Fin (k + 3), 3 ≤ j.val → P j := by
  constructor
  · intro h j hj
    have hlt := j.isLt
    have hj' : j = (⟨j.val - 3, by omega⟩ : Fin k).succ.succ.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    rw [hj']
    exact h _
  · intro h i
    exact h _ (by simp only [Fin.val_succ]; omega)

/-- Sum of squares of an integer vector that is not zero is at least one. -/
private lemma one_le_sum_sq {n : ℕ} {u v : Fin n → ℤ} (h : u ≠ v) :
    1 ≤ ∑ j, (u j - v j) ^ 2 := by
  have hnn : 0 ≤ ∑ j, (u j - v j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hne : ∑ j, (u j - v j) ^ 2 ≠ 0 := by
    intro h0
    rw [Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg _] at h0
    refine h (funext fun j => sub_eq_zero.1 ?_)
    exact (pow_eq_zero_iff two_ne_zero).1 (h0 j (Finset.mem_univ j))
  omega

private lemma radius_nonneg (i : Idx k) : 0 ≤ radius k i := by
  rcases i with x | y <;> norm_num [radius]

private lemma smallOffset_zero : smallOffset k 0 = Real.sqrt 7 / 2 := by
  simp [smallOffset]

private lemma smallOffset_one : smallOffset k 1 = 1 / 2 := by
  simp [smallOffset]

private lemma smallOffset_two : smallOffset k 2 = 1 / 2 := by
  have h : ((2 : Fin (k + 3)) : ℕ) = 2 := Nat.mod_eq_of_lt (show 2 < k + 3 by omega)
  simp only [smallOffset, PiLp.toLp_apply, h]
  norm_num

private lemma smallOffset_succ_three (i : Fin k) : smallOffset k i.succ.succ.succ = 0 := by
  simp [smallOffset]

private lemma center_inl_apply (x : BigIdx k) (j : Fin (k + 3)) :
    center k (.inl x) j = 2 * (x.1 j : ℝ) := by
  simp [center]

private lemma center_inr_apply (y : SmallIdx k) (j : Fin (k + 3)) :
    center k (.inr y) j = smallOffset k j + (y.1 j : ℝ) := by
  simp [center]

private lemma dist_inl_inl_sq (x x' : BigIdx k) :
    dist (center k (.inl x)) (center k (.inl x')) ^ 2 =
      4 * ((∑ j, (x.1 j - x'.1 j) ^ 2 : ℤ) : ℝ) := by
  rw [dist_sq_eq_sum]
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by simp only [center_inl_apply]; ring

private lemma dist_inr_inr_sq (y y' : SmallIdx k) :
    dist (center k (.inr y)) (center k (.inr y')) ^ 2 =
      ((∑ j, (y.1 j - y'.1 j) ^ 2 : ℤ) : ℝ) := by
  rw [dist_sq_eq_sum]
  push_cast
  exact Finset.sum_congr rfl fun j _ => by simp only [center_inr_apply]; ring

private lemma dist_inl_inr_sq (x : BigIdx k) (y : SmallIdx k) :
    dist (center k (.inl x)) (center k (.inr y)) ^ 2 =
      (Real.sqrt 7 / 2 + ((y.1 0 - 2 * x.1 0 : ℤ) : ℝ)) ^ 2 +
        (1 / 2 + ((y.1 1 - 2 * x.1 1 : ℤ) : ℝ)) ^ 2 +
        (1 / 2 + ((y.1 2 - 2 * x.1 2 : ℤ) : ℝ)) ^ 2 +
        ((∑ i : Fin k, (y.1 i.succ.succ.succ - 2 * x.1 i.succ.succ.succ) ^ 2 : ℤ) : ℝ) := by
  have htail : ∀ i : Fin k,
      (center k (.inl x) i.succ.succ.succ - center k (.inr y) i.succ.succ.succ) ^ 2 =
        ((y.1 i.succ.succ.succ - 2 * x.1 i.succ.succ.succ : ℤ) : ℝ) ^ 2 := by
    intro i
    rw [center_inl_apply, center_inr_apply, smallOffset_succ_three]
    push_cast
    ring
  rw [dist_sq_eq_sum, sum_fin_add_three, Finset.sum_congr rfl fun i _ => htail i]
  simp only [center_inl_apply, center_inr_apply, smallOffset_zero, smallOffset_one,
    smallOffset_two]
  push_cast
  ring

/-- The polynomial identity behind the big–small distance, using `(√7)² = 7`. -/
private lemma big_small_identity (a t0 t1 t2 R : ℝ) (ha : a ^ 2 = 7) :
    (a / 2 + t0) ^ 2 + (1 / 2 + t1) ^ 2 + (1 / 2 + t2) ^ 2 + R =
      9 / 4 + ((a * t0 + t0 ^ 2) + (t1 * (t1 + 1) + t2 * (t2 + 1)) + R) := by
  linear_combination (1 / 4 : ℝ) * ha

/-- `t (t + 1)` is nonnegative for an integer `t`. -/
private lemma int_mul_succ_nonneg (t : ℤ) : 0 ≤ t * (t + 1) := by
  rcases le_or_gt 0 t with h | h
  · exact mul_nonneg h (by omega)
  · have e : t * (t + 1) = (-t) * (-(t + 1)) := by ring
    rw [e]
    exact mul_nonneg (by omega) (by omega)

private lemma big_small_ge (a : ℝ) (ha : a ^ 2 = 7) (ha0 : 0 ≤ a) (t0 t1 t2 R : ℤ)
    (h0 : 0 ≤ t0) (hR : 0 ≤ R) :
    (9 / 4 : ℝ) ≤ (a / 2 + t0) ^ 2 + (1 / 2 + t1) ^ 2 + (1 / 2 + t2) ^ 2 + R := by
  have hA : (0 : ℝ) ≤ a * t0 := mul_nonneg ha0 (by exact_mod_cast h0)
  have hB : (0 : ℝ) ≤ (t0 : ℝ) ^ 2 := sq_nonneg _
  have hC : (0 : ℝ) ≤ (t1 : ℝ) * (t1 + 1) := by exact_mod_cast int_mul_succ_nonneg t1
  have hD : (0 : ℝ) ≤ (t2 : ℝ) * (t2 + 1) := by exact_mod_cast int_mul_succ_nonneg t2
  have hE : (0 : ℝ) ≤ R := by exact_mod_cast hR
  rw [big_small_identity a t0 t1 t2 R ha]
  linarith

private lemma big_small_iff (a : ℝ) (ha : a ^ 2 = 7) (ha0 : 0 ≤ a) (t0 t1 t2 R : ℤ)
    (h0 : 0 ≤ t0) (hR : 0 ≤ R) :
    (a / 2 + t0) ^ 2 + (1 / 2 + t1) ^ 2 + (1 / 2 + t2) ^ 2 + R = (9 / 4 : ℝ) ↔
      t0 = 0 ∧ t1 * (t1 + 1) = 0 ∧ t2 * (t2 + 1) = 0 ∧ R = 0 := by
  rw [big_small_identity a t0 t1 t2 R ha]
  have hA : (0 : ℝ) ≤ a * t0 := mul_nonneg ha0 (by exact_mod_cast h0)
  have hB : (0 : ℝ) ≤ (t0 : ℝ) ^ 2 := sq_nonneg _
  have hC : (0 : ℝ) ≤ (t1 : ℝ) * (t1 + 1) := by exact_mod_cast int_mul_succ_nonneg t1
  have hD : (0 : ℝ) ≤ (t2 : ℝ) * (t2 + 1) := by exact_mod_cast int_mul_succ_nonneg t2
  have hE : (0 : ℝ) ≤ R := by exact_mod_cast hR
  constructor
  · intro h
    have ht0 : (t0 : ℝ) ^ 2 = 0 := by linarith
    have hC0 : (t1 : ℝ) * (t1 + 1) = 0 := by linarith
    have hD0 : (t2 : ℝ) * (t2 + 1) = 0 := by linarith
    have hE0 : (R : ℝ) = 0 := by linarith
    have ht : (t0 : ℝ) = 0 := (pow_eq_zero_iff two_ne_zero).1 ht0
    exact ⟨by exact_mod_cast ht, by exact_mod_cast hC0, by exact_mod_cast hD0,
      by exact_mod_cast hE0⟩
  · rintro ⟨h0', h1', h2', h3'⟩
    have ht : (t0 : ℝ) = 0 := by exact_mod_cast h0'
    have hC0 : (t1 : ℝ) * (t1 + 1) = 0 := by exact_mod_cast h1'
    have hD0 : (t2 : ℝ) * (t2 + 1) = 0 := by exact_mod_cast h2'
    have hE0 : (R : ℝ) = 0 := by exact_mod_cast h3'
    rw [ht, hC0, hD0, hE0]
    ring

private lemma dist_inl_inr_sq_ge (x : BigIdx k) (y : SmallIdx k) :
    (9 / 4 : ℝ) ≤ dist (center k (.inl x)) (center k (.inr y)) ^ 2 := by
  have h0 : 0 ≤ y.1 0 - 2 * x.1 0 := by
    have := x.2
    have := y.2.1
    omega
  have hR : 0 ≤ ∑ i : Fin k, (y.1 i.succ.succ.succ - 2 * x.1 i.succ.succ.succ) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [dist_inl_inr_sq]
  exact big_small_ge (Real.sqrt 7) (Real.sq_sqrt (by norm_num)) (Real.sqrt_nonneg _) _ _ _ _ h0 hR

/-- Distinct spheres are at distance at least the sum of their radii. -/
lemma radius_add_le_dist (i j : Idx k) (hij : i ≠ j) :
    radius k i + radius k j ≤ dist (center k i) (center k j) := by
  refine (sq_le_sq₀ (add_nonneg (radius_nonneg k i) (radius_nonneg k j)) dist_nonneg).1 ?_
  rcases i with x | y <;> rcases j with x' | y'
  · have hx : x.1 ≠ x'.1 := fun h => hij (congrArg Sum.inl (Subtype.ext h))
    have h1 : (1 : ℝ) ≤ ((∑ l, (x.1 l - x'.1 l) ^ 2 : ℤ) : ℝ) := by
      exact_mod_cast one_le_sum_sq hx
    have hr : radius k (.inl x) + radius k (.inl x') = 2 := by norm_num [radius]
    rw [hr, dist_inl_inl_sq]
    linarith
  · have hr : radius k (.inl x) + radius k (.inr y') = 3 / 2 := by norm_num [radius]
    rw [hr]
    linarith [dist_inl_inr_sq_ge k x y']
  · have hr : radius k (.inr y) + radius k (.inl x') = 3 / 2 := by norm_num [radius]
    rw [hr, dist_comm]
    linarith [dist_inl_inr_sq_ge k x' y]
  · have hy : y.1 ≠ y'.1 := fun h => hij (congrArg Sum.inr (Subtype.ext h))
    have h1 : (1 : ℝ) ≤ ((∑ l, (y.1 l - y'.1 l) ^ 2 : ℤ) : ℝ) := by
      exact_mod_cast one_le_sum_sq hy
    have hr : radius k (.inr y) + radius k (.inr y') = 1 := by norm_num [radius]
    rw [hr, dist_inr_inr_sq]
    linarith

/-- The packing of Theorem 6.1 in dimension `k + 3`. -/
@[reducible] noncomputable def packing : SpherePacking (k + 3) where
  ι := Idx k
  center := center k
  radius := radius k
  radius_pos := by
    intro i
    rcases i with x | y <;> norm_num [radius]
  disjoint := fun _ _ hij => ball_disjoint_ball (radius_add_le_dist k _ _ hij)

variable {k}

/-- Two spheres of the packing touch iff they are distinct and the squared distance of their
centres is the square of the sum of their radii. -/
private lemma tangent_iff_sq (a b : Idx k) :
    (packing k).Tangent a b ↔
      a ≠ b ∧ dist (center k a) (center k b) ^ 2 = (radius k a + radius k b) ^ 2 := by
  change (a ≠ b ∧ dist (center k a) (center k b) = radius k a + radius k b) ↔ _
  refine and_congr_right fun _ => ?_
  exact ⟨fun h => by rw [h],
    fun h => (pow_left_inj₀ dist_nonneg
      (add_nonneg (radius_nonneg k a) (radius_nonneg k b)) two_ne_zero).1 h⟩

/-- Big spheres touch iff their index vectors differ by a unit vector. -/
theorem tangent_inl_inl (x x' : BigIdx k) :
    (packing k).Tangent (.inl x) (.inl x') ↔ ∑ j, (x.1 j - x'.1 j) ^ 2 = 1 := by
  rw [tangent_iff_sq, dist_inl_inl_sq]
  have hr : (radius k (.inl x) + radius k (.inl x')) ^ 2 = (4 : ℝ) := by norm_num [radius]
  rw [hr]
  constructor
  · rintro ⟨-, h⟩
    have h' : ((∑ j, (x.1 j - x'.1 j) ^ 2 : ℤ) : ℝ) = 1 := by linarith
    exact_mod_cast h'
  · intro hS
    refine ⟨fun h => ?_, ?_⟩
    · obtain rfl := Sum.inl_injective h
      simp at hS
    · simp [hS]

/-- Small spheres touch iff their index vectors differ by a unit vector. -/
theorem tangent_inr_inr (y y' : SmallIdx k) :
    (packing k).Tangent (.inr y) (.inr y') ↔ ∑ j, (y.1 j - y'.1 j) ^ 2 = 1 := by
  rw [tangent_iff_sq, dist_inr_inr_sq]
  have hr : (radius k (.inr y) + radius k (.inr y')) ^ 2 = (1 : ℝ) := by norm_num [radius]
  rw [hr]
  constructor
  · rintro ⟨-, h⟩
    exact_mod_cast h
  · intro hS
    refine ⟨fun h => ?_, ?_⟩
    · obtain rfl := Sum.inr_injective h
      simp at hS
    · simp [hS]

/-- A big sphere and a small sphere touch iff the coordinate conditions of Theorem 6.1 hold. -/
theorem tangent_inl_inr (x : BigIdx k) (y : SmallIdx k) :
    (packing k).Tangent (.inl x) (.inr y) ↔
      x.1 0 = 0 ∧ y.1 0 = 0 ∧ (y.1 1 = 2 * x.1 1 ∨ y.1 1 = 2 * x.1 1 - 1) ∧
        (y.1 2 = 2 * x.1 2 ∨ y.1 2 = 2 * x.1 2 - 1) ∧
        ∀ j : Fin (k + 3), 3 ≤ j.val → y.1 j = 2 * x.1 j := by
  rw [tangent_iff_sq, and_iff_right Sum.inl_ne_inr]
  have hr : (radius k (.inl x) + radius k (.inr y)) ^ 2 = (9 / 4 : ℝ) := by
    norm_num [radius]
  have h0 : 0 ≤ y.1 0 - 2 * x.1 0 := by
    have := x.2
    have := y.2.1
    omega
  have hR : 0 ≤ ∑ i : Fin k, (y.1 i.succ.succ.succ - 2 * x.1 i.succ.succ.succ) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [hr, dist_inl_inr_sq,
    big_small_iff (Real.sqrt 7) (Real.sq_sqrt (by norm_num)) (Real.sqrt_nonneg _) _ _ _ _ h0 hR]
  have hR_iff : (∑ i : Fin k, (y.1 i.succ.succ.succ - 2 * x.1 i.succ.succ.succ) ^ 2) = 0 ↔
      ∀ j : Fin (k + 3), 3 ≤ j.val → y.1 j = 2 * x.1 j := by
    rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg _]
    simp only [Finset.mem_univ, true_implies, pow_eq_zero_iff two_ne_zero, sub_eq_zero]
    exact forall_fin_three_iff (k := k) (P := fun j => y.1 j = 2 * x.1 j)
  rw [hR_iff]
  have hx := x.2
  have hy := y.2.1
  constructor
  · rintro ⟨h0', h1', h2', h3'⟩
    refine ⟨by omega, by omega, ?_, ?_, h3'⟩
    · rcases mul_eq_zero.1 h1' with h | h <;> omega
    · rcases mul_eq_zero.1 h2' with h | h <;> omega
  · rintro ⟨hx0, hy0, h1', h2', h3'⟩
    exact ⟨by omega, mul_eq_zero.2 (by omega), mul_eq_zero.2 (by omega), h3'⟩

/-- Tangency is symmetric. -/
theorem tangent_comm (a b : Idx k) : (packing k).Tangent a b ↔ (packing k).Tangent b a := by
  rw [tangent_iff_sq, tangent_iff_sq, dist_comm (center k a), add_comm (radius k a)]
  exact and_congr ne_comm Iff.rfl

end SpherePackings.Counterexample
