module

public import SpherePackings.Support.Counterexample.Tangency

@[expose] public section

/-!
# Covered spheres, and the packing of Theorem 6.1 in dimension three

In dimension three every sphere of the packing of Theorem 6.1 is covered
(`SpherePacking.Covered`, Section 1.2.1 of the paper, `rw-spheres.tex:331-333`): each sphere has
tangent neighbours whose tangent half-spaces bound every coordinate of a point of their intersection.
-/

open Metric

namespace SpherePackings

open BouRabeeGwynne

namespace Counterexample

/-- The inner product of two vectors of `ℝ³`, in coordinates. -/
private lemma inner_three (u w : Euc (0 + 3)) :
    inner ℝ u w = u 0 * w 0 + u 1 * w 1 + u 2 * w 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three]
  ring

private lemma center_big_apply (x : BigIdx 0) (j : Fin (0 + 3)) :
    center 0 (.inl x) j = 2 * (x.1 j : ℝ) := by
  simp [center]

private lemma center_small_apply (y : SmallIdx 0) (j : Fin (0 + 3)) :
    center 0 (.inr y) j = smallOffset 0 j + (y.1 j : ℝ) := by
  simp [center]

private lemma smallOffset_zero' : smallOffset 0 0 = Real.sqrt 7 / 2 := by
  simp [smallOffset]

private lemma smallOffset_one' : smallOffset 0 1 = 1 / 2 := by
  simp [smallOffset]

private lemma smallOffset_two' : smallOffset 0 2 = 1 / 2 := by
  simp [smallOffset]

/-- A tangent pair gives its half-space inequality, with the radii and the distance substituted. -/
private lemma halfspace_coord {i j : Idx 0} (hij : (packing 0).Tangent i j) {z : Euc (0 + 3)}
    (hz : z ∈ (packing 0).tangentHalfspace i j) :
    inner ℝ (z - center 0 i) (center 0 j - center 0 i) ≤
      radius 0 i * (radius 0 i + radius 0 j) := by
  have h2 : dist (center 0 i) (center 0 j) = radius 0 i + radius 0 j := hij.2
  have h3 : inner ℝ (z - center 0 i) (center 0 j - center 0 i) ≤
      radius 0 i * dist (center 0 i) (center 0 j) := hz
  rw [h2] at h3
  exact h3

/-- A set whose points have coordinates `0, 1, 2` within `3` of those of `c` is bounded. -/
private lemma isBounded_of_coord_le (c : Euc (0 + 3)) (S : Set (Euc (0 + 3)))
    (h : ∀ z ∈ S, |z 0 - c 0| ≤ 3 ∧ |z 1 - c 1| ≤ 3 ∧ |z 2 - c 2| ≤ 3) :
    Bornology.IsBounded S := by
  refine (Metric.isBounded_closedBall (x := c) (r := 6)).subset fun z hz => ?_
  obtain ⟨h0, h1, h2⟩ := h z hz
  rw [mem_closedBall, EuclideanSpace.dist_eq, Real.sqrt_le_left (by norm_num), Fin.sum_univ_three]
  have e0 : dist (z 0) (c 0) ^ 2 ≤ 3 ^ 2 := by
    rw [Real.dist_eq]
    exact pow_le_pow_left₀ (abs_nonneg _) h0 2
  have e1 : dist (z 1) (c 1) ^ 2 ≤ 3 ^ 2 := by
    rw [Real.dist_eq]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have e2 : dist (z 2) (c 2) ^ 2 ≤ 3 ^ 2 := by
    rw [Real.dist_eq]
    exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  linarith

/-- A product of two reals of absolute value at most `1/2` is at least `-1/4`. -/
private lemma neg_quarter_le_mul {p q : ℝ} (hp : |p| ≤ 1 / 2) (hq : |q| ≤ 1 / 2) :
    -(1 / 4) ≤ p * q := by
  have h : |p * q| ≤ 1 / 4 := by
    rw [abs_mul]
    nlinarith [abs_nonneg p, abs_nonneg q]
  linarith [neg_abs_le (p * q)]

private lemma one_le_sqrt_seven : (1 : ℝ) ≤ Real.sqrt 7 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), Real.sqrt_nonneg 7]

/-- Big spheres with `x₀ ≤ -1`: the neighbours `x ± e_l` bound each coordinate by `1`. -/
private lemma covered_big_neg (x : BigIdx 0) (hx : x.1 0 ≤ -1) :
    (packing 0).Covered (.inl x) := by
  unfold SpherePacking.Covered
  refine isBounded_of_coord_le (center 0 (.inl x)) _ fun z hz => ?_
  have hn : ∀ j, (packing 0).Tangent (.inl x) j →
      z ∈ (packing 0).tangentHalfspace (.inl x) j :=
    fun j hj => Set.mem_iInter₂.1 hz j hj
  have hp0 : (packing 0).Tangent (.inl x) (.inl ⟨fun j => x.1 j + ![1, 0, 0] j, by simp; omega⟩) :=
    (tangent_inl_inl _ _).2 (by simp [Fin.sum_univ_three])
  have hm0 : (packing 0).Tangent (.inl x) (.inl ⟨fun j => x.1 j + ![-1, 0, 0] j, by simp; omega⟩) :=
    (tangent_inl_inl _ _).2 (by simp [Fin.sum_univ_three])
  have hp1 : (packing 0).Tangent (.inl x) (.inl ⟨fun j => x.1 j + ![0, 1, 0] j, by simp; omega⟩) :=
    (tangent_inl_inl _ _).2 (by simp [Fin.sum_univ_three])
  have hm1 : (packing 0).Tangent (.inl x) (.inl ⟨fun j => x.1 j + ![0, -1, 0] j, by simp; omega⟩) :=
    (tangent_inl_inl _ _).2 (by simp [Fin.sum_univ_three])
  have hp2 : (packing 0).Tangent (.inl x) (.inl ⟨fun j => x.1 j + ![0, 0, 1] j, by simp; omega⟩) :=
    (tangent_inl_inl _ _).2 (by simp [Fin.sum_univ_three])
  have hm2 : (packing 0).Tangent (.inl x) (.inl ⟨fun j => x.1 j + ![0, 0, -1] j, by simp; omega⟩) :=
    (tangent_inl_inl _ _).2 (by simp [Fin.sum_univ_three])
  have e0p := halfspace_coord hp0 (hn _ hp0)
  have e0m := halfspace_coord hm0 (hn _ hm0)
  have e1p := halfspace_coord hp1 (hn _ hp1)
  have e1m := halfspace_coord hm1 (hn _ hm1)
  have e2p := halfspace_coord hp2 (hn _ hp2)
  have e2m := halfspace_coord hm2 (hn _ hm2)
  simp [inner_three, center_big_apply, radius] at e0p e0m e1p e1m e2p e2m
  simp only [center_big_apply]
  refine ⟨abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by linarith, by linarith⟩,
    abs_le.2 ⟨by linarith, by linarith⟩⟩

/-- Big spheres with `x₀ = 0`: the neighbours `x - e_0`, `x ± e_1`, `x ± e_2` and the two small
neighbours `(0, 2x₁, 2x₂)` and `(0, 2x₁ - 1, 2x₂ - 1)` bound the coordinates. -/
private lemma covered_big_zero (x : BigIdx 0) (hx : x.1 0 = 0) :
    (packing 0).Covered (.inl x) := by
  unfold SpherePacking.Covered
  refine isBounded_of_coord_le (center 0 (.inl x)) _ fun z hz => ?_
  have hn : ∀ j, (packing 0).Tangent (.inl x) j →
      z ∈ (packing 0).tangentHalfspace (.inl x) j :=
    fun j hj => Set.mem_iInter₂.1 hz j hj
  have hm0 : (packing 0).Tangent (.inl x) (.inl ⟨fun j => x.1 j + ![-1, 0, 0] j, by simp; omega⟩) :=
    (tangent_inl_inl _ _).2 (by simp [Fin.sum_univ_three])
  have hp1 : (packing 0).Tangent (.inl x) (.inl ⟨fun j => x.1 j + ![0, 1, 0] j, by simp; omega⟩) :=
    (tangent_inl_inl _ _).2 (by simp [Fin.sum_univ_three])
  have hm1 : (packing 0).Tangent (.inl x) (.inl ⟨fun j => x.1 j + ![0, -1, 0] j, by simp; omega⟩) :=
    (tangent_inl_inl _ _).2 (by simp [Fin.sum_univ_three])
  have hp2 : (packing 0).Tangent (.inl x) (.inl ⟨fun j => x.1 j + ![0, 0, 1] j, by simp; omega⟩) :=
    (tangent_inl_inl _ _).2 (by simp [Fin.sum_univ_three])
  have hm2 : (packing 0).Tangent (.inl x) (.inl ⟨fun j => x.1 j + ![0, 0, -1] j, by simp; omega⟩) :=
    (tangent_inl_inl _ _).2 (by simp [Fin.sum_univ_three])
  have hs1 : (packing 0).Tangent (.inl x) (.inr ⟨![0, 2 * x.1 1, 2 * x.1 2],
      by simp, fun j hj => absurd hj (by have := j.isLt; omega)⟩) :=
    (tangent_inl_inr _ _).2 ⟨hx, by simp, by simp, by simp,
      fun j hj => absurd hj (by have := j.isLt; omega)⟩
  have hs2 : (packing 0).Tangent (.inl x) (.inr ⟨![0, 2 * x.1 1 - 1, 2 * x.1 2 - 1],
      by simp, fun j hj => absurd hj (by have := j.isLt; omega)⟩) :=
    (tangent_inl_inr _ _).2 ⟨hx, by simp, by simp, by simp,
      fun j hj => absurd hj (by have := j.isLt; omega)⟩
  have f0m := halfspace_coord hm0 (hn _ hm0)
  have f1p := halfspace_coord hp1 (hn _ hp1)
  have f1m := halfspace_coord hm1 (hn _ hm1)
  have f2p := halfspace_coord hp2 (hn _ hp2)
  have f2m := halfspace_coord hm2 (hn _ hm2)
  have g1 := halfspace_coord hs1 (hn _ hs1)
  have g2 := halfspace_coord hs2 (hn _ hs2)
  simp [inner_three, center_big_apply, center_small_apply, smallOffset_zero', smallOffset_one',
    smallOffset_two', radius, hx] at f0m f1p f1m f2p f2m g1 g2
  simp only [center_big_apply, hx, Int.cast_zero, mul_zero, sub_zero]
  have hu0 : z 0 ≤ 3 := by
    nlinarith [one_le_sqrt_seven, Real.sqrt_nonneg 7, Real.mul_self_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]
  refine ⟨abs_le.2 ⟨by linarith, hu0⟩, abs_le.2 ⟨by linarith, by linarith⟩,
    abs_le.2 ⟨by linarith, by linarith⟩⟩

/-- Small spheres with `y₀ ≥ 1`: the neighbours `y ± e_l` bound each coordinate by `1/2`. -/
private lemma covered_small_pos (y : SmallIdx 0) (hy : 1 ≤ y.1 0) :
    (packing 0).Covered (.inr y) := by
  unfold SpherePacking.Covered
  refine isBounded_of_coord_le (center 0 (.inr y)) _ fun z hz => ?_
  have hn : ∀ j, (packing 0).Tangent (.inr y) j →
      z ∈ (packing 0).tangentHalfspace (.inr y) j :=
    fun j hj => Set.mem_iInter₂.1 hz j hj
  have hp0 : (packing 0).Tangent (.inr y) (.inr ⟨fun j => y.1 j + ![1, 0, 0] j,
      by simp; omega, fun j hj => absurd hj (by have := j.isLt; omega)⟩) :=
    (tangent_inr_inr _ _).2 (by simp [Fin.sum_univ_three])
  have hm0 : (packing 0).Tangent (.inr y) (.inr ⟨fun j => y.1 j + ![-1, 0, 0] j,
      by simp; omega, fun j hj => absurd hj (by have := j.isLt; omega)⟩) :=
    (tangent_inr_inr _ _).2 (by simp [Fin.sum_univ_three])
  have hp1 : (packing 0).Tangent (.inr y) (.inr ⟨fun j => y.1 j + ![0, 1, 0] j,
      by simp; omega, fun j hj => absurd hj (by have := j.isLt; omega)⟩) :=
    (tangent_inr_inr _ _).2 (by simp [Fin.sum_univ_three])
  have hm1 : (packing 0).Tangent (.inr y) (.inr ⟨fun j => y.1 j + ![0, -1, 0] j,
      by simp; omega, fun j hj => absurd hj (by have := j.isLt; omega)⟩) :=
    (tangent_inr_inr _ _).2 (by simp [Fin.sum_univ_three])
  have hp2 : (packing 0).Tangent (.inr y) (.inr ⟨fun j => y.1 j + ![0, 0, 1] j,
      by simp; omega, fun j hj => absurd hj (by have := j.isLt; omega)⟩) :=
    (tangent_inr_inr _ _).2 (by simp [Fin.sum_univ_three])
  have hm2 : (packing 0).Tangent (.inr y) (.inr ⟨fun j => y.1 j + ![0, 0, -1] j,
      by simp; omega, fun j hj => absurd hj (by have := j.isLt; omega)⟩) :=
    (tangent_inr_inr _ _).2 (by simp [Fin.sum_univ_three])
  have e0p := halfspace_coord hp0 (hn _ hp0)
  have e0m := halfspace_coord hm0 (hn _ hm0)
  have e1p := halfspace_coord hp1 (hn _ hp1)
  have e1m := halfspace_coord hm1 (hn _ hm1)
  have e2p := halfspace_coord hp2 (hn _ hp2)
  have e2m := halfspace_coord hm2 (hn _ hm2)
  simp [inner_three, center_small_apply, smallOffset_zero', smallOffset_one',
    smallOffset_two', radius] at e0p e0m e1p e1m e2p e2m
  simp only [center_small_apply, smallOffset_zero', smallOffset_one', smallOffset_two']
  refine ⟨abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by linarith, by linarith⟩,
    abs_le.2 ⟨by linarith, by linarith⟩⟩

/-- Small spheres with `y₀ = 0`: the neighbours `y + e_0`, `y ± e_1`, `y ± e_2` bound `u₀ ≤ 1/2`
and `|u_1|, |u_2| ≤ 1/2`, and the big neighbour `(0, a, b)` with `2a - y₁ ∈ {0, 1}` and
`2b - y₂ ∈ {0, 1}` bounds `u₀` from below. -/
private lemma covered_small_zero (y : SmallIdx 0) (hy : y.1 0 = 0) :
    (packing 0).Covered (.inr y) := by
  unfold SpherePacking.Covered
  refine isBounded_of_coord_le (center 0 (.inr y)) _ fun z hz => ?_
  have hn : ∀ j, (packing 0).Tangent (.inr y) j →
      z ∈ (packing 0).tangentHalfspace (.inr y) j :=
    fun j hj => Set.mem_iInter₂.1 hz j hj
  obtain ⟨a, ha0, ha1⟩ : ∃ a : ℤ, 0 ≤ 2 * a - y.1 1 ∧ 2 * a - y.1 1 ≤ 1 :=
    ⟨(y.1 1 + 1) / 2, by omega⟩
  obtain ⟨b, hb0, hb1⟩ : ∃ b : ℤ, 0 ≤ 2 * b - y.1 2 ∧ 2 * b - y.1 2 ≤ 1 :=
    ⟨(y.1 2 + 1) / 2, by omega⟩
  have hp0 : (packing 0).Tangent (.inr y) (.inr ⟨fun j => y.1 j + ![1, 0, 0] j,
      by simp; omega, fun j hj => absurd hj (by have := j.isLt; omega)⟩) :=
    (tangent_inr_inr _ _).2 (by simp [Fin.sum_univ_three])
  have hp1 : (packing 0).Tangent (.inr y) (.inr ⟨fun j => y.1 j + ![0, 1, 0] j,
      by simp; omega, fun j hj => absurd hj (by have := j.isLt; omega)⟩) :=
    (tangent_inr_inr _ _).2 (by simp [Fin.sum_univ_three])
  have hm1 : (packing 0).Tangent (.inr y) (.inr ⟨fun j => y.1 j + ![0, -1, 0] j,
      by simp; omega, fun j hj => absurd hj (by have := j.isLt; omega)⟩) :=
    (tangent_inr_inr _ _).2 (by simp [Fin.sum_univ_three])
  have hp2 : (packing 0).Tangent (.inr y) (.inr ⟨fun j => y.1 j + ![0, 0, 1] j,
      by simp; omega, fun j hj => absurd hj (by have := j.isLt; omega)⟩) :=
    (tangent_inr_inr _ _).2 (by simp [Fin.sum_univ_three])
  have hm2 : (packing 0).Tangent (.inr y) (.inr ⟨fun j => y.1 j + ![0, 0, -1] j,
      by simp; omega, fun j hj => absurd hj (by have := j.isLt; omega)⟩) :=
    (tangent_inr_inr _ _).2 (by simp [Fin.sum_univ_three])
  have hx : (packing 0).Tangent (.inr y) (.inl ⟨![0, a, b], by simp⟩) :=
    (tangent_comm _ _).1 ((tangent_inl_inr ⟨![0, a, b], by simp⟩ y).2 ⟨by simp, hy, by simp; omega,
      by simp; omega, fun j hj => absurd hj (by have := j.isLt; omega)⟩)
  have e0p := halfspace_coord hp0 (hn _ hp0)
  have e1p := halfspace_coord hp1 (hn _ hp1)
  have e1m := halfspace_coord hm1 (hn _ hm1)
  have e2p := halfspace_coord hp2 (hn _ hp2)
  have e2m := halfspace_coord hm2 (hn _ hm2)
  have eX := halfspace_coord hx (hn _ hx)
  simp [inner_three, center_big_apply, center_small_apply, smallOffset_zero', smallOffset_one',
    smallOffset_two', radius, hy] at e0p e1p e1m e2p e2m eX
  simp only [center_small_apply, smallOffset_zero', smallOffset_one', smallOffset_two', hy,
    Int.cast_zero, add_zero]
  have hu1 : |z 1 - (1 / 2 + (y.1 1 : ℝ))| ≤ 1 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
  have hu2 : |z 2 - (1 / 2 + (y.1 2 : ℝ))| ≤ 1 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
  have hq1 : |2 * (a : ℝ) - (1 / 2 + (y.1 1 : ℝ))| ≤ 1 / 2 := by
    have h0' : (0 : ℝ) ≤ 2 * (a : ℝ) - (y.1 1 : ℝ) := by exact_mod_cast ha0
    have h1' : 2 * (a : ℝ) - (y.1 1 : ℝ) ≤ 1 := by exact_mod_cast ha1
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have hq2 : |2 * (b : ℝ) - (1 / 2 + (y.1 2 : ℝ))| ≤ 1 / 2 := by
    have h0' : (0 : ℝ) ≤ 2 * (b : ℝ) - (y.1 2 : ℝ) := by exact_mod_cast hb0
    have h1' : 2 * (b : ℝ) - (y.1 2 : ℝ) ≤ 1 := by exact_mod_cast hb1
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have hk1 := neg_quarter_le_mul hu1 hq1
  have hk2 := neg_quarter_le_mul hu2 hq2
  refine ⟨abs_le.2 ⟨?_, by linarith⟩, abs_le.2 ⟨by linarith, by linarith⟩,
    abs_le.2 ⟨by linarith, by linarith⟩⟩
  nlinarith [one_le_sqrt_seven, Real.sqrt_nonneg 7, Real.mul_self_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]

/-- In dimension three every sphere of the packing of Theorem 6.1 is covered. -/
theorem packing_covered (i : Idx 0) : (packing 0).Covered i := by
  rcases i with x | y
  · rcases lt_or_eq_of_le x.2 with h | h
    · exact covered_big_neg x (by omega)
    · exact covered_big_zero x h
  · rcases lt_or_eq_of_le y.2.1 with h | h
    · exact covered_small_pos y (by omega)
    · exact covered_small_zero y h.symm

end Counterexample

end SpherePackings
