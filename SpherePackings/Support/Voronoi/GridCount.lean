module

public import SpherePackings.Support.Voronoi.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.PSeries

@[expose] public section

/-!
# Grid points in bounded sets, and two summable sequences

Counting estimates for the union bounds in the proof of Proposition 1.1
(`rw-spheres.tex:1690-1764`).
-/

open Metric Filter
open scoped Topology

namespace SpherePackings.Voronoi

variable {d : ℕ}

/-- The point of the mesh-`k` grid with integer coordinates `n`. -/
private def gridPt (k : ℝ) (n : Fin d → ℤ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j => k * n j)

private lemma exists_eq_gridPt {k : ℝ} {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ grid k) :
    ∃ n : Fin d → ℤ, x = gridPt k n := by
  have hx' : ∀ j, ∃ m : ℤ, x j = k * m := hx
  choose n hn using hx'
  exact ⟨n, PiLp.ext fun j => by simp [gridPt, hn j]⟩

/-- A set covered by the images of a finset of integer vectors has at most `T.card` points. -/
private lemma ncard_le_card_of_subset {k : ℝ} {A : Set (EuclideanSpace ℝ (Fin d))}
    {T : Finset (Fin d → ℤ)} (h : A ⊆ gridPt k '' ↑T) : A.ncard ≤ T.card :=
  (Set.ncard_le_ncard h (T.finite_toSet.image _)).trans <|
    (Set.ncard_image_le T.finite_toSet).trans (Set.ncard_coe_finset T).le

/-- If `|k m| ≤ R` for an integer `m`, then `|m| ≤ |R| / k`. -/
private lemma abs_cast_le_div {k R : ℝ} (hk : 0 < k) {m : ℤ} (h : |k * (m : ℝ)| ≤ R) :
    |(m : ℝ)| ≤ |R| / k := by
  rw [le_div_iff₀ hk]
  calc |(m : ℝ)| * k = |k * (m : ℝ)| := by rw [abs_mul, abs_of_pos hk]; ring
    _ ≤ R := h
    _ ≤ |R| := le_abs_self R

/-- An integer `m` with `|m| ≤ t` lies in `[-⌊t⌋, ⌊t⌋]`. -/
private lemma mem_Icc_floor_of_abs_le {m : ℤ} {t : ℝ} (h : |(m : ℝ)| ≤ t) :
    m ∈ Finset.Icc (-⌊t⌋) ⌊t⌋ := by
  rw [abs_le] at h
  rw [Finset.mem_Icc]
  constructor
  · have : -m ≤ ⌊t⌋ := Int.le_floor.mpr (by push_cast; linarith [h.1])
    linarith
  · exact Int.le_floor.mpr h.2

/-- Solving `|u - r v| ≤ 2 r` for `v` gives `u / r - 2 ≤ v ≤ u / r + 2`. -/
private lemma sub_two_le_le_add_two {r u v : ℝ} (hr : 0 < r) (h : |u - r * v| ≤ 2 * r) :
    u / r - 2 ≤ v ∧ v ≤ u / r + 2 := by
  rw [abs_le] at h
  constructor
  · have h' : u / r ≤ v + 2 := (div_le_iff₀ hr).mpr (by linarith [h.2])
    linarith
  · have h' : v - 2 ≤ u / r := (le_div_iff₀ hr).mpr (by linarith [h.1])
    linarith

/-- Grid points in `closedBall 0 R` have integer coordinates bounded by `|R| / k`. -/
private lemma grid_inter_closedBall_subset {k : ℝ} (hk : 0 < k) (R : ℝ) :
    grid (d := d) k ∩ closedBall 0 R ⊆
      gridPt k '' ↑(Fintype.piFinset fun _ : Fin d => Finset.Icc (-⌊|R| / k⌋) ⌊|R| / k⌋) := by
  rintro x ⟨hx, hxR⟩
  obtain ⟨n, rfl⟩ := exists_eq_gridPt hx
  refine ⟨n, ?_, rfl⟩
  have hR' := mem_closedBall_zero_iff.mp hxR
  have hj : ∀ j, |k * (n j : ℝ)| ≤ R := fun j => by
    have := (PiLp.norm_apply_le (gridPt k n) j).trans hR'
    simpa only [gridPt, PiLp.toLp_apply, Real.norm_eq_abs] using this
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  exact fun j => mem_Icc_floor_of_abs_le (abs_cast_le_div hk (hj j))

/-- Finitely many grid points lie in a ball. -/
theorem finite_grid_inter_closedBall {k : ℝ} (hk : 0 < k) (R : ℝ) :
    (grid (d := d) k ∩ closedBall 0 R).Finite :=
  Set.Finite.subset ((Finset.finite_toSet _).image _) (grid_inter_closedBall_subset hk R)

/-- At most `(2R/k + 1)^d` grid points of mesh `k` lie in `closedBall 0 R`. -/
theorem ncard_grid_inter_closedBall_le {k R : ℝ} (hk : 0 < k) (hR : 0 ≤ R) :
    ((grid (d := d) k ∩ closedBall 0 R).ncard : ℝ) ≤ (2 * R / k + 1) ^ d := by
  have hsub := grid_inter_closedBall_subset (d := d) hk R
  rw [abs_of_nonneg hR] at hsub
  have hN0 : 0 ≤ ⌊R / k⌋ := Int.floor_nonneg.mpr (div_nonneg hR hk.le)
  have hNle : (⌊R / k⌋ : ℝ) ≤ R / k := Int.floor_le _
  have h1 := ncard_le_card_of_subset hsub
  have hcard : (Fintype.piFinset fun _ : Fin d => Finset.Icc (-⌊R / k⌋) ⌊R / k⌋).card =
      (2 * ⌊R / k⌋ + 1).toNat ^ d := by
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Int.card_Icc, show ⌊R / k⌋ + 1 - -⌊R / k⌋ = 2 * ⌊R / k⌋ + 1 by ring]
  rw [hcard] at h1
  have h2 : ((grid (d := d) k ∩ closedBall 0 R).ncard : ℝ) ≤
      ((2 * ⌊R / k⌋ + 1).toNat : ℝ) ^ d := by
    rw [← Nat.cast_pow]
    exact_mod_cast h1
  have hcast : ((2 * ⌊R / k⌋ + 1).toNat : ℝ) = 2 * (⌊R / k⌋ : ℝ) + 1 := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (show (0 : ℤ) ≤ 2 * ⌊R / k⌋ + 1 by omega)]
    push_cast
    ring
  have hN' : (0 : ℝ) ≤ ⌊R / k⌋ := by exact_mod_cast hN0
  have h3 : 2 * (⌊R / k⌋ : ℝ) + 1 ≤ 2 * R / k + 1 := by
    rw [mul_div_assoc]
    linarith
  rw [hcast] at h2
  exact h2.trans (pow_le_pow_left₀ (by linarith) h3 d)

/-- A point lies in at most `5^d` of the cubes `x + [-2r, 2r]^d`, `x ∈ r ℤ^d`. -/
theorem ncard_grid_cube_mem_le {r : ℝ} (hr : 0 < r) (y : EuclideanSpace ℝ (Fin d)) :
    ({x | x ∈ grid r ∧ y ∈ cube x (2 * r)}.ncard : ℝ) ≤ 5 ^ d := by
  set T : Finset (Fin d → ℤ) :=
    Fintype.piFinset fun j : Fin d => Finset.Icc ⌈y j / r - 2⌉ ⌊y j / r + 2⌋ with hT
  have hsub : {x | x ∈ grid r ∧ y ∈ cube x (2 * r)} ⊆ gridPt r '' ↑T := by
    rintro x ⟨hx, hy⟩
    obtain ⟨n, rfl⟩ := exists_eq_gridPt hx
    refine ⟨n, ?_, rfl⟩
    have hy' : ∀ j, |y j - (gridPt r n) j| ≤ 2 * r := hy
    simp only [gridPt, PiLp.toLp_apply] at hy'
    rw [Finset.mem_coe, hT, Fintype.mem_piFinset]
    intro j
    obtain ⟨h1, h2⟩ := sub_two_le_le_add_two hr (hy' j)
    exact Finset.mem_Icc.mpr ⟨Int.ceil_le.mpr h1, Int.le_floor.mpr h2⟩
  have hcoord : ∀ j : Fin d, (Finset.Icc ⌈y j / r - 2⌉ ⌊y j / r + 2⌋).card ≤ 5 := fun j => by
    rw [Int.card_Icc]
    have h1 := Int.floor_le (y j / r + 2)
    have h2 := Int.le_ceil (y j / r - 2)
    have h3 : ⌊y j / r + 2⌋ - ⌈y j / r - 2⌉ ≤ 4 := by
      have : ((⌊y j / r + 2⌋ - ⌈y j / r - 2⌉ : ℤ) : ℝ) ≤ 4 := by push_cast; linarith
      exact_mod_cast this
    omega
  have hT5 : T.card ≤ 5 ^ d := by
    have h := Finset.prod_le_pow_card (Finset.univ : Finset (Fin d))
      (fun j => (Finset.Icc ⌈y j / r - 2⌉ ⌊y j / r + 2⌋).card) 5 (fun j _ => hcoord j)
    rw [Finset.card_univ, Fintype.card_fin] at h
    rw [hT, Fintype.card_piFinset]
    exact h
  have h1 := ncard_le_card_of_subset hsub
  exact_mod_cast h1.trans hT5

/-- `x ^ a` as `x ^ (-2)` times `(x ^ (1 / 2)) ^ (2 * a + 4)`, for `x > 0`. -/
private lemma rpow_eq_rpow_neg_two_mul {x : ℝ} (a : ℝ) (hx : 0 < x) :
    x ^ a = x ^ (-2 : ℝ) * (x ^ (1 / 2 : ℝ)) ^ (2 * a + 4) := by
  rw [← Real.rpow_mul hx.le, ← Real.rpow_add hx]
  congr 1
  ring

/-- Polynomial growth times stretched-exponential decay is summable. -/
theorem summable_rpow_mul_exp_neg_rpow (a : ℝ) {c : ℝ} (hc : 0 < c) :
    Summable fun m : ℕ => (m : ℝ) ^ a * Real.exp (-(c * (m : ℝ) ^ (1 / 2 : ℝ))) := by
  have hg : Summable fun m : ℕ => (m : ℝ) ^ (-2 : ℝ) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hk : Tendsto (fun x : ℝ => x ^ (2 * a + 4) * Real.exp (-(c * x))) atTop (𝓝 0) := by
    simpa only [neg_mul] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 * a + 4) c hc
  have hsqrt : Tendsto (fun m : ℕ => (m : ℝ) ^ (1 / 2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp tendsto_natCast_atTop_atTop
  have hlt := Tendsto.eventually_lt_const (by norm_num : (0 : ℝ) < 1) (hk.comp hsqrt)
  refine Summable.of_norm_bounded_eventually hg ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hlt, eventually_ge_atTop 1] with m hm hm1
  have hx : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have key : (m : ℝ) ^ a * Real.exp (-(c * (m : ℝ) ^ (1 / 2 : ℝ))) =
      (m : ℝ) ^ (-2 : ℝ) * (((m : ℝ) ^ (1 / 2 : ℝ)) ^ (2 * a + 4) *
        Real.exp (-(c * (m : ℝ) ^ (1 / 2 : ℝ)))) := by
    rw [rpow_eq_rpow_neg_two_mul a hx]
    ring
  have hP : 0 ≤ (m : ℝ) ^ (-2 : ℝ) * (((m : ℝ) ^ (1 / 2 : ℝ)) ^ (2 * a + 4) *
      Real.exp (-(c * (m : ℝ) ^ (1 / 2 : ℝ)))) := by
    positivity
  rw [Real.norm_eq_abs, key, abs_of_nonneg hP]
  exact mul_le_of_le_one_right (by positivity) hm.le

end SpherePackings.Voronoi
