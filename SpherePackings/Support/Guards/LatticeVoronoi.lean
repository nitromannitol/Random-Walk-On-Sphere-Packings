module

public import SpherePackings.Support.Voronoi.Tiling
public import SpherePackings.Support.Voronoi.GridCount
public import SpherePackings.Support.Voronoi.GeometricConstraint

@[expose] public section

/-!
# Voronoi cells of the lattice `h ℤ^d`

The Voronoi cell of a point of `h ℤ^d` is the cube of half-side `h/2` around it.  Hence the lattice
satisfies `GoodVoronoi` on every bounded set, which gives orthogonal tilings with small mesh: a guard
that the hypotheses of Theorems A and B are satisfiable.
-/

open Metric

namespace SpherePackings.Voronoi

open BouRabeeGwynne

variable {d : ℕ}

/-- The point `s` with its `j`-th coordinate shifted by `c`. -/
private def moveCoord (s : EuclideanSpace ℝ (Fin d)) (j : Fin d) (c : ℝ) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => if i = j then s j + c else s i)

private lemma moveCoord_apply_self (s : EuclideanSpace ℝ (Fin d)) (j : Fin d) (c : ℝ) :
    moveCoord s j c j = s j + c := by
  simp [moveCoord]

private lemma moveCoord_apply_ne {s : EuclideanSpace ℝ (Fin d)} {j i : Fin d} {c : ℝ}
    (hi : i ≠ j) : moveCoord s j c i = s i := by
  simp [moveCoord, hi]

/-- Shifting one coordinate of a point of `h ℤ^d` by `±h` gives a point of `h ℤ^d`. -/
private lemma moveCoord_mem_grid {h : ℝ} {s : EuclideanSpace ℝ (Fin d)} (hs : s ∈ grid h)
    (j : Fin d) {c : ℝ} (hc : c = h ∨ c = -h) : moveCoord s j c ∈ grid h := by
  have hs' : ∀ i, ∃ m : ℤ, s i = h * m := hs
  intro i
  by_cases hij : i = j
  · rw [hij, moveCoord_apply_self]
    obtain ⟨m, hm⟩ := hs' j
    rcases hc with rfl | rfl
    · exact ⟨m + 1, by rw [hm]; push_cast; ring⟩
    · exact ⟨m - 1, by rw [hm]; push_cast; ring⟩
  · rw [moveCoord_apply_ne hij]
    exact hs' i

/-- The squared distance from `x` to `y` is the sum of the squared coordinate differences. -/
private lemma dist_sq_eq_sum (x y : EuclideanSpace ℝ (Fin d)) :
    dist x y ^ 2 = ∑ i, (x i - y i) ^ 2 := by
  have h0 : 0 ≤ ∑ i, dist (x i) (y i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt h0]
  exact Finset.sum_congr rfl fun i _ => by rw [Real.dist_eq, sq_abs]

/-- If `x'` and `x` agree off coordinate `j`, the squared distances to `y` differ only in
coordinate `j`. -/
private lemma dist_sq_sub_eq (x x' y : EuclideanSpace ℝ (Fin d)) (j : Fin d)
    (hx : ∀ i, i ≠ j → x' i = x i) :
    dist x' y ^ 2 - dist x y ^ 2 = (x' j - y j) ^ 2 - (x j - y j) ^ 2 := by
  have hsum : ∑ i, ((x' i - y i) ^ 2 - (x i - y i) ^ 2) = (x' j - y j) ^ 2 - (x j - y j) ^ 2 :=
    Finset.sum_eq_single j (fun i _ hi => by simp [hx i hi])
      fun h => absurd (Finset.mem_univ j) h
  rw [Finset.sum_sub_distrib] at hsum
  rw [dist_sq_eq_sum, dist_sq_eq_sum]
  exact hsum

/-- Along one coordinate, a point of `h ℤ` within `h/2` of `t` is at least as close to `t` as any
other point of `h ℤ`. -/
private lemma abs_sub_le_abs_sub_of_grid {h a b t : ℝ} (hh : 0 < h) (ha : ∃ m : ℤ, a = h * m)
    (hb : ∃ n : ℤ, b = h * n) (ht : |a - t| ≤ h / 2) : |a - t| ≤ |b - t| := by
  obtain ⟨m, rfl⟩ := ha
  obtain ⟨n, rfl⟩ := hb
  by_cases hmn : m = n
  · subst hmn
    exact le_rfl
  · have hk : (1 : ℝ) ≤ |(m : ℝ) - n| := by
      have : (1 : ℤ) ≤ |m - n| := Int.one_le_abs (sub_ne_zero.mpr hmn)
      exact_mod_cast this
    have hd : h ≤ |(h * m - t) - (h * n - t)| := by
      have e : (h * m - t) - (h * n - t) = h * ((m : ℝ) - n) := by ring
      rw [e, abs_mul, abs_of_pos hh]
      exact le_mul_of_one_le_right hh.le hk
    rcases abs_cases ((h * m - t) - (h * n - t)) with ⟨h1, s1⟩ | ⟨h1, s1⟩ <;>
      rcases abs_cases (h * n - t) with ⟨h2, s2⟩ | ⟨h2, s2⟩ <;>
      rcases abs_cases (h * m - t) with ⟨h3, s3⟩ | ⟨h3, s3⟩ <;>
      linarith

/-- The Voronoi cell of a point of the lattice `h ℤ^d` is the cube of half-side `h/2` around it. -/
theorem cell_grid_eq_cube {h : ℝ} (hh : 0 < h) {s : Euc d} (hs : s ∈ grid (d := d) h) :
    cell (grid h) s = cube s (h / 2) := by
  have hsg : ∀ j, ∃ m : ℤ, s j = h * m := hs
  refine Set.Subset.antisymm ?_ ?_
  · intro y hy j
    by_contra hlt
    have hgt : h / 2 < |y j - s j| := not_le.mp hlt
    have hstep : ∀ c : ℝ, (c = h ∨ c = -h) → (s j - y j) ^ 2 ≤ (s j + c - y j) ^ 2 := by
      intro c hc
      have h1 : dist s y ≤ dist (moveCoord s j c) y := hy _ (moveCoord_mem_grid hs j hc)
      have h2 := pow_le_pow_left₀ dist_nonneg h1 2
      have h3 := dist_sq_sub_eq s (moveCoord s j c) y j (fun i hi => moveCoord_apply_ne hi)
      rw [moveCoord_apply_self] at h3
      linarith
    rcases abs_cases (y j - s j) with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1] at hgt
      nlinarith [hstep h (Or.inl rfl), mul_pos hh (show (0 : ℝ) < 2 * (y j - s j) - h by linarith)]
    · rw [h1] at hgt
      nlinarith [hstep (-h) (Or.inr rfl),
        mul_pos hh (show (0 : ℝ) < -(2 * (y j - s j) + h) by linarith)]
  · intro y hy s' hs'
    have hy' : ∀ j, |y j - s j| ≤ h / 2 := hy
    have hs'g : ∀ j, ∃ n : ℤ, s' j = h * n := hs'
    rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => ?_)
    rw [Real.dist_eq, Real.dist_eq]
    exact pow_le_pow_left₀ (abs_nonneg _)
      (abs_sub_le_abs_sub_of_grid hh (hsg j) (hs'g j) (by rw [abs_sub_comm]; exact hy' j)) 2

/-- The lattice `h ℤ^d` satisfies `GoodVoronoi` on every bounded set, with inner radius `h/2` and
outer radius `h √d`. -/
theorem goodVoronoi_grid (hd : 1 ≤ d) {h : ℝ} (hh : 0 < h) {D : Set (Euc d)}
    (hD : Bornology.IsBounded D) :
    GoodVoronoi (grid (d := d) h) D (h / 2) (h * Real.sqrt d) := by
  have hd0 : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  have hR : 0 < h * Real.sqrt d := mul_pos hh (Real.sqrt_pos.mpr hd0)
  refine ⟨half_pos hh, hR, hD, ?_, ?_, ?_, ?_⟩
  · intro s hs
    rw [cell_grid_eq_cube hh hs.1]
    intro y hy j
    exact (abs_sub_coord_le_dist y s j).trans (mem_closedBall.mp hy)
  · intro s hs y hy
    rw [cell_grid_eq_cube hh hs.1] at hy
    have hy' : ∀ j, |y j - s j| ≤ h / 2 := hy
    rw [mem_closedBall]
    exact (dist_le_mul_sqrt y s (half_pos hh).le hy').trans
      (mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _))
  · obtain ⟨ρ, hρ⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Euc d)).mp
      (hD.cthickening (δ := 6 * (h * Real.sqrt d)))
    exact (finite_grid_inter_closedBall hh ρ).subset (Set.inter_subset_inter_right _ hρ)
  · intro y _
    obtain ⟨g, hg, hgy⟩ := exists_grid_near hh y
    refine ⟨g, hg, ?_⟩
    rw [cell_grid_eq_cube hh hg]
    intro j
    exact (abs_sub_comm (y j) (g j)).trans_le (hgy j)

end SpherePackings.Voronoi
