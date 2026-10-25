module

public import SpherePackings.Support.Voronoi.Basic
public import Mathlib.Analysis.Convex.Combination

@[expose] public section

/-!
# Lemma 5.2: the polar of a perturbed cross-polytope is bounded

`rw-spheres.tex:1650-1653` (label `lemma:dual-polytope-bound`).
-/

open Metric

namespace SpherePackings.Voronoi

variable {d : ℕ}

/-- The inner product on `EuclideanSpace ℝ (Fin d)` as a coordinate sum. -/
private lemma inner_eq_sum_mul (p y : EuclideanSpace ℝ (Fin d)) :
    inner ℝ p y = ∑ j, p j * y j := by
  simp [PiLp.inner_apply, mul_comm]

/-- Coordinates of a point of `cube 0 a` are bounded by `a`. -/
private lemma abs_coord_le_of_mem_cube {ε : EuclideanSpace ℝ (Fin d)} {a : ℝ}
    (h : ε ∈ cube 0 a) (j : Fin d) : |ε j| ≤ a := by
  have h' : ∀ j : Fin d, |ε j - (0 : EuclideanSpace ℝ (Fin d)) j| ≤ a := h
  simpa using h' j

/-- If every `|ε_j| ≤ 1/(4d)` and every `|y_j| ≤ |y_i|`, then `|⟪ε, y⟫| ≤ |y_i| / 4`. -/
private lemma abs_inner_le_quarter (hd : 1 ≤ d) (ε y : EuclideanSpace ℝ (Fin d)) (i : Fin d)
    (hε : ∀ j, |ε j| ≤ 1 / (4 * (d : ℝ))) (hmax : ∀ j, |y j| ≤ |y i|) :
    |inner ℝ ε y| ≤ |y i| / 4 := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < d).ne'
  rw [inner_eq_sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h : ∀ j ∈ (Finset.univ : Finset (Fin d)), |ε j * y j| ≤ 1 / (4 * (d : ℝ)) * |y i| := by
    intro j _
    rw [abs_mul]
    exact mul_le_mul (hε j) (hmax j) (abs_nonneg _) (by positivity)
  refine (Finset.sum_le_sum h).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- Lower bound `⟪ε + s • e_i, y⟫ ≥ (3/4) |y_i|` when `s * y_i = |y_i|`. -/
private lemma three_quarters_le_inner (hd : 1 ≤ d) (y : EuclideanSpace ℝ (Fin d)) (i : Fin d)
    (ε : EuclideanSpace ℝ (Fin d)) (s : ℝ) (hs : s * y i = |y i|)
    (hε : ∀ j, |ε j| ≤ 1 / (4 * (d : ℝ))) (hmax : ∀ j, |y j| ≤ |y i|) :
    3 / 4 * |y i| ≤ inner ℝ (ε + s • EuclideanSpace.single i (1 : ℝ)) y := by
  have h1 := abs_inner_le_quarter hd ε y i hε hmax
  have h2 := neg_abs_le (inner ℝ ε y)
  rw [inner_add_left, real_inner_smul_left, EuclideanSpace.inner_single_left]
  simp only [map_one, one_mul]
  linarith

/-- **Lemma 5.2** (`lemma:dual-polytope-bound`).  There is `δ' ∈ (0,1)`, depending only on `d`,
such that for every choice of points `x^{(i±)} ∈ [-δ', δ']^d ± e_i`, the polar
`P* = {y : x ⬝ y ≤ 1 for all x ∈ P}` of `P = conv(x^{(1+)}, x^{(1-)}, …, x^{(d+)}, x^{(d-)})`
lies in the ball `B_{2√d}`.  Here `x i true = x^{(i+)}` and `x i false = x^{(i-)}`. -/
theorem dual_polytope_bound (hd : 1 ≤ d) :
    ∃ δ' : ℝ, 0 < δ' ∧ δ' < 1 ∧
      ∀ x : Fin d → Bool → EuclideanSpace ℝ (Fin d),
        (∀ i b, x i b - (if b then (1 : ℝ) else -1) • EuclideanSpace.single i (1 : ℝ) ∈
          cube 0 δ') →
        {y : EuclideanSpace ℝ (Fin d) |
            ∀ p ∈ convexHull ℝ (Set.range (Function.uncurry x)), inner ℝ p y ≤ 1} ⊆
          ball 0 (2 * Real.sqrt d) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  refine ⟨1 / (4 * (d : ℝ)), div_pos one_pos (by linarith), ?_, ?_⟩
  · rw [div_lt_one (by linarith)]
    linarith
  intro x hx y hy
  have hy' : ∀ p ∈ convexHull ℝ (Set.range (Function.uncurry x)), inner ℝ p y ≤ 1 := hy
  -- a coordinate of `y` of maximal absolute value
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => |y j|)
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hmax : ∀ j, |y j| ≤ |y i| := fun j => hi j (Finset.mem_univ j)
  -- the sign of `y_i`
  obtain ⟨b, hb⟩ : ∃ b : Bool, (if b then (1 : ℝ) else -1) * y i = |y i| := by
    rcases le_total 0 (y i) with h0 | h0
    · exact ⟨true, by simp [abs_of_nonneg h0]⟩
    · exact ⟨false, by simp [abs_of_nonpos h0]⟩
  -- the point `x i b = ε + s • e_i` lies in the polar bound
  have hε := fun j => abs_coord_le_of_mem_cube (hx i b) j
  have hlow := three_quarters_le_inner hd y i _ _ hb hε hmax
  rw [sub_add_cancel] at hlow
  have hpoint : inner ℝ (x i b) y ≤ 1 :=
    hy' (x i b) (subset_convexHull ℝ _ (Set.mem_range_self (i, b)))
  have hyi : |y i| ≤ 4 / 3 := by linarith
  -- so every coordinate of `y` is at most `4/3`, and `‖y‖² ≤ 16d/9 < 4d`
  have hsum : ∑ j, ‖y j‖ ^ 2 ≤ ∑ _j : Fin d, (4 / 3 : ℝ) ^ 2 := by
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) ((hmax j).trans hyi) 2
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hS : ∑ j, ‖y j‖ ^ 2 < 4 * d := by linarith
  have h4 : (2 * Real.sqrt d) ^ 2 = 4 * d := by
    rw [mul_pow, Real.sq_sqrt hd0.le]
    norm_num
  rw [mem_ball_zero_iff, EuclideanSpace.norm_eq, Real.sqrt_lt' (mul_pos two_pos
    (Real.sqrt_pos.2 hd0)), h4]
  exact hS

end SpherePackings.Voronoi
