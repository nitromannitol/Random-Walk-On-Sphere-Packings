module

public import BouRabeeGwynne.LipschitzDomain

@[expose] public section

/-!
# The unit ball is a Lipschitz domain

A guard on the hypotheses of Theorems A and B(b): the open unit ball satisfies the Lipschitz-chart
definition `BouRabeeGwynne.IsLipschitzDomain`.
-/

open Metric

namespace SpherePackings

open BouRabeeGwynne

/-- Plain-real form of the square-root estimate `|S - T| ≤ |a - b|`. -/
private lemma sqrt_sub_sqrt_abs_le_of_sq {a b S T : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ha' : a ≤ 1 / 2) (hb' : b ≤ 1 / 2) (hS : 0 ≤ S) (hT : 0 ≤ T)
    (hS2 : S ^ 2 = 1 - a ^ 2) (hT2 : T ^ 2 = 1 - b ^ 2) : |S - T| ≤ |a - b| := by
  have ha2 : a ^ 2 ≤ 1 / 4 := by nlinarith
  have hb2 : b ^ 2 ≤ 1 / 4 := by nlinarith
  have hS1 : 1 / 2 ≤ S := by nlinarith
  have hT1 : 1 / 2 ≤ T := by nlinarith
  have h1 : (S - T) * (S + T) = -((a - b) * (a + b)) := by linear_combination hS2 - hT2
  have h2 : |S - T| * (S + T) = |a - b| * (a + b) := by
    calc |S - T| * (S + T) = |(S - T) * (S + T)| := by
          rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ S + T)]
      _ = |a - b| * (a + b) := by
          rw [h1, abs_neg, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ a + b)]
  have h3 : |S - T| ≤ |S - T| * (S + T) := le_mul_of_one_le_right (abs_nonneg _) (by linarith)
  have h4 : |a - b| * (a + b) ≤ |a - b| := mul_le_of_le_one_right (abs_nonneg _) (by linarith)
  linarith

/-- Plain-real form of the bound `|1 - S| < 1/2`. -/
private lemma abs_one_sub_lt_half_of_sq {a S : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1 / 2)
    (hS : 0 ≤ S) (hS2 : S ^ 2 = 1 - a ^ 2) : |1 - S| < 1 / 2 := by
  have ha2 : a ^ 2 ≤ 1 / 4 := by nlinarith
  have h1 : 1 / 2 < S := by nlinarith
  have h2 : S ≤ 1 := by nlinarith [sq_nonneg a]
  rw [abs_lt]
  constructor <;> linarith

private lemma one_sub_sq_nonneg_of_le_half {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1 / 2) :
    0 ≤ 1 - a ^ 2 := by
  nlinarith

/-- The square-root graph function `1 - √(1 - a²)` is `1`-Lipschitz on `[0, 1/2]`. -/
private lemma abs_sqrt_sub_sqrt_le_half {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ha' : a ≤ 1 / 2) (hb' : b ≤ 1 / 2) :
    |Real.sqrt (1 - a ^ 2) - Real.sqrt (1 - b ^ 2)| ≤ |a - b| :=
  sqrt_sub_sqrt_abs_le_of_sq ha hb ha' hb' (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (Real.sq_sqrt (one_sub_sq_nonneg_of_le_half ha ha'))
    (Real.sq_sqrt (one_sub_sq_nonneg_of_le_half hb hb'))

/-- The square-root graph function is strictly within `1/2` of `1` on `[0, 1/2]`. -/
private lemma abs_one_sub_sqrt_lt_half {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1 / 2) :
    |1 - Real.sqrt (1 - a ^ 2)| < 1 / 2 :=
  abs_one_sub_lt_half_of_sq ha ha' (Real.sqrt_nonneg _)
    (Real.sq_sqrt (one_sub_sq_nonneg_of_le_half ha ha'))

private lemma abs_min_half_sub_min_half_le (s t : ℝ) :
    |min s (1 / 2) - min t (1 / 2)| ≤ |s - t| := by
  have h := abs_min_sub_min_le_max s (1 / 2 : ℝ) t (1 / 2)
  rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)] at h
  exact h

private lemma lt_one_iff_sq_of_nonneg {x : ℝ} (hx : 0 ≤ x) : x < 1 ↔ x ^ 2 < 1 := by
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

/-- The defining inequality of the graph: `(1 - t)² + s² < 1` iff `1 - √(1 - s²) < t`. -/
private lemma sphere_lt_iff_sqrt {s t : ℝ} (ht : t < 1) :
    (1 - t) ^ 2 + s ^ 2 < 1 ↔ 1 - Real.sqrt (1 - s ^ 2) < t := by
  have h : 1 - Real.sqrt (1 - s ^ 2) < t ↔ 1 - t < Real.sqrt (1 - s ^ 2) := by
    constructor <;> intro h <;> linarith
  rw [h, Real.lt_sqrt (by linarith : (0 : ℝ) ≤ 1 - t)]
  constructor <;> intro h <;> linarith

/-- The squared norm of the cylinder coordinates `(q, t)`. -/
private lemma norm_sq_cylinderCoordinates {d : ℕ} (q : Euc (d - 1)) (t : ℝ) :
    ‖cylinderCoordinates q t‖ ^ 2 = t ^ 2 + ‖q‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fintype.sum_option]
  simp [cylinderCoordinates]

private lemma inner_single_none_cylinderCoordinates {d : ℕ} (q : Euc (d - 1)) (t : ℝ) :
    inner ℝ (EuclideanSpace.single none (1 : ℝ)) (cylinderCoordinates q t) = t := by
  rw [EuclideanSpace.inner_single_left]
  simp [cylinderCoordinates]

/-- An isometry of `Euc d` onto the cylinder index space, sending `-p` to the vertical unit vector.
-/
private lemma exists_isometry_neg_point {d : ℕ} (hd : 1 ≤ d) {p : Euc d} (hp : ‖p‖ = 1) :
    ∃ R : Euc d ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Option (Fin (d - 1))),
      R.symm (EuclideanSpace.single none 1) = -p := by
  have hcard : Module.finrank ℝ (Euc d) = Fintype.card (Option (Fin (d - 1))) := by
    rw [finrank_euclideanSpace_fin, Fintype.card_option, Fintype.card_fin]
    omega
  have hv : Orthonormal ℝ (({none} : Set (Option (Fin (d - 1)))).domRestrict fun _ => -p) := by
    unfold Orthonormal
    refine ⟨fun i => ?_, ?_⟩
    · simpa [Set.domRestrict_apply] using hp
    · intro i j hij
      exact absurd (Subtype.ext ((Set.mem_singleton_iff.1 i.2).trans
        (Set.mem_singleton_iff.1 j.2).symm)) hij
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard hv
  exact ⟨b.repr, by rw [OrthonormalBasis.repr_symm_single, hb none (Set.mem_singleton none)]⟩

/-- The open unit ball is a Lipschitz domain. -/
theorem isLipschitzDomain_ball {d : ℕ} (hd : 1 ≤ d) : IsLipschitzDomain (ball (0 : Euc d) 1) := by
  unfold IsLipschitzDomain BouRabeeGwynne.IsDomain HasLipschitzBoundary
  refine ⟨⟨isOpen_ball, ⟨0, mem_ball_self one_pos⟩,
    (convex_ball 0 1).isPreconnected⟩, ?_⟩
  intro p hp
  rw [frontier_ball _ one_ne_zero, mem_sphere_zero_iff_norm] at hp
  obtain ⟨R, hR⟩ := exists_isometry_neg_point hd hp
  refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, R,
    fun q => 1 - Real.sqrt (1 - (min ‖q‖ (1 / 2)) ^ 2), 1, ?_, ?_, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
    have hx : 0 ≤ min ‖x‖ (1 / 2) := le_min (norm_nonneg _) (by norm_num)
    have hy : 0 ≤ min ‖y‖ (1 / 2) := le_min (norm_nonneg _) (by norm_num)
    have key := abs_sqrt_sub_sqrt_le_half hx hy (min_le_right _ _) (min_le_right _ _)
    have e : ∀ u v : ℝ, |1 - u - (1 - v)| = |u - v| := fun u v => by
      rw [show 1 - u - (1 - v) = -(u - v) by ring, abs_neg]
    rw [e]
    exact key.trans ((abs_min_half_sub_min_half_le _ _).trans (abs_norm_sub_norm_le x y))
  · dsimp only
    rw [norm_zero, min_eq_left (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num
  · intro q _
    have ha : 0 ≤ min ‖q‖ (1 / 2) := le_min (norm_nonneg _) (by norm_num)
    exact abs_one_sub_sqrt_lt_half ha (min_le_right _ _)
  · intro q t hq ht
    have hq' : ‖q‖ ≤ 1 / 2 := hq.le
    have ht' : t < 1 := by linarith [(abs_lt.1 ht).2]
    have hnorm : ‖p + R.symm (cylinderCoordinates q t)‖ ^ 2 = (1 - t) ^ 2 + ‖q‖ ^ 2 := by
      have h1 := R.symm.inner_map_map (EuclideanSpace.single none (1 : ℝ))
        (cylinderCoordinates q t)
      rw [hR, inner_single_none_cylinderCoordinates, inner_neg_left] at h1
      rw [norm_add_sq_real, hp, LinearIsometryEquiv.norm_map, norm_sq_cylinderCoordinates]
      linear_combination (-2 : ℝ) * h1
    show p + R.symm (cylinderCoordinates q t) ∈ ball 0 1 ↔
      1 - Real.sqrt (1 - (min ‖q‖ (1 / 2)) ^ 2) < t
    rw [min_eq_left hq', mem_ball_zero_iff,
      lt_one_iff_sq_of_nonneg (norm_nonneg (p + R.symm (cylinderCoordinates q t))), hnorm]
    exact sphere_lt_iff_sqrt ht'

end SpherePackings
