module

public import SpherePackings.Support.Voronoi.Basic
public import BouRabeeGwynne.PaperObjects

@[expose] public section

/-!
# Bounded Voronoi cells are convex polytopes

For a locally finite point set, a Voronoi cell contained in a ball is cut out by the finitely many
bisecting halfspaces of display (1.7) (`rw-spheres.tex:347-350`) of points within four times that
radius.
-/

open Metric

namespace SpherePackings.Voronoi

open BouRabeeGwynne

variable {d : ℕ}

/-- Display (1.7): the halfspace form of the Voronoi inequality. -/
theorem dist_le_dist_iff_inner_le (s s' y : EuclideanSpace ℝ (Fin d)) :
    dist s y ≤ dist s' y ↔ inner ℝ (s' - s) y ≤ (‖s'‖ ^ 2 - ‖s‖ ^ 2) / 2 := by
  rw [dist_eq_norm, dist_eq_norm, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
    norm_sub_sq_real, norm_sub_sq_real, inner_sub_left]
  constructor <;> intro h <;> linarith

theorem convex_cell (S : Set (EuclideanSpace ℝ (Fin d))) (s : EuclideanSpace ℝ (Fin d)) :
    Convex ℝ (cell S s) := by
  intro x hx y hy a b ha hb hab s' hs'
  have key := add_le_add
    (mul_le_mul_of_nonneg_left ((dist_le_dist_iff_inner_le s s' x).1 (hx s' hs')) ha)
    (mul_le_mul_of_nonneg_left ((dist_le_dist_iff_inner_le s s' y).1 (hy s' hs')) hb)
  rw [← add_mul, hab, one_mul] at key
  rw [dist_le_dist_iff_inner_le, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  exact key

theorem isClosed_cell (S : Set (EuclideanSpace ℝ (Fin d))) (s : EuclideanSpace ℝ (Fin d)) :
    IsClosed (cell S s) := by
  have h : cell S s = ⋂ s' ∈ S, {y | dist s y ≤ dist s' y} := by
    ext y
    simp [cell]
  rw [h]
  exact isClosed_biInter fun s' _ => isClosed_le (by fun_prop) (by fun_prop)

/-- Shrinking a point of `D`-distance from `s` to a distance in `(R, 2 R]`. -/
private lemma exists_scale {R D : ℝ} (hR : 0 < R) (hD : R < D) :
    ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ R < t * D ∧ t * D ≤ 2 * R := by
  have hD0 : D ≠ 0 := (by linarith : (0 : ℝ) < D).ne'
  refine ⟨min 1 (2 * R / D), ⟨le_min zero_le_one (div_nonneg (by linarith) (by linarith)),
    min_le_left _ _⟩, ?_⟩
  have h2 : 2 * R / D * D = 2 * R := div_mul_cancel₀ _ hD0
  rw [min_mul_of_nonneg _ _ (by linarith), one_mul, h2]
  exact ⟨lt_min hD (by linarith), min_le_right _ _⟩

/-- A cell inside `closedBall s R` is cut out by the points of `S` within `4 R` of `s`. -/
theorem cell_eq_of_subset_closedBall (S : Set (EuclideanSpace ℝ (Fin d)))
    {s : EuclideanSpace ℝ (Fin d)} {R : ℝ} (hRpos : 0 < R) (hR : cell S s ⊆ closedBall s R) :
    cell S s = {y | ∀ s' ∈ S ∩ closedBall s (4 * R), dist s y ≤ dist s' y} := by
  -- The right-hand side is the cell of the truncated set `S ∩ closedBall s (4 * R)`.
  have hconv : Convex ℝ (cell (S ∩ closedBall s (4 * R)) s) := convex_cell _ s
  -- Points of the truncated cell within `2 R` of `s` lie in the full cell.
  have hA : ∀ y ∈ cell (S ∩ closedBall s (4 * R)) s, dist s y ≤ 2 * R → y ∈ cell S s := by
    intro y hy hy2 s' hs'
    by_cases h : s' ∈ closedBall s (4 * R)
    · exact hy s' ⟨hs', h⟩
    · rw [mem_closedBall, not_le] at h
      have htri := dist_triangle s' y s
      rw [dist_comm y s] at htri
      linarith
  -- Points of the truncated cell lie within `R` of `s`.
  have hB : ∀ y ∈ cell (S ∩ closedBall s (4 * R)) s, dist s y ≤ R := by
    intro y hy
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨t, ht01, hgt, hle⟩ := exists_scale hRpos hlt
    have hp := hconv.add_smul_sub_mem (self_mem_cell _ s) hy ht01
    have hdp : dist (s + t • (y - s)) s = t * dist s y := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht01.1,
        ← dist_eq_norm, dist_comm]
    have h3 : dist (s + t • (y - s)) s ≤ R :=
      mem_closedBall.1 (hR (hA _ hp (by rw [dist_comm, hdp]; exact hle)))
    rw [hdp] at h3
    linarith
  ext y
  constructor
  · intro hy s' hs'
    exact hy s' hs'.1
  · intro hy
    exact hA y hy (le_trans (hB y hy) (by linarith))

/-- The points of `S` within a closed ball of any center and radius form a finite set. -/
private lemma finite_inter_closedBall (S : Set (EuclideanSpace ℝ (Fin d)))
    (hS : ∀ R : ℝ, (S ∩ closedBall 0 R).Finite) (s : EuclideanSpace ℝ (Fin d)) (R : ℝ) :
    (S ∩ closedBall s R).Finite := by
  refine (hS (‖s‖ + R)).subset ?_
  rintro x ⟨hxS, hx⟩
  refine ⟨hxS, ?_⟩
  have h : dist x s ≤ R := mem_closedBall.1 hx
  rw [dist_eq_norm] at h
  have h2 := norm_add_le (x - s) s
  rw [sub_add_cancel] at h2
  rw [mem_closedBall_zero_iff]
  linarith

/-- A bounded Voronoi cell of a locally finite set, containing a ball around its point, as a
`ConvexPolytope`. -/
noncomputable def cellPolytope (S : Set (EuclideanSpace ℝ (Fin d)))
    (hS : ∀ R : ℝ, (S ∩ closedBall 0 R).Finite) (s : EuclideanSpace ℝ (Fin d)) {r R : ℝ}
    (hr : 0 < r) (hin : closedBall s r ⊆ cell S s) (hout : cell S s ⊆ closedBall s R) :
    ConvexPolytope d := by
  classical
  -- `max R 1` is positive and still bounds the cell.
  have hR : 0 < max R 1 := lt_max_of_lt_right zero_lt_one
  have hout' : cell S s ⊆ closedBall s (max R 1) :=
    hout.trans (closedBall_subset_closedBall (le_max_left R 1))
  have hfin := finite_inter_closedBall S hS s (4 * max R 1)
  exact {
    carrier := cell S s
    compact := isCompact_of_isClosed_isBounded (isClosed_cell S s)
      (Metric.isBounded_closedBall.subset hout)
    convex := convex_cell S s
    interior_nonempty := ⟨s, interior_maximal (ball_subset_closedBall.trans hin) isOpen_ball
      (mem_ball_self hr)⟩
    halfspaces := hfin.toFinset.image fun s' => (s' - s, (‖s'‖ ^ 2 - ‖s‖ ^ 2) / 2)
    halfspace_rep := by
      rw [cell_eq_of_subset_closedBall S hR hout']
      ext x
      simp only [Set.mem_ofPred_eq, Finset.mem_image, Set.Finite.mem_toFinset]
      constructor
      · rintro hx p ⟨s', hs', rfl⟩
        exact (dist_le_dist_iff_inner_le s s' x).1 (hx s' hs')
      · intro hx s' hs'
        exact (dist_le_dist_iff_inner_le s s' x).2 (hx _ ⟨s', hs', rfl⟩)
  }

@[simp] theorem cellPolytope_carrier (S : Set (EuclideanSpace ℝ (Fin d)))
    (hS : ∀ R : ℝ, (S ∩ closedBall 0 R).Finite) (s : EuclideanSpace ℝ (Fin d)) {r R : ℝ}
    (hr : 0 < r) (hin : closedBall s r ⊆ cell S s) (hout : cell S s ⊆ closedBall s R) :
    (cellPolytope S hS s hr hin hout).carrier = cell S s := by
  rfl

end SpherePackings.Voronoi
