module

public import SpherePackings.Support.Voronoi.GeometricConstraint

@[expose] public section

/-!
# From cube counts to inner and outer balls of Voronoi cells

The deterministic step of the proof of Proposition 1.1 (`rw-spheres.tex:1690-1764`).  If every cube
of the `k`-grid near `U` contains a point and every cube of the `r`-grid near `U` contains at most
one, then every Voronoi cell meeting `U` contains the ball of radius `r` around its point and lies in
the ball of radius `4 k √d`.  The centres of these cells lie within `k √d` of `U`, and Lemma 5.1 is
applied to that neighbourhood.
-/

open Metric

namespace SpherePackings.Voronoi

variable {d : ℕ}

/-- Cube counts near `U` bound every Voronoi cell meeting `U` between two balls.  Here `δ` and `R`
are constants for which Lemma 5.1(b) holds, and the occupied cubes have half-side
`min δ (1/4) · k`. -/
theorem cell_between_balls_of_counts (hd : 1 ≤ d) {δ R : ℝ} (hδ : 0 < δ) (hR : 0 ≤ R)
    (hδ5 : ∀ (U S : Set (EuclideanSpace ℝ (Fin d))) (k : ℝ), 0 < k →
      (∀ y ∈ grid k ∩ cthickening (R * k) U, (S ∩ cube y (δ * k)).Nonempty) →
      ∀ s ∈ S ∩ U, cell S s ⊆ ball s (4 * k * Real.sqrt d))
    {U S : Set (EuclideanSpace ℝ (Fin d))} {ρ k r : ℝ} (hk : 0 < k) (hr : 0 < r)
    (hscale : (R + 3 * Real.sqrt d) * k ≤ ρ)
    (hscale' : 2 * r * Real.sqrt d + k * Real.sqrt d ≤ ρ)
    (hE : ∀ y ∈ grid k ∩ cthickening ρ U, (S ∩ cube y (min δ (1 / 4) * k)).Nonempty)
    (hF : ∀ x ∈ grid r ∩ cthickening ρ U, (S ∩ cube x (2 * r)).Subsingleton) :
    ∀ s ∈ S, (cell S s ∩ U).Nonempty →
      closedBall s r ⊆ cell S s ∧ cell S s ⊆ ball s (4 * k * Real.sqrt d) := by
  intro s hs ⟨y, hyc, hyU⟩
  have hsd : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hks : 0 ≤ k * Real.sqrt d := mul_nonneg hk.le hsd
  have hδ' : 0 < min δ (1 / 4) := lt_min hδ (by norm_num)
  have hRk : 0 ≤ R * k := mul_nonneg hR hk.le
  have h3 : 3 * k * Real.sqrt d ≤ ρ := by nlinarith
  -- The point `s` lies within `k √d` of `U`.
  obtain ⟨g, hgG, hgy⟩ := exists_grid_near hk y
  have hgy' : dist g y ≤ k / 2 * Real.sqrt d := dist_le_mul_sqrt g y (by positivity) hgy
  have hgU : g ∈ cthickening ρ U :=
    mem_cthickening_of_dist_le g y ρ U hyU (by nlinarith)
  obtain ⟨s'', hs''S, hs''c⟩ := hE g ⟨hgG, hgU⟩
  have hs''g : dist s'' g ≤ min δ (1 / 4) * k * Real.sqrt d :=
    dist_le_mul_sqrt s'' g (by positivity) hs''c
  have hmin : min δ (1 / 4) * k * Real.sqrt d ≤ 1 / 4 * (k * Real.sqrt d) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (min_le_right _ _) hks
  have hsy : dist s y ≤ k * Real.sqrt d := by
    calc dist s y ≤ dist s'' y := hyc s'' hs''S
      _ ≤ dist s'' g + dist g y := dist_triangle _ _ _
      _ ≤ k * Real.sqrt d := by nlinarith
  have hsU' : s ∈ cthickening (k * Real.sqrt d) U :=
    mem_cthickening_of_dist_le s y _ U hyU hsy
  refine ⟨?_, ?_⟩
  · -- Inner ball, from Lemma 5.1(a) on the `k √d`-neighbourhood of `U`.
    refine geometric_constraint_inner (cthickening (k * Real.sqrt d) U) S hr ?_ s ⟨hs, hsU'⟩
    intro x ⟨hxG, hxU⟩
    apply hF x ⟨hxG, ?_⟩
    have := cthickening_cthickening_subset (by positivity : (0 : ℝ) ≤ 2 * r * Real.sqrt d) hks U hxU
    exact cthickening_mono hscale' U this
  · -- Outer ball, from Lemma 5.1(b) on the same neighbourhood.
    refine hδ5 (cthickening (k * Real.sqrt d) U) S k hk ?_ s ⟨hs, hsU'⟩
    intro x ⟨hxG, hxU⟩
    have hx3 := cthickening_cthickening_subset hRk hks U hxU
    obtain ⟨p, hpS, hpc⟩ := hE x ⟨hxG, cthickening_mono (by nlinarith) U hx3⟩
    refine ⟨p, hpS, fun j => (hpc j).trans ?_⟩
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) hk.le

end SpherePackings.Voronoi
