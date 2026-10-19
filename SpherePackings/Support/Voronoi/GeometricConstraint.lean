import SpherePackings.Support.Voronoi.Basic
import SpherePackings.Support.Voronoi.GridCount

/-!
# Lemma 5.1: inner and outer balls for Voronoi cells

`rw-spheres.tex:1627-1642` (label `lemma:geometric-constraint`).  Part (a):
`geometric_constraint_inner_collar` (the grid cubes `x + [-r, r]^d` that meet `U`, as in the corrected
paper) and `geometric_constraint_inner_cube` (the cubes `x + [-2r, 2r]^d`);
`geometric_constraint_inner`, with the grid points in `B_{2r√d}(U)`, is the form used for
Proposition 1.1.  Part (b): `geometric_constraint_outer`, with constants `δ = δ(d)` and `R = R(d) ≥ 2`
(witnesses `δ = 1/10`, `R = max(2, 1.1√d)`), as in the corrected paper.
-/

open Metric

namespace SpherePackings.Voronoi

variable {d : ℕ}

/-- A coordinate difference is bounded by the distance. -/
lemma abs_sub_coord_le_dist (x y : EuclideanSpace ℝ (Fin d)) (j : Fin d) :
    |x j - y j| ≤ dist x y := by
  have h := PiLp.dist_apply_le x y j
  rwa [Real.dist_eq] at h

/-- If every coordinate difference is at most `a ≥ 0`, the distance is at most `a √d`. -/
lemma dist_le_mul_sqrt (x y : EuclideanSpace ℝ (Fin d)) {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ j, |x j - y j| ≤ a) : dist x y ≤ a * Real.sqrt d := by
  rw [EuclideanSpace.dist_eq]
  have h1 : ∑ j, dist (x j) (y j) ^ 2 ≤ ∑ _j : Fin d, a ^ 2 := by
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Real.dist_eq]
    exact pow_le_pow_left₀ (abs_nonneg _) (h j) 2
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  calc Real.sqrt (∑ j, dist (x j) (y j) ^ 2) ≤ Real.sqrt ((d : ℝ) * a ^ 2) :=
        Real.sqrt_le_sqrt h1
    _ = a * Real.sqrt d := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq ha]
        ring

/-- `t ≤ r ⌈t / r⌉ < t + r` for `r > 0`. -/
private lemma mul_ceil_bounds {r t : ℝ} (hr : 0 < r) :
    t ≤ r * ⌈t / r⌉ ∧ r * ⌈t / r⌉ < t + r := by
  have hr' : r ≠ 0 := hr.ne'
  constructor
  · calc t = r * (t / r) := (mul_div_cancel₀ t hr').symm
      _ ≤ r * ⌈t / r⌉ := mul_le_mul_of_nonneg_left (Int.le_ceil _) hr.le
  · calc r * (⌈t / r⌉ : ℝ) < r * (t / r + 1) := mul_lt_mul_of_pos_left (Int.ceil_lt_add_one _) hr
      _ = t + r := by rw [mul_add, mul_div_cancel₀ t hr', mul_one]

/-- Grid point just below the coordinatewise maximum of two points, at distance in `[r, 2r)`. -/
private lemma exists_grid_between {r : ℝ} (hr : 0 < r) (a b : EuclideanSpace ℝ (Fin d)) :
    ∃ x ∈ grid r, ∀ j, max (a j) (b j) - 2 * r ≤ x j ∧ x j < max (a j) (b j) - r := by
  refine ⟨WithLp.toLp 2 (fun j => r * ⌈(max (a j) (b j) - 2 * r) / r⌉), ?_, ?_⟩
  · intro j
    exact ⟨⌈(max (a j) (b j) - 2 * r) / r⌉, rfl⟩
  · intro j
    rw [PiLp.toLp_apply]
    have h := mul_ceil_bounds (t := max (a j) (b j) - 2 * r) hr
    constructor <;> linarith [h.1, h.2]

/-- `k * round (t / k)` is within `k / 2` of `t`. -/
private lemma abs_mul_round_sub_le {k : ℝ} (hk : 0 < k) (t : ℝ) :
    |k * round (t / k) - t| ≤ k / 2 := by
  have e : k * round (t / k) - t = k * (round (t / k) - t / k) := by
    rw [mul_sub, mul_div_cancel₀ t hk.ne']
  rw [e, abs_mul, abs_of_pos hk, abs_sub_comm]
  calc k * |t / k - round (t / k)| ≤ k * (1 / 2) :=
        mul_le_mul_of_nonneg_left (abs_sub_round _) hk.le
    _ = k / 2 := by ring

/-- Grid point within `k / 2` in every coordinate of a given point. -/
lemma exists_grid_near {k : ℝ} (hk : 0 < k) (p : EuclideanSpace ℝ (Fin d)) :
    ∃ g ∈ grid k, ∀ j, |g j - p j| ≤ k / 2 := by
  refine ⟨WithLp.toLp 2 (fun j => k * round (p j / k)), ?_, ?_⟩
  · intro j
    exact ⟨round (p j / k), rfl⟩
  · intro j
    rw [PiLp.toLp_apply]
    exact abs_mul_round_sub_le hk (p j)

/-- Lemma 5.1(a) with the grid points in `B_{2r√d}(U)`, a consequence of
`geometric_constraint_inner_cube`.  If every cube `x + [-2r, 2r]^d` centred at a grid point
`x ∈ r ℤ^d` within distance `2 r √d` of `U` contains at most one point of `S`, then
`B_r(s) ⊆ 𝒞_s` for every `s ∈ S ∩ U`. -/
theorem geometric_constraint_inner (U S : Set (EuclideanSpace ℝ (Fin d))) {r : ℝ} (hr : 0 < r)
    (h : ∀ x ∈ grid r ∩ cthickening (2 * r * Real.sqrt d) U, (S ∩ cube x (2 * r)).Subsingleton) :
    ∀ s ∈ S ∩ U, closedBall s r ⊆ cell S s := by
  rintro s ⟨hsS, hsU⟩ y hy s' hs'
  rw [mem_closedBall] at hy
  by_cases hss : s' = s
  · subst hss
    exact le_rfl
  · have hex : ∃ j, 3 * r < |s j - s' j| := by
      by_contra hcon
      simp only [not_exists, not_lt] at hcon
      obtain ⟨x, hxgrid, hxj⟩ := exists_grid_between hr s s'
      have hcs : ∀ j, |s j - x j| ≤ 2 * r := by
        intro j
        rw [abs_le]
        have hc := abs_le.mp (hcon j)
        have hm : max (s j) (s' j) ≤ s j + 3 * r :=
          max_le (by linarith) (by linarith [hc.1, hc.2])
        constructor <;> linarith [le_max_left (s j) (s' j), (hxj j).1, (hxj j).2]
      have hcs' : ∀ j, |s' j - x j| ≤ 2 * r := by
        intro j
        rw [abs_le]
        have hc := abs_le.mp (hcon j)
        have hm : max (s j) (s' j) ≤ s' j + 3 * r :=
          max_le (by linarith [hc.1, hc.2]) (by linarith)
        constructor <;> linarith [le_max_right (s j) (s' j), (hxj j).1, (hxj j).2]
      have hxU : x ∈ cthickening (2 * r * Real.sqrt d) U :=
        mem_cthickening_of_dist_le x s _ U hsU (by
          rw [dist_comm]
          exact dist_le_mul_sqrt s x (by positivity) hcs)
      exact hss (h x ⟨hxgrid, hxU⟩ ⟨hs', hcs'⟩ ⟨hsS, hcs⟩)
    obtain ⟨j, hj⟩ := hex
    have h1 : 3 * r < dist s' s := by
      rw [dist_comm]
      exact lt_of_lt_of_le hj (abs_sub_coord_le_dist s s' j)
    have h2 := dist_triangle s' y s
    linarith [dist_comm s y]

/-- **Lemma 5.1(a)**, corrected.  If every cube `x + [-2r, 2r]^d` centred at a grid point
`x ∈ r ℤ^d` that meets `U` contains at most one point of `S`, then `B_r(s) ⊆ 𝒞_s` for every
`s ∈ S ∩ U`.  (The printed version asks this only for `x ∈ U`; the proof uses the cubes that contain
a point of `U`.) -/
theorem geometric_constraint_inner_cube (U S : Set (EuclideanSpace ℝ (Fin d))) {r : ℝ} (hr : 0 < r)
    (h : ∀ x ∈ grid r, (cube x (2 * r) ∩ U).Nonempty → (S ∩ cube x (2 * r)).Subsingleton) :
    ∀ s ∈ S ∩ U, closedBall s r ⊆ cell S s := by
  rintro s ⟨hsS, hsU⟩ y hy s' hs'
  rw [mem_closedBall] at hy
  by_cases hss : s' = s
  · subst hss
    exact le_rfl
  · have hex : ∃ j, 3 * r < |s j - s' j| := by
      by_contra hcon
      simp only [not_exists, not_lt] at hcon
      obtain ⟨x, hxgrid, hxj⟩ := exists_grid_between hr s s'
      have hcs : ∀ j, |s j - x j| ≤ 2 * r := by
        intro j
        rw [abs_le]
        have hc := abs_le.mp (hcon j)
        have hm : max (s j) (s' j) ≤ s j + 3 * r :=
          max_le (by linarith) (by linarith [hc.1, hc.2])
        constructor <;> linarith [le_max_left (s j) (s' j), (hxj j).1, (hxj j).2]
      have hcs' : ∀ j, |s' j - x j| ≤ 2 * r := by
        intro j
        rw [abs_le]
        have hc := abs_le.mp (hcon j)
        have hm : max (s j) (s' j) ≤ s' j + 3 * r :=
          max_le (by linarith [hc.1, hc.2]) (by linarith)
        constructor <;> linarith [le_max_right (s j) (s' j), (hxj j).1, (hxj j).2]
      exact hss (h x hxgrid ⟨s, hcs, hsU⟩ ⟨hs', hcs'⟩ ⟨hsS, hcs⟩)
    obtain ⟨j, hj⟩ := hex
    have h1 : 3 * r < dist s' s := by
      rw [dist_comm]
      exact lt_of_lt_of_le hj (abs_sub_coord_le_dist s s' j)
    have h2 := dist_triangle s' y s
    linarith [dist_comm s y]

/-- Round `t` towards `t'` on the grid `r ℤ`: within `r` of `t`, and within `2r` of `t'` when
`|t - t'| < 2r`. -/
private lemma exists_round_toward {r : ℝ} (hr : 0 < r) (t t' : ℝ) (h : |t - t'| < 2 * r) :
    ∃ m : ℤ, |r * m - t| ≤ r ∧ |r * m - t'| < 2 * r := by
  rcases le_total t t' with htt | htt
  · refine ⟨⌈t / r⌉, ?_⟩
    have h1 := (mul_ceil_bounds (t := t) hr).1
    have h2 := (mul_ceil_bounds (t := t) hr).2
    have h3 := abs_lt.mp h
    constructor
    · rw [abs_le]; constructor <;> linarith
    · rw [abs_lt]; constructor <;> linarith
  · refine ⟨⌊t / r⌋, ?_⟩
    have h1 : r * ⌊t / r⌋ ≤ t := by
      calc r * (⌊t / r⌋ : ℝ) ≤ r * (t / r) := mul_le_mul_of_nonneg_left (Int.floor_le _) hr.le
        _ = t := mul_div_cancel₀ t hr.ne'
    have h2 : t - r < r * ⌊t / r⌋ := by
      have := Int.sub_one_lt_floor (t / r)
      calc t - r = r * (t / r - 1) := by rw [mul_sub, mul_div_cancel₀ t hr.ne', mul_one]
        _ < r * ⌊t / r⌋ := mul_lt_mul_of_pos_left this hr
    have h3 := abs_lt.mp h
    constructor
    · rw [abs_le]; constructor <;> linarith
    · rw [abs_lt]; constructor <;> linarith

/-- **Lemma 5.1(a)**, as in the corrected paper (`rw-spheres-corrected.tex`, Correction 15).  If
every cube `x + [-2r, 2r]^d` centred at a grid point `x ∈ r ℤ^d` whose cube `x + [-r, r]^d` meets
`U` contains at most one point of `S`, then `B_r(s) ⊆ 𝒞_s` for every `s ∈ S ∩ U`. -/
theorem geometric_constraint_inner_collar (U S : Set (EuclideanSpace ℝ (Fin d))) {r : ℝ}
    (hr : 0 < r)
    (h : ∀ x ∈ grid r, (cube x r ∩ U).Nonempty → (S ∩ cube x (2 * r)).Subsingleton) :
    ∀ s ∈ S ∩ U, closedBall s r ⊆ cell S s := by
  rintro s ⟨hsS, hsU⟩ y hy s' hs'
  rw [mem_closedBall] at hy
  by_cases hss : s' = s
  · subst hss
    exact le_rfl
  · have hfar : 2 * r ≤ dist s' s := by
      by_contra hlt
      rw [not_le] at hlt
      have hc : ∀ j, |s j - s' j| < 2 * r := fun j =>
        lt_of_le_of_lt (abs_sub_coord_le_dist s s' j) (by rwa [dist_comm])
      choose m hm using fun j => exists_round_toward hr (s j) (s' j) (hc j)
      let x : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (fun j => r * m j)
      have hxg : x ∈ grid r := fun j => ⟨m j, rfl⟩
      have hxs : ∀ j, |s j - x j| ≤ r := fun j => by
        rw [abs_sub_comm]; exact (hm j).1
      have hxs' : ∀ j, |s' j - x j| ≤ 2 * r := fun j => by
        rw [abs_sub_comm]; exact (hm j).2.le
      have hxs2 : ∀ j, |s j - x j| ≤ 2 * r := fun j => (hxs j).trans (by linarith)
      exact hss (h x hxg ⟨s, hxs, hsU⟩ ⟨hs', hxs'⟩ ⟨hsS, hxs2⟩)
    have h2 := dist_triangle s' y s
    linarith [dist_comm s y]

/-- Grid points have a positive gap above any radius: for `s` and `A` there is `η > 0` such that a
grid point within `A + η` of `s` is within `A`. -/
lemma exists_grid_gap {k : ℝ} (hk : 0 < k) (s : EuclideanSpace ℝ (Fin d)) (A : ℝ) :
    ∃ η > 0, ∀ y ∈ grid k, dist y s < A + η → dist y s ≤ A := by
  have hF := finite_grid_inter_closedBall (d := d) hk (‖s‖ + |A| + k)
  let T : Finset ℝ := insert k ((hF.toFinset.filter fun y => A < dist y s).image
    fun y => dist y s - A)
  have hT : T.Nonempty := Finset.insert_nonempty _ _
  refine ⟨T.min' hT, ?_, fun y hy hys => ?_⟩
  · show 0 < T.min' hT
    rw [Finset.lt_min'_iff]
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hk
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact sub_pos.mpr (Finset.mem_filter.mp hy).2
  · by_contra hA
    rw [not_le] at hA
    have hηk : T.min' hT ≤ k := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
    have hyF : y ∈ hF.toFinset := by
      rw [Set.Finite.mem_toFinset]
      refine ⟨hy, ?_⟩
      rw [mem_closedBall, dist_zero_right]
      have h1 : ‖y‖ ≤ ‖s‖ + dist y s := by
        rw [dist_eq_norm]
        calc ‖y‖ = ‖s + (y - s)‖ := by rw [add_sub_cancel]
          _ ≤ ‖s‖ + ‖y - s‖ := norm_add_le _ _
      linarith [le_abs_self A]
    have hmem : dist y s - A ∈ T :=
      Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hyF, hA⟩, rfl⟩)
    have := Finset.min'_le T _ hmem
    linarith

/-- **Lemma 5.1(b)**, as in the corrected paper (`rw-spheres-corrected.tex`): there are constants
`δ = δ(d) ∈ (0, 1)` and `R = R(d) ≥ 2` such that, for all `U`, `S` and `k > 0`, if every cube
`y + [-δk, δk]^d` centred at a grid point `y ∈ k ℤ^d` within distance `R k` of `U` contains a point
of `S`, then `𝒞_s ⊆ B_{4k√d}(s)` for every `s ∈ S ∩ U`.  Witnesses: `δ = 1/10` and
`R = max(2, 1.1√d)`; every point of `𝒞_s` is then within `(3/5) k √d` of `s`. -/
theorem geometric_constraint_outer (hd : 1 ≤ d) :
    ∃ δ R : ℝ, 0 < δ ∧ δ < 1 ∧ 2 ≤ R ∧
      ∀ (U S : Set (EuclideanSpace ℝ (Fin d))) (k : ℝ), 0 < k →
        (∀ y ∈ grid k ∩ cthickening (R * k) U, (S ∩ cube y (δ * k)).Nonempty) →
        ∀ s ∈ S ∩ U, cell S s ⊆ ball s (4 * k * Real.sqrt d) := by
  refine ⟨1 / 10, max 2 (11 / 10 * Real.sqrt d), by norm_num, by norm_num, le_max_left _ _, ?_⟩
  intro U S k hk h s hs z hz
  obtain ⟨hsS, hsU⟩ := hs
  have hsd : 1 ≤ Real.sqrt d := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    exact_mod_cast hd
  have hks : 0 < k * Real.sqrt d := mul_pos hk (by linarith)
  set a := 3 / 5 * k * Real.sqrt d with ha
  set A := 11 / 10 * Real.sqrt d * k with hA
  rw [mem_ball]
  suffices hcl : dist z s ≤ a by
    calc dist z s ≤ a := hcl
      _ = 3 / 5 * (k * Real.sqrt d) := by rw [ha]; ring
      _ < 4 * (k * Real.sqrt d) := mul_lt_mul_of_pos_right (by norm_num) hks
      _ = 4 * k * Real.sqrt d := by ring
  by_contra hlt
  rw [not_le] at hlt
  have ha0 : 0 ≤ a := by positivity
  -- Move a little past distance `a` along the segment to `z`, staying below the next grid radius.
  obtain ⟨η, hη, hgap⟩ := exists_grid_gap hk s A
  set L := dist z s with hL
  have hL0 : 0 < L := lt_of_le_of_lt ha0 hlt
  set e := min η (L - a) / 2 with he
  have he0 : 0 < e := by
    have : 0 < min η (L - a) := lt_min hη (by linarith)
    positivity
  have heη : e < η := by
    have := min_le_left η (L - a)
    linarith
  have heL : e < L - a := by
    have := min_le_right η (L - a)
    linarith
  set c := (a + e) / L with hc
  have hcL : c * L = a + e := div_mul_cancel₀ _ hL0.ne'
  have hc0 : 0 < c := div_pos (by linarith) hL0
  have hc1 : c ≤ 1 := by
    rw [div_le_one hL0]
    linarith
  set p : EuclideanSpace ℝ (Fin d) := s + c • (z - s) with hp
  have hps : dist p s = a + e := by
    rw [dist_eq_norm, hp, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc0,
      ← dist_eq_norm, ← hL, hcL]
  have hpz : dist p z = L - (a + e) := by
    have e1 : p - z = (c - 1) • (z - s) := by
      rw [hp, sub_smul, one_smul]
      abel
    rw [dist_eq_norm, e1, norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith),
      ← dist_eq_norm, ← hL]
    linear_combination -hcL
  -- The nearest grid point to `p` is tested, and its cube supplies a site closer to `z` than `s`.
  obtain ⟨g, hgG, hgp⟩ := exists_grid_near hk p
  have hgp_d : dist g p ≤ k / 2 * Real.sqrt d := dist_le_mul_sqrt g p (by positivity) hgp
  have hgs : dist g s ≤ A := by
    refine hgap g hgG ?_
    have t1 := dist_triangle g p s
    have : A = a + k / 2 * Real.sqrt d := by rw [hA, ha]; ring
    linarith
  have hAR : A ≤ max 2 (11 / 10 * Real.sqrt d) * k :=
    (le_of_eq (by ring)).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hk.le)
  obtain ⟨s'', hs''S, hs''c⟩ :=
    h g ⟨hgG, mem_cthickening_of_dist_le g s _ U hsU (hgs.trans hAR)⟩
  have hs''d : dist s'' g ≤ 1 / 10 * k * Real.sqrt d :=
    dist_le_mul_sqrt s'' g (by positivity) hs''c
  have hz' := hz s'' hs''S
  have t1 : dist s'' z ≤ dist s'' p + dist p z := dist_triangle _ _ _
  have t2 : dist s'' p ≤ dist s'' g + dist g p := dist_triangle _ _ _
  have : a = k / 2 * Real.sqrt d + 1 / 10 * k * Real.sqrt d := by rw [ha]; ring
  rw [dist_comm s z] at hz'
  linarith

end SpherePackings.Voronoi
