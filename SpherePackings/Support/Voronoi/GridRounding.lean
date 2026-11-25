import SpherePackings.Support.Voronoi.GeometricConstraint

/-!
# Lemma 5.1(b) with the published radius in dimensions at most twelve

The published Lemma 5.1(b) (`rw-spheres.tex:1635-1641`) tests the grid points of
`k ℤ^d ∩ B_{2k}(U)`.  The corrected paper (`rw-spheres-corrected.tex:1762`) states that this
radius suffices for `4 ≤ d ≤ 12` with a smaller `δ`, by a rounding argument that it does not
give, and that it fails for every `d ≥ 13`.  This file proves the published radius for every
`1 ≤ d ≤ 12`, with `δ = γ/(4√d)` and the directional margin `γ = 5/5184`.

* `exists_corner`: for a point `a` of the cube `[-1/2, 1/2]^d` and vectors `g`, `h`, some corner
  `b` of the cube has `g · b ≥ g · a` and `h · b ≥ h · a - |h_j|` for some `j`.  Among the
  maximizers of `g` on the slice `{b : h · b = h · a}` of the cube, one of largest norm has at
  most one coordinate in `(-1/2, 1/2)`; rounding that coordinate gives `b`.
* `exists_int_point_margin`: for `1 ≤ d ≤ 12`, every `s ∈ ℝ^d` and every unit vector `u`, some
  `y ∈ ℤ^d` has `|y - s| < 2` and `(y - s) · u ≥ |y - s|²/(8√d) + 5/5184`.  The point `y` is a
  corner of the unit lattice cube containing `s + u/9`, chosen by `exists_corner`.
* `geometric_constraint_outer_two`: Lemma 5.1(b) as printed, for `1 ≤ d ≤ 12`.
-/

open Metric

namespace SpherePackings.Voronoi

variable {d : ℕ}

/-! ### Rounding to a corner of the cube -/

lemma sum_mul_update (g b : Fin d → ℝ) (j : Fin d) (c : ℝ) :
    ∑ i, g i * Function.update b j c i = ∑ i, g i * b i + g j * (c - b j) := by
  classical
  have h1 := Finset.add_sum_erase Finset.univ (fun i => g i * Function.update b j c i)
    (Finset.mem_univ j)
  have h2 := Finset.add_sum_erase Finset.univ (fun i => g i * b i) (Finset.mem_univ j)
  have h3 : ∑ i ∈ Finset.univ.erase j, g i * Function.update b j c i =
      ∑ i ∈ Finset.univ.erase j, g i * b i :=
    Finset.sum_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  simp only [Function.update_self] at h1
  linarith

/-- A nonzero direction supported on two coordinates and orthogonal to `h`. -/
lemma exists_direction {i j : Fin d} (hij : i ≠ j) (h : Fin d → ℝ) :
    ∃ e : Fin d → ℝ, ∑ k, h k * e k = 0 ∧ 0 < ∑ k, e k ^ 2 ∧
      ∀ k, k ≠ i → k ≠ j → e k = 0 := by
  classical
  by_cases hh : h i = 0 ∧ h j = 0
  · refine ⟨fun k => if k = i then 1 else 0, ?_, ?_, fun k hk _ => by simp [hk]⟩
    · rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)]
      simp [hh.1]
    · rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)]
      simp
  · refine ⟨fun k => if k = i then h j else if k = j then -h i else 0, ?_, ?_,
      fun k hk hk' => by simp [hk, hk']⟩
    · rw [Fintype.sum_eq_add i j hij (fun k hk => by simp [hk.1, hk.2])]
      dsimp only
      rw [ite_eq_left (rfl : i = i), ite_eq_right (Ne.symm hij), ite_eq_left (rfl : j = j)]
      ring
    · rw [Fintype.sum_eq_add i j hij (fun k hk => by simp [hk.1, hk.2])]
      dsimp only
      rw [ite_eq_left (rfl : i = i), ite_eq_right (Ne.symm hij), ite_eq_left (rfl : j = j)]
      have hne : h i ≠ 0 ∨ h j ≠ 0 := by tauto
      rcases hne with h1 | h1
      · have := pow_pos (abs_pos.mpr h1) 2
        rw [sq_abs] at this
        nlinarith [sq_nonneg (h j)]
      · have := pow_pos (abs_pos.mpr h1) 2
        rw [sq_abs] at this
        nlinarith [sq_nonneg (h i)]

/-- **Rounding to a corner.**  For a point `a` of the cube `[-1/2, 1/2]^d` and vectors `g`,
`h`, some corner `b` of the cube has `g · b ≥ g · a` and `h · b ≥ h · a - |h_j|` for some
coordinate `j`. -/
lemma exists_corner (hd : 0 < d) (a g h : Fin d → ℝ) (ha : ∀ i, |a i| ≤ 1 / 2) :
    ∃ b : Fin d → ℝ, (∀ i, |b i| = 1 / 2) ∧ ∑ i, g i * a i ≤ ∑ i, g i * b i ∧
      ∃ j, ∑ i, h i * a i - |h j| ≤ ∑ i, h i * b i := by
  classical
  set C : Set (Fin d → ℝ) := {b | ∀ i, |b i| ≤ 1 / 2} with hC
  have hCc : IsCompact C := by
    have : C = Set.pi Set.univ fun _ => Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := by
      ext b
      simp only [hC, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc,
        abs_le]
    rw [this]
    exact isCompact_univ_pi fun _ => isCompact_Icc
  have hcg : Continuous fun b : Fin d → ℝ => ∑ i, g i * b i := by fun_prop
  have hch : Continuous fun b : Fin d → ℝ => ∑ i, h i * b i := by fun_prop
  have hcn : Continuous fun b : Fin d → ℝ => ∑ i, b i ^ 2 := by fun_prop
  set P : Set (Fin d → ℝ) := C ∩ {b | ∑ i, h i * b i = ∑ i, h i * a i} with hP
  have hPc : IsCompact P := hCc.inter_right (isClosed_eq hch continuous_const)
  have haP : a ∈ P := ⟨ha, rfl⟩
  obtain ⟨b₁, hb₁P, hb₁⟩ := hPc.exists_isMaxOn ⟨a, haP⟩ hcg.continuousOn
  set F : Set (Fin d → ℝ) := P ∩ {b | ∑ i, g i * b₁ i ≤ ∑ i, g i * b i} with hF
  have hFc : IsCompact F := hPc.inter_right (isClosed_le continuous_const hcg)
  obtain ⟨c, hcF, hc⟩ := hFc.exists_isMaxOn
    ⟨b₁, hb₁P, show ∑ i, g i * b₁ i ≤ ∑ i, g i * b₁ i from le_rfl⟩ hcn.continuousOn
  obtain ⟨⟨hcC, hch_eq⟩, hcg_ge⟩ := hcF
  have hcg_ge' : ∑ i, g i * b₁ i ≤ ∑ i, g i * c i := hcg_ge
  have hch_eq' : ∑ i, h i * c i = ∑ i, h i * a i := hch_eq
  have hga : ∑ i, g i * a i ≤ ∑ i, g i * c i := (isMaxOn_iff.mp hb₁ a haP).trans hcg_ge'
  -- A largest maximizer has at most one coordinate strictly inside `(-1/2, 1/2)`.
  have hone : ∀ i j, i ≠ j → |c i| < 1 / 2 → |c j| = 1 / 2 := by
    intro i j hij hi
    by_contra hj
    have hj' : |c j| < 1 / 2 := lt_of_le_of_ne (hcC j) hj
    obtain ⟨e, heh, hepos, hesupp⟩ := exists_direction hij h
    set D : ℝ := 1 + |e i| + |e j| with hD
    have hDpos : 0 < D := by positivity
    set μ : ℝ := min (1 / 2 - |c i|) (1 / 2 - |c j|) with hμ
    have hμpos : 0 < μ := lt_min (by linarith) (by linarith)
    set τ : ℝ := μ / D with hτ
    have hτpos : 0 < τ := div_pos hμpos hDpos
    have hτD : τ * D = μ := div_mul_cancel₀ μ hDpos.ne'
    have hτi : τ * |e i| ≤ 1 / 2 - |c i| := by
      have : τ * |e i| ≤ τ * D := mul_le_mul_of_nonneg_left (by rw [hD]; linarith [abs_nonneg (e j)])
        hτpos.le
      linarith [min_le_left (1 / 2 - |c i|) (1 / 2 - |c j|)]
    have hτj : τ * |e j| ≤ 1 / 2 - |c j| := by
      have : τ * |e j| ≤ τ * D := mul_le_mul_of_nonneg_left (by rw [hD]; linarith [abs_nonneg (e i)])
        hτpos.le
      linarith [min_le_right (1 / 2 - |c i|) (1 / 2 - |c j|)]
    have hstep : ∀ σ : ℝ, |σ| ≤ 1 → ∀ k, |c k + σ * τ * e k| ≤ 1 / 2 := by
      intro σ hσ k
      have hbound : ∀ m, τ * |e m| ≤ 1 / 2 - |c m| → |c m + σ * τ * e m| ≤ 1 / 2 := by
        intro m hm
        calc |c m + σ * τ * e m| ≤ |c m| + |σ * τ * e m| := abs_add_le _ _
          _ = |c m| + |σ| * (τ * |e m|) := by
              rw [abs_mul, abs_mul, abs_of_pos hτpos]
              ring
          _ ≤ |c m| + 1 * (τ * |e m|) := by
              gcongr
          _ ≤ 1 / 2 := by linarith
      by_cases hki : k = i
      · subst hki
        exact hbound k hτi
      · by_cases hkj : k = j
        · subst hkj
          exact hbound k hτj
        · rw [hesupp k hki hkj, mul_zero, add_zero]
          exact hcC k
    have hlin : ∀ (f : Fin d → ℝ) (σ : ℝ), ∑ k, f k * (c k + σ * τ * e k) =
        ∑ k, f k * c k + σ * τ * ∑ k, f k * e k := by
      intro f σ
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hmemP : ∀ σ : ℝ, |σ| ≤ 1 → (fun k => c k + σ * τ * e k) ∈ P := by
      intro σ hσ
      refine ⟨hstep σ hσ, ?_⟩
      show ∑ k, h k * (c k + σ * τ * e k) = _
      rw [hlin, heh, mul_zero, add_zero, hch_eq']
    have hcb : ∑ i, g i * c i ≤ ∑ i, g i * b₁ i := isMaxOn_iff.mp hb₁ c ⟨hcC, hch_eq⟩
    have hge : ∑ k, g k * e k = 0 := by
      have h1 := isMaxOn_iff.mp hb₁ _ (hmemP 1 (by norm_num))
      have h2 := isMaxOn_iff.mp hb₁ _ (hmemP (-1) (by norm_num))
      rw [hlin] at h1 h2
      have hp : τ * ∑ k, g k * e k ≤ 0 := by linarith
      have hn : 0 ≤ τ * ∑ k, g k * e k := by linarith
      have : τ * ∑ k, g k * e k = 0 := le_antisymm hp hn
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 hτpos.ne'
      · exact h0
    have hmemF : ∀ σ : ℝ, |σ| ≤ 1 → (fun k => c k + σ * τ * e k) ∈ F := by
      intro σ hσ
      refine ⟨hmemP σ hσ, ?_⟩
      show _ ≤ ∑ k, g k * (c k + σ * τ * e k)
      rw [hlin, hge, mul_zero, add_zero]
      exact hcg_ge'
    have hsq : ∀ σ : ℝ, ∑ k, (c k + σ * τ * e k) ^ 2 =
        ∑ k, c k ^ 2 + 2 * σ * τ * ∑ k, c k * e k + σ ^ 2 * τ ^ 2 * ∑ k, e k ^ 2 := by
      intro σ
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hp := isMaxOn_iff.mp hc _ (hmemF 1 (by norm_num))
    have hm := isMaxOn_iff.mp hc _ (hmemF (-1) (by norm_num))
    rw [hsq] at hp hm
    have hpos : 0 < τ ^ 2 * ∑ k, e k ^ 2 := mul_pos (pow_pos hτpos 2) hepos
    nlinarith
  by_cases hall : ∀ i, |c i| = 1 / 2
  · refine ⟨c, hall, hga, ⟨0, hd⟩, ?_⟩
    rw [hch_eq']
    linarith [abs_nonneg (h ⟨0, hd⟩)]
  · push Not at hall
    obtain ⟨j, hj⟩ := hall
    have hjlt : |c j| < 1 / 2 := lt_of_le_of_ne (hcC j) hj
    have hcj := abs_le.mp (hcC j)
    set v : ℝ := if 0 ≤ g j then 1 / 2 else -(1 / 2) with hv
    have hvb : |v - c j| ≤ 1 := by
      rw [hv]
      split_ifs <;> (rw [abs_le]; constructor <;> linarith)
    refine ⟨Function.update c j v, ?_, ?_, j, ?_⟩
    · intro i
      by_cases hij : i = j
      · subst hij
        rw [Function.update_self, hv]
        split_ifs <;> norm_num
      · rw [Function.update_of_ne hij]
        exact hone j i (Ne.symm hij) hjlt
    · rw [sum_mul_update]
      have : 0 ≤ g j * (v - c j) := by
        rw [hv]
        split_ifs with hg
        · exact mul_nonneg hg (by linarith)
        · push Not at hg
          exact mul_nonneg_of_nonpos_of_nonpos hg.le (by linarith)
      linarith
    · rw [sum_mul_update, hch_eq']
      have : -|h j| ≤ h j * (v - c j) := by
        calc -|h j| ≤ -(|h j| * |v - c j|) := by nlinarith [abs_nonneg (h j)]
          _ = -|h j * (v - c j)| := by rw [abs_mul]
          _ ≤ h j * (v - c j) := neg_abs_le _
      linarith

/-! ### A lattice point ahead of every point -/

lemma numeric_margin {q : ℝ} (hq1 : 1 ≤ q) (hq2 : q ≤ 7 / 2) :
    (q ^ 2 / 4 + 1 / 81) * (1 / (8 * q)) ≤ 1 / 9 - 5 / 5184 := by
  have hq : 0 < q := by linarith
  have h : q ^ 2 / 4 + 1 / 81 ≤ 571 / 648 * q := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq1) (sub_nonneg.mpr hq2)]
  rw [show (q ^ 2 / 4 + 1 / 81) * (1 / (8 * q)) = (q ^ 2 / 4 + 1 / 81) / (8 * q) by ring,
    div_le_iff₀ (by positivity)]
  linarith

/-- **The directional margin.**  For `1 ≤ d ≤ 12`, every `s ∈ ℝ^d` and every unit vector `u`,
some `y ∈ ℤ^d` has `|y - s| < 2` and `(y - s) · u ≥ |y - s|²/(8√d) + 5/5184`. -/
lemma exists_int_point_margin (hd : 1 ≤ d) (hd12 : d ≤ 12) (s u : Fin d → ℝ)
    (hu : ∑ i, u i ^ 2 = 1) :
    ∃ y : Fin d → ℤ, ∑ i, ((y i : ℝ) - s i) ^ 2 < 4 ∧
      (∑ i, ((y i : ℝ) - s i) ^ 2) / (8 * Real.sqrt d) + 5 / 5184 ≤
        ∑ i, ((y i : ℝ) - s i) * u i := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd12' : (d : ℝ) ≤ 12 := by exact_mod_cast hd12
  obtain ⟨q, hq⟩ : ∃ q, q = Real.sqrt d := ⟨_, rfl⟩
  have hq1 : 1 ≤ q := by
    rw [hq, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hd'
  have hq2 : q ≤ 7 / 2 := by
    rw [hq, show (7 / 2 : ℝ) = Real.sqrt ((7 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hqsq : q ^ 2 = d := by rw [hq]; exact Real.sq_sqrt (by positivity)
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = 1 / (8 * q) := ⟨_, rfl⟩
  have hq0 : 0 < q := by linarith
  have hwpos : 0 < w := by
    rw [hw]
    positivity
  obtain ⟨x, hx⟩ : ∃ x : Fin d → ℝ, ∀ i, x i = s i + 1 / 9 * u i := ⟨_, fun i => rfl⟩
  obtain ⟨a, hadef⟩ : ∃ a : Fin d → ℝ, ∀ i, a i = x i - (⌊x i⌋ + 1 / 2) := ⟨_, fun i => rfl⟩
  have ha : ∀ i, |a i| ≤ 1 / 2 := fun i => by
    have h1 := Int.floor_le (x i)
    have h2 := Int.lt_floor_add_one (x i)
    rw [abs_le, hadef]
    constructor <;> linarith
  obtain ⟨h, hh⟩ : ∃ h : Fin d → ℝ, ∀ i, h i = a i - 1 / 9 * u i := ⟨_, fun i => rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : Fin d → ℝ, ∀ i, g i = u i + 2 * w * h i := ⟨_, fun i => rfl⟩
  obtain ⟨b, hb, hgb, j, hhb⟩ := exists_corner (by omega) a g h ha
  obtain ⟨y, hy⟩ : ∃ y : Fin d → ℤ, ∀ i, y i = ⌊x i⌋ + if b i = 1 / 2 then 1 else 0 :=
    ⟨_, fun i => rfl⟩
  have hb2 : ∀ i, b i ^ 2 = 1 / 4 := fun i => by
    rw [← sq_abs, hb i]
    norm_num
  have hE : ∀ i, (y i : ℝ) - s i = b i - h i := by
    intro i
    rw [hy i, hh i, hadef i, hx i]
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2)).mp (hb i) with h1 | h1
    · rw [ite_eq_left h1]
      push_cast
      rw [h1]
      ring
    · rw [ite_eq_right (by rw [h1]; norm_num)]
      push_cast
      rw [h1]
      ring
  refine ⟨y, ?_⟩
  have e1 : ∑ i, ((y i : ℝ) - s i) ^ 2 = ∑ i, (b i - h i) ^ 2 :=
    Finset.sum_congr rfl fun i _ => by rw [hE i]
  have e2 : ∑ i, ((y i : ℝ) - s i) * u i = ∑ i, (b i - h i) * u i :=
    Finset.sum_congr rfl fun i _ => by rw [hE i]
  rw [e1, e2, ← hq]
  -- The scalar sums.
  have eb2 : ∑ i, b i ^ 2 = d / 4 := by
    simp only [hb2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have eN : ∑ i, (b i - h i) ^ 2 = d / 4 - 2 * ∑ i, h i * b i + ∑ i, h i ^ 2 := by
    rw [← eb2, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have eD : ∑ i, (b i - h i) * u i = ∑ i, b i * u i - ∑ i, h i * u i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have eHU : ∑ i, h i * u i = ∑ i, a i * u i - 1 / 9 := by
    have : ∑ i, h i * u i = ∑ i, a i * u i - 1 / 9 * ∑ i, u i ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [hh i]; ring
    rw [this, hu, mul_one]
  have eH2 : ∑ i, h i ^ 2 = ∑ i, a i ^ 2 - 2 / 9 * ∑ i, a i * u i + 1 / 81 := by
    have : ∑ i, h i ^ 2 =
        ∑ i, a i ^ 2 - 2 / 9 * ∑ i, a i * u i + 1 / 81 * ∑ i, u i ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [hh i]; ring
    rw [this, hu, mul_one]
  have eHA : ∑ i, h i * a i = ∑ i, a i ^ 2 - 1 / 9 * ∑ i, a i * u i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [hh i]; ring
  have eGB : ∑ i, g i * b i = ∑ i, b i * u i + 2 * w * ∑ i, h i * b i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [hg i]; ring
  have eGA : ∑ i, g i * a i = ∑ i, a i * u i + 2 * w * ∑ i, h i * a i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [hg i]; ring
  have hA7 : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (a i)
  have haj : |a j| ^ 2 ≤ ∑ i, a i ^ 2 := by
    rw [sq_abs]
    exact Finset.single_le_sum (f := fun i => a i ^ 2) (fun i _ => sq_nonneg (a i))
      (Finset.mem_univ j)
  have huj : u j ^ 2 ≤ 1 := by
    rw [← hu]
    exact Finset.single_le_sum (f := fun i => u i ^ 2) (fun i _ => sq_nonneg (u i))
      (Finset.mem_univ j)
  have hujabs : |u j| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (u j)]
  have hhj : |h j| ≤ |a j| + 1 / 9 := by
    rw [hh j]
    calc |a j - 1 / 9 * u j| ≤ |a j| + |1 / 9 * u j| := abs_sub _ _
      _ ≤ |a j| + 1 / 9 := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 9)]
          linarith
  have hajabs : |a j| ≤ 1 / 2 := ha j
  have hquad : 0 ≤ 3 / 4 - 2 * |a j| + |a j| ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hajabs) (by linarith : (0 : ℝ) ≤ 3 / 2 - |a j|)]
  rw [eN, eD, eHU, eH2]
  rw [eGB, eGA, eHA] at hgb
  rw [eHA] at hhb
  constructor
  · linarith
  · have hnum := numeric_margin hq1 hq2
    rw [← hw, hqsq] at hnum
    have hwA : 0 ≤ w * ∑ i, a i ^ 2 := mul_nonneg hwpos.le hA7
    rw [div_eq_mul_one_div _ (8 * q), ← hw]
    nlinarith

/-! ### Lemma 5.1(b) with the published radius -/

lemma dist_sq_eq_sum (x y : EuclideanSpace ℝ (Fin d)) :
    dist x y ^ 2 = ∑ i, (x i - y i) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  exact Finset.sum_congr rfl fun i _ => by rw [Real.dist_eq, sq_abs]

/-- The final comparison of `lemma51b_radius_two`, in scalar form. -/
lemma radius_two_scalar {k L q Nv W1 W2 : ℝ} (hk : 0 < k) (hq1 : 1 ≤ q)
    (hL : 4 * k * q ≤ L) (hNv : 0 ≤ Nv)
    (hW1 : Nv / (8 * q) + 3 * (5 / 5184) / 4 ≤ W1)
    (hW2 : W2 ≤ Nv + 5 / 5184 + (5 / 5184) ^ 2 / 16) :
    k ^ 2 * W2 - 2 * k * L * W1 < 0 := by
  have hq : 0 < q := by linarith
  have hW1nn : 0 ≤ W1 := le_trans (by positivity) hW1
  have h1 : 2 * k * (4 * k * q) * W1 ≤ 2 * k * L * W1 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL (by positivity)) hW1nn
  have h2 : 2 * k * (4 * k * q) * (Nv / (8 * q) + 3 * (5 / 5184) / 4) ≤
      2 * k * (4 * k * q) * W1 := mul_le_mul_of_nonneg_left hW1 (by positivity)
  have h3 : 2 * k * (4 * k * q) * (Nv / (8 * q) + 3 * (5 / 5184) / 4) =
      k ^ 2 * Nv + k ^ 2 * (q * (30 / 5184)) := by
    field_simp
    ring
  have h4 : k ^ 2 * W2 ≤ k ^ 2 * (Nv + 5 / 5184 + (5 / 5184) ^ 2 / 16) :=
    mul_le_mul_of_nonneg_left hW2 (by positivity)
  have h5 : k ^ 2 * (5 / 5184 + (5 / 5184) ^ 2 / 16) < k ^ 2 * (q * (30 / 5184)) := by
    apply mul_lt_mul_of_pos_left _ (by positivity)
    nlinarith
  nlinarith

/-- **Lemma 5.1(b) as printed, for `1 ≤ d ≤ 12`** (`rw-spheres.tex:1635-1641`; the corrected
paper, `rw-spheres-corrected.tex:1762`, states it for `4 ≤ d ≤ 12` without proof).  With
`δ = γ/(4√d)` and `γ = 5/5184`: for all `U`, `S` and `k > 0`, if every cube `y + [-δk, δk]^d`
centred at a grid point `y ∈ k ℤ^d` within distance `2k` of `U` contains a point of `S`, then
`𝒞_s ⊆ B_{4k√d}(s)` for every `s ∈ S ∩ U`.  The radius `2k` fails for every `d ≥ 13`. -/
theorem geometric_constraint_outer_two (hd : 1 ≤ d) (hd12 : d ≤ 12) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ (U S : Set (EuclideanSpace ℝ (Fin d))) (k : ℝ), 0 < k →
        (∀ y ∈ grid k ∩ cthickening (2 * k) U, (S ∩ cube y (δ * k)).Nonempty) →
        ∀ s ∈ S ∩ U, cell S s ⊆ ball s (4 * k * Real.sqrt d) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨q, hq⟩ : ∃ q, q = Real.sqrt d := ⟨_, rfl⟩
  have hq1 : 1 ≤ q := by
    rw [hq, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hd'
  have hqpos : 0 < q := by linarith
  have hqsq : q ^ 2 = d := by rw [hq]; exact Real.sq_sqrt (by positivity)
  refine ⟨5 / 5184 / (4 * q), by positivity, ?_, ?_⟩
  · rw [div_lt_one (by positivity)]
    linarith
  intro U S k hk h s hs z hz
  obtain ⟨hsS, hsU⟩ := hs
  rw [mem_ball, ← hq]
  by_contra hge
  push Not at hge
  obtain ⟨L, hL⟩ : ∃ L, L = dist z s := ⟨_, rfl⟩
  rw [← hL] at hge
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity) hge
  obtain ⟨u, hu⟩ : ∃ u : Fin d → ℝ, ∀ i, u i = (z i - s i) / L := ⟨_, fun i => rfl⟩
  have hL2 : L ^ 2 = ∑ i, (z i - s i) ^ 2 := by rw [hL]; exact dist_sq_eq_sum z s
  have hu1 : ∑ i, u i ^ 2 = 1 := by
    simp only [hu, div_pow]
    rw [← Finset.sum_div, ← hL2, div_self (by positivity)]
  obtain ⟨y, hy4, hym⟩ := exists_int_point_margin hd hd12 (fun i => s i / k) u hu1
  rw [← hq] at hym
  obtain ⟨Y, hY⟩ : ∃ Y : EuclideanSpace ℝ (Fin d), Y = WithLp.toLp 2 (fun i => k * y i) :=
    ⟨_, rfl⟩
  have hYi : ∀ i, Y i = k * y i := fun i => by rw [hY]
  have hYgrid : Y ∈ grid k := fun i => ⟨y i, hYi i⟩
  obtain ⟨v, hv⟩ : ∃ v : Fin d → ℝ, ∀ i, v i = (y i : ℝ) - s i / k := ⟨_, fun i => rfl⟩
  have hvsum : ∀ (F : ℝ → ℝ), ∑ i, F ((y i : ℝ) - s i / k) = ∑ i, F (v i) :=
    fun F => Finset.sum_congr rfl fun i _ => by rw [hv i]
  have hNv4 : ∑ i, v i ^ 2 < 4 := by
    have := hvsum (fun r => r ^ 2)
    simp only at this
    linarith
  have hmargin : (∑ i, v i ^ 2) / (8 * q) + 5 / 5184 ≤ ∑ i, v i * u i := by
    have e1 := hvsum (fun r => r ^ 2)
    have e2 : ∑ i, ((y i : ℝ) - s i / k) * u i = ∑ i, v i * u i :=
      Finset.sum_congr rfl fun i _ => by rw [hv i]
    simp only at e1
    rw [← e1, ← e2]
    exact hym
  have hYs2 : dist Y s ^ 2 = k ^ 2 * ∑ i, v i ^ 2 := by
    rw [dist_sq_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hYi, hv]
    field_simp
  have hYs : dist Y s ≤ 2 * k := by
    have h1 : dist Y s ^ 2 ≤ (2 * k) ^ 2 := by
      rw [hYs2]
      nlinarith [sq_nonneg k]
    exact (pow_le_pow_iff_left₀ dist_nonneg (by positivity) (by norm_num)).mp h1
  obtain ⟨s', hs'S, hs'c⟩ := h Y ⟨hYgrid, mem_cthickening_of_dist_le Y s _ U hsU hYs⟩
  have hcontra : dist s z ≤ dist s' z := hz s' hs'S
  obtain ⟨ε, hε⟩ : ∃ ε : Fin d → ℝ, ∀ i, ε i = (s' i - Y i) / k := ⟨_, fun i => rfl⟩
  have hεb : ∀ i, |ε i| ≤ 5 / 5184 / (4 * q) := by
    intro i
    rw [hε, abs_div, abs_of_pos hk, div_le_iff₀ hk]
    exact hs'c i
  have hcoord : ∀ i, s' i - z i = k * (v i + ε i) - L * u i := by
    intro i
    rw [hv, hε, hu, hYi]
    field_simp
    ring
  have hNeb : ∑ i, ε i ^ 2 ≤ (5 / 5184) ^ 2 / 16 := by
    have h1 : ∑ i, ε i ^ 2 ≤ ∑ _i : Fin d, (5 / 5184 / (4 * q)) ^ 2 :=
      Finset.sum_le_sum fun i _ => by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hεb i) 2
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    have h2 : (d : ℝ) * (5 / 5184 / (4 * q)) ^ 2 = (5 / 5184) ^ 2 / 16 := by
      rw [← hqsq]
      field_simp
      ring
    linarith
  have hNv0 : 0 ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hNe0 : 0 ≤ ∑ i, ε i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hcs1 : -(5 / 5184 / 4) ≤ ∑ i, ε i * u i := by
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ ε u
    rw [hu1, mul_one] at h1
    have h2 : (∑ i, ε i * u i) ^ 2 ≤ (5 / 5184 / 4) ^ 2 := by
      calc (∑ i, ε i * u i) ^ 2 ≤ ∑ i, ε i ^ 2 := h1
        _ ≤ (5 / 5184) ^ 2 / 16 := hNeb
        _ = (5 / 5184 / 4) ^ 2 := by norm_num
    exact (abs_le_of_sq_le_sq' h2 (by norm_num)).1
  have hcs2 : ∑ i, v i * ε i ≤ 5 / 5184 / 2 := by
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v ε
    have h2 : (∑ i, v i * ε i) ^ 2 ≤ (5 / 5184 / 2) ^ 2 := by
      calc (∑ i, v i * ε i) ^ 2 ≤ (∑ i, v i ^ 2) * ∑ i, ε i ^ 2 := h1
        _ ≤ 4 * ((5 / 5184) ^ 2 / 16) := mul_le_mul hNv4.le hNeb hNe0 (by norm_num)
        _ = (5 / 5184 / 2) ^ 2 := by norm_num
    exact (abs_le_of_sq_le_sq' h2 (by norm_num)).2
  have hW1 : ∑ i, (v i + ε i) * u i = ∑ i, v i * u i + ∑ i, ε i * u i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hW2 : ∑ i, (v i + ε i) ^ 2 = ∑ i, v i ^ 2 + 2 * ∑ i, v i * ε i + ∑ i, ε i ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hS : ∑ i, (s' i - z i) ^ 2 =
      k ^ 2 * ∑ i, (v i + ε i) ^ 2 - 2 * k * L * ∑ i, (v i + ε i) * u i +
        L ^ 2 * ∑ i, u i ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [hcoord i]; ring
  have hz2 : ∑ i, (s i - z i) ^ 2 = L ^ 2 := by
    rw [hL2]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hkey := radius_two_scalar (W1 := ∑ i, (v i + ε i) * u i)
    (W2 := ∑ i, (v i + ε i) ^ 2) hk hq1 hge hNv0 (by rw [hW1]; linarith) (by rw [hW2]; linarith)
  have hlt : ∑ i, (s' i - z i) ^ 2 < ∑ i, (s i - z i) ^ 2 := by
    rw [hS, hz2, hu1, mul_one]
    linarith
  have hd1 : dist s' z ^ 2 < dist s z ^ 2 := by
    rw [dist_sq_eq_sum, dist_sq_eq_sum]
    exact hlt
  have := (pow_lt_pow_iff_left₀ dist_nonneg dist_nonneg (by norm_num : (2 : ℕ) ≠ 0)).mp hd1
  linarith

end SpherePackings.Voronoi
