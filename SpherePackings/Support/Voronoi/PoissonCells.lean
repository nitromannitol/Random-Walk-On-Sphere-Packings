module

public import SpherePackings.Support.Voronoi.CountsToCells
public import SpherePackings.Support.Voronoi.GridCount
public import SpherePackings.Support.Poisson.Tails
public import SpherePackings.Support.MeasureOverlap
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

@[expose] public section

/-!
# Proposition 1.1: Voronoi cells of Poisson point processes

`rw-spheres.tex:360-381` (statement) and `rw-spheres.tex:1690-1764` (proof).  For a measure `μ`
satisfying the mass bounds (1.4) and Poisson point processes `Λ_m` of intensity `m μ`, almost surely,
for all large `m`, every Voronoi cell meeting `U` contains the ball of radius `m^{-8/β⁻}` around its
point and lies in the ball of radius `m^{-1/(3β⁺)}`.

Correction: the printed proposition asks for (1.4) only at points of `U`.  That is not enough
(for `μ` the Lebesgue measure on `U` the points of `Λ_m` lie in `U` and the cells of the extreme
points are unbounded), and the printed proof uses (1.4) at points outside `U`.  Here (1.4) is
required on an open neighbourhood `W` of `closure U`.

The union bound for cubes containing two or more points uses `∑ λ_x² ≤ (max λ_x) ∑ λ_x` and the
bounded overlap of the cubes in place of the printed partition by mass levels.
-/

open MeasureTheory Metric Filter Set
open scoped ENNReal NNReal Topology

namespace SpherePackings

open Voronoi

variable {d : ℕ}


/-- Display (1.4), on a set `W`: for all small radii `r`, `r^{β⁺} ≤ μ(B_r(z)) ≤ r^{β⁻}` for every
`z ∈ W`. -/
def HolderMassBounds (μ : Measure (EuclideanSpace ℝ (Fin d))) (W : Set (EuclideanSpace ℝ (Fin d))) (βp βm : ℝ) : Prop :=
  ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → ∀ z ∈ W,
    ENNReal.ofReal (r ^ βp) ≤ μ (ball z r) ∧ μ (ball z r) ≤ ENNReal.ofReal (r ^ βm)

lemma isClosed_cube (x : (EuclideanSpace ℝ (Fin d))) (a : ℝ) : IsClosed (cube x a) := by
  have : cube x a = ⋂ j, {y : EuclideanSpace ℝ (Fin d) | |y j - x j| ≤ a} := by ext; simp [cube]
  rw [this]
  exact isClosed_iInter fun j => isClosed_le (by fun_prop) continuous_const

lemma measurableSet_cube (x : (EuclideanSpace ℝ (Fin d))) (a : ℝ) : MeasurableSet (cube x a) :=
  (isClosed_cube x a).measurableSet

lemma ball_subset_cube (x : (EuclideanSpace ℝ (Fin d))) (a : ℝ) : ball x a ⊆ cube x a := fun y hy j =>
  (abs_sub_coord_le_dist y x j).trans (mem_ball.mp hy).le

lemma cube_subset_closedBall (x : (EuclideanSpace ℝ (Fin d))) {a : ℝ} (ha : 0 ≤ a) :
    cube x a ⊆ closedBall x (a * Real.sqrt d) := fun y hy =>
  mem_closedBall.mpr (dist_le_mul_sqrt y x ha hy)

/-- The upper mass bound makes `μ` finite on compact subsets of `W`. -/
lemma HolderMassBounds.measure_lt_top {μ : Measure (EuclideanSpace ℝ (Fin d))} {W : Set (EuclideanSpace ℝ (Fin d))} {βp βm : ℝ}
    (hμ : HolderMassBounds μ W βp βm) {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) (hKW : K ⊆ W) :
    μ K < ∞ := by
  obtain ⟨r₀, hr₀, hb⟩ := hμ
  refine hK.measure_lt_top_of_nhdsWithin fun x hx => ?_
  refine ⟨ball x (r₀ / 2), mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (by positivity)), ?_⟩
  exact ((hb (r₀ / 2) (by positivity) (by linarith) x (hKW hx)).2).trans_lt ENNReal.ofReal_lt_top

/-- Cubes are bounded. -/
lemma isBounded_cube (y : EuclideanSpace ℝ (Fin d)) (a : ℝ) : Bornology.IsBounded (cube y a) :=
  (isBounded_closedBall (x := y) (r := |a| * Real.sqrt d)).subset fun z hz =>
    dist_le_mul_sqrt z y (abs_nonneg a) fun j => (hz j).trans (le_abs_self a)

namespace IsPoissonPointProcess

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Λ : Ω → Set (EuclideanSpace ℝ (Fin d))} {ν : Measure (EuclideanSpace ℝ (Fin d))}

lemma measure_empty_eq (h : IsPoissonPointProcess P Λ ν) {B : Set (EuclideanSpace ℝ (Fin d))} (hB : MeasurableSet B)
    (hBb : Bornology.IsBounded B) (hνB : ν B ≠ ∞) :
    P {ω | Λ ω ∩ B = ∅} = ENNReal.ofReal (Real.exp (-(ν B).toReal)) := by
  rw [← h.measureReal_empty hB hBb hνB, ofReal_measureReal]

lemma measure_not_subsingleton_le (h : IsPoissonPointProcess P Λ ν) {B : Set (EuclideanSpace ℝ (Fin d))}
    (hB : MeasurableSet B) (hBb : Bornology.IsBounded B) (hνB : ν B ≠ ∞) :
    P {ω | ¬ (Λ ω ∩ B).Subsingleton} ≤ ENNReal.ofReal ((ν B).toReal ^ 2) := by
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal (h.measureReal_not_subsingleton_le hB hBb hνB)

/-- Union bound for empty cubes. -/
lemma measure_exists_empty_le (h : IsPoissonPointProcess P Λ ν) (Y : Finset (EuclideanSpace ℝ (Fin d))) (a c : ℝ)
    (hfin : ∀ y ∈ Y, ν (cube y a) ≠ ∞) (hc : ∀ y ∈ Y, c ≤ (ν (cube y a)).toReal) :
    P {ω | ∃ y ∈ Y, Λ ω ∩ cube y a = ∅} ≤ ENNReal.ofReal (Y.card * Real.exp (-c)) := by
  have hset : {ω | ∃ y ∈ Y, Λ ω ∩ cube y a = ∅} = ⋃ y ∈ Y, {ω | Λ ω ∩ cube y a = ∅} := by
    ext; simp
  rw [hset]
  refine (measure_biUnion_finset_le Y _).trans ?_
  calc ∑ y ∈ Y, P {ω | Λ ω ∩ cube y a = ∅}
      ≤ ∑ _y ∈ Y, ENNReal.ofReal (Real.exp (-c)) := by
        refine Finset.sum_le_sum fun y hy => ?_
        rw [h.measure_empty_eq (measurableSet_cube y a) (isBounded_cube y a) (hfin y hy)]
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg (hc y hy)))
    _ = ENNReal.ofReal (Y.card * Real.exp (-c)) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]

/-- Union bound for cubes with two or more points: `∑ λ_x² ≤ (max λ_x) ∑ λ_x`. -/
lemma measure_exists_double_le (h : IsPoissonPointProcess P Λ ν) (X : Finset (EuclideanSpace ℝ (Fin d))) (a M : ℝ)
    (hfin : ∀ x ∈ X, ν (cube x a) ≠ ∞) (hM : ∀ x ∈ X, (ν (cube x a)).toReal ≤ M) :
    P {ω | ∃ x ∈ X, ¬ (Λ ω ∩ cube x a).Subsingleton} ≤
      ENNReal.ofReal (M * ∑ x ∈ X, (ν (cube x a)).toReal) := by
  have hset : {ω | ∃ x ∈ X, ¬ (Λ ω ∩ cube x a).Subsingleton} =
      ⋃ x ∈ X, {ω | ¬ (Λ ω ∩ cube x a).Subsingleton} := by
    ext; simp
  rw [hset]
  refine (measure_biUnion_finset_le X _).trans ?_
  calc ∑ x ∈ X, P {ω | ¬ (Λ ω ∩ cube x a).Subsingleton}
      ≤ ∑ x ∈ X, ENNReal.ofReal (M * (ν (cube x a)).toReal) := by
        refine Finset.sum_le_sum fun x hx => ?_
        refine (h.measure_not_subsingleton_le (measurableSet_cube x a) (isBounded_cube x a)
          (hfin x hx)).trans ?_
        apply ENNReal.ofReal_le_ofReal
        rw [sq]
        exact mul_le_mul_of_nonneg_right (hM x hx) ENNReal.toReal_nonneg
    _ = ENNReal.ofReal (M * ∑ x ∈ X, (ν (cube x a)).toReal) := by
        rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg]
        intro x hx
        exact mul_nonneg ((ENNReal.toReal_nonneg).trans (hM x hx)) ENNReal.toReal_nonneg

end IsPoissonPointProcess

/-- Real-power arithmetic for the empty-cube estimate: `m (δ m^{-1/(2β)})^β = δ^β m^{1/2}`. -/
lemma mul_rpow_scale {m δ β : ℝ} (hm : 0 < m) (hδ : 0 ≤ δ) (hβ : 0 < β) :
    m * (δ * m ^ (-1 / (2 * β))) ^ β = δ ^ β * m ^ (1 / 2 : ℝ) := by
  rw [Real.mul_rpow hδ (Real.rpow_nonneg hm.le _), ← Real.rpow_mul hm.le]
  have h1 : -1 / (2 * β) * β = -(1 / 2 : ℝ) := by field_simp
  rw [h1, mul_left_comm, ← Real.rpow_one_add' hm.le (by norm_num)]
  norm_num

/-- Real-power arithmetic for the double-point estimate: `m (c m^{-8/β})^β = c^β m^{-7}`. -/
lemma mul_rpow_scale' {m c β : ℝ} (hm : 0 < m) (hc : 0 ≤ c) (hβ : 0 < β) :
    m * (c * m ^ (-8 / β)) ^ β = c ^ β * m ^ (-7 : ℝ) := by
  rw [Real.mul_rpow hc (Real.rpow_nonneg hm.le _), ← Real.rpow_mul hm.le]
  have h1 : -8 / β * β = (-8 : ℝ) := by field_simp
  rw [h1, mul_left_comm, ← Real.rpow_one_add' hm.le (by norm_num)]
  norm_num

lemma tendsto_natCast_rpow_neg {a : ℝ} (ha : 0 < a) :
    Tendsto (fun m : ℕ => (m : ℝ) ^ (-a)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop ha).comp tendsto_natCast_atTop_atTop

/-- Proposition 1.1, first part, together with the density of the points: every point of `U` is
within `m^{-1/(3β⁺)}` of a point of `Λ_m`. -/
theorem voronoi_cells_between_balls_aux (hd : 1 ≤ d) {U : Set (EuclideanSpace ℝ (Fin d))} (hUb : Bornology.IsBounded U)
    {μ : Measure (EuclideanSpace ℝ (Fin d))} {βp βm : ℝ} (hβp : 0 < βp) (hβm : 0 < βm) {W : Set (EuclideanSpace ℝ (Fin d))}
    (hW : IsOpen W) (hUW : closure U ⊆ W) (hμ : HolderMassBounds μ W βp βm)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Λ : ℕ → Ω → Set (EuclideanSpace ℝ (Fin d))) (hΛ : ∀ m : ℕ, IsPoissonPointProcess P (Λ m) ((m : ℝ≥0∞) • μ)) :
    ∀ᵐ ω ∂P, ∀ᶠ m in atTop, (∀ s ∈ Λ m ω, (cell (Λ m ω) s ∩ U).Nonempty →
      ball s ((m : ℝ) ^ (-8 / βm)) ⊆ cell (Λ m ω) s ∧
        cell (Λ m ω) s ⊆ ball s ((m : ℝ) ^ (-1 / (3 * βp)))) ∧
      ∀ y ∈ U, ∃ s ∈ Λ m ω, dist s y < (m : ℝ) ^ (-1 / (3 * βp)) := by
  obtain ⟨r₀, hr₀, hbd⟩ := hμ
  obtain ⟨ρ₀, hρ₀, hρ₀W⟩ := hUb.isCompact_closure.exists_cthickening_subset_open hW hUW
  set ρ := ρ₀ / 2 with hρdef
  have hρ : 0 < ρ := half_pos hρ₀
  -- The compact neighbourhood carrying all cubes.
  set K := cthickening ρ₀ U with hKdef
  have hKW : K ⊆ W := by rw [hKdef, ← cthickening_closure]; exact hρ₀W
  have hKc : IsCompact K :=
    isCompact_of_isClosed_isBounded isClosed_cthickening hUb.cthickening
  have hμK : μ K < ∞ := HolderMassBounds.measure_lt_top ⟨r₀, hr₀, hbd⟩ hKc hKW
  obtain ⟨R₁, hR₁⟩ := (hUb.cthickening (δ := ρ)).subset_closedBall 0
  set R := max R₁ 1 with hRdef
  have hR : 0 ≤ R := le_max_of_le_right zero_le_one
  have hregion : cthickening ρ U ⊆ closedBall 0 R :=
    hR₁.trans (closedBall_subset_closedBall (le_max_left _ _))
  -- A closed ball of radius at most `ρ` around a point of `cthickening ρ U` lies in `K`.
  have hballK : ∀ {y : (EuclideanSpace ℝ (Fin d))} {t : ℝ}, y ∈ cthickening ρ U → 0 ≤ t → t ≤ ρ → closedBall y t ⊆ K := by
    intro y t hy ht htρ z hz
    have h1 : z ∈ cthickening t (cthickening ρ U) :=
      mem_cthickening_of_dist_le z y t _ hy (mem_closedBall.mp hz)
    have h2 := cthickening_cthickening_subset ht hρ.le U h1
    exact cthickening_mono (by rw [hρdef]; linarith) U h2
  obtain ⟨δ, Rg, hδ0, -, hRg, hδ5⟩ := geometric_constraint_outer hd
  set δ' := min δ (1 / 4) with hδ'def
  have hδ' : 0 < δ' := lt_min hδ0 (by norm_num)
  set sd := Real.sqrt d with hsddef
  have hsd : 0 < sd := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  -- The two scales.
  set k : ℕ → ℝ := fun m => (m : ℝ) ^ (-1 / (2 * βp)) with hkdef
  set r : ℕ → ℝ := fun m => (m : ℝ) ^ (-8 / βm) with hrdef
  have hk0 : Tendsto k atTop (𝓝 0) := by
    have := tendsto_natCast_rpow_neg (a := 1 / (2 * βp)) (by positivity)
    simpa only [hkdef, neg_div] using this
  have hr0 : Tendsto r atTop (𝓝 0) := by
    have := tendsto_natCast_rpow_neg (a := 8 / βm) (by positivity)
    simpa only [hrdef, neg_div] using this
  have hq0 : Tendsto (fun m : ℕ => (m : ℝ) ^ (-1 / (6 * βp))) atTop (𝓝 0) := by
    have := tendsto_natCast_rpow_neg (a := 1 / (6 * βp)) (by positivity)
    simpa only [neg_div] using this
  have ev : ∀ {f : ℕ → ℝ}, Tendsto f atTop (𝓝 0) → ∀ {c ε : ℝ}, 0 < ε →
      ∀ᶠ m in atTop, c * f m < ε := by
    intro f hf c ε hε
    have := hf.const_mul c
    rw [mul_zero] at this
    exact this.eventually (gt_mem_nhds hε)
  have hscale : ∀ᶠ m : ℕ in atTop, 1 ≤ m ∧ k m ≤ 1 ∧ δ' * k m < r₀ ∧ (Rg + 3 * sd) * k m ≤ ρ ∧
      2 * r m * sd + k m * sd ≤ ρ ∧ 3 * sd * r m < r₀ ∧ 2 * r m * sd ≤ ρ ∧
      δ' * k m * sd ≤ ρ ∧ 4 * k m * sd ≤ (m : ℝ) ^ (-1 / (3 * βp)) := by
    filter_upwards [eventually_ge_atTop 1, ev hk0 (c := 1) (ε := 2) two_pos,
      ev hk0 (c := δ') hr₀, ev hk0 (c := Rg + 3 * sd) hρ, ev hr0 (c := 2 * sd) (half_pos hρ),
      ev hk0 (c := sd) (half_pos hρ), ev hr0 (c := 3 * sd) hr₀,
      ev hk0 (c := δ' * sd) hρ, ev hq0 (c := 4 * sd) one_pos, ev hk0 (c := 1) one_pos]
      with m hm1 _ h2 h3 h4 h5 h6 h7 h8 h9
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
    refine ⟨hm1, by linarith, h2, by linarith, by linarith, h6, by linarith, by linarith, ?_⟩
    have hsplit : k m = (m : ℝ) ^ (-1 / (6 * βp)) * (m : ℝ) ^ (-1 / (3 * βp)) := by
      rw [hkdef, ← Real.rpow_add hmpos]
      field_simp
      ring_nf
    rw [hsplit]
    have hpos : 0 ≤ (m : ℝ) ^ (-1 / (3 * βp)) := Real.rpow_nonneg hmpos.le _
    calc 4 * ((m : ℝ) ^ (-1 / (6 * βp)) * (m : ℝ) ^ (-1 / (3 * βp))) * sd
        = 4 * sd * (m : ℝ) ^ (-1 / (6 * βp)) * (m : ℝ) ^ (-1 / (3 * βp)) := by ring
      _ ≤ 1 * (m : ℝ) ^ (-1 / (3 * βp)) := mul_le_mul_of_nonneg_right h8.le hpos
      _ = _ := one_mul _
  -- Bad events.
  set Ebad : ℕ → Set Ω := fun m =>
    {ω | ∃ y ∈ grid (k m) ∩ cthickening ρ U, Λ m ω ∩ cube y (δ' * k m) = ∅} with hEbad
  set Fbad : ℕ → Set Ω := fun m =>
    {ω | ∃ x ∈ grid (r m) ∩ cthickening ρ U, ¬ (Λ m ω ∩ cube x (2 * r m)).Subsingleton}
    with hFbad
  have hsmul : ∀ (m : ℕ) (B : Set (EuclideanSpace ℝ (Fin d))), ((m : ℝ≥0∞) • μ) B = (m : ℝ≥0∞) * μ B := fun m B => by
    rw [Measure.smul_apply, smul_eq_mul]
  have hfinK : ∀ (m : ℕ) {B : Set (EuclideanSpace ℝ (Fin d))}, B ⊆ K → ((m : ℝ≥0∞) • μ) B ≠ ∞ := fun m B hB => by
    rw [hsmul]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top m) (measure_mono hB |>.trans_lt hμK).ne
  set C₁ : ℝ := (2 * R + 1) ^ d with hC₁
  set c₁ : ℝ := δ' ^ βp with hc₁
  have hc₁pos : 0 < c₁ := Real.rpow_pos_of_pos hδ' _
  set C₂ : ℝ := (3 * sd) ^ βm * 5 ^ d * (μ K).toReal with hC₂
  have hEb : ∀ᶠ m : ℕ in atTop, P (Ebad m) ≤ ENNReal.ofReal
      (C₁ * ((m : ℝ) ^ ((d : ℝ) / (2 * βp)) * Real.exp (-(c₁ * (m : ℝ) ^ (1 / 2 : ℝ))))) := by
    filter_upwards [hscale] with m hm
    obtain ⟨hm1, hk1, hkr₀, -, -, -, -, hkρ, -⟩ := hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
    have hkpos : 0 < k m := Real.rpow_pos_of_pos hmpos _
    have hYfin : (grid (k m) ∩ cthickening ρ U).Finite :=
      (finite_grid_inter_closedBall hkpos R).subset (inter_subset_inter_right _ hregion)
    have hset : Ebad m = {ω | ∃ y ∈ hYfin.toFinset, Λ m ω ∩ cube y (δ' * k m) = ∅} := by
      ext ω; simp only [hEbad, Set.mem_ofPred_eq, Set.Finite.mem_toFinset]
    have hcubeK : ∀ y ∈ hYfin.toFinset, cube y (δ' * k m) ⊆ K := fun y hy =>
      (cube_subset_closedBall y (by positivity)).trans
        (hballK ((Set.Finite.mem_toFinset _).mp hy).2 (by positivity) hkρ)
    rw [hset]
    refine ((hΛ m).measure_exists_empty_le hYfin.toFinset (δ' * k m) (c₁ * (m : ℝ) ^ (1 / 2 : ℝ))
      (fun y hy => hfinK m (hcubeK y hy)) (fun y hy => ?_)).trans ?_
    · -- The mass of each cube.
      have hyW : y ∈ W := hKW (hballK ((Set.Finite.mem_toFinset _).mp hy).2 le_rfl hρ.le
        (mem_closedBall_self le_rfl))
      have hlow := (hbd (δ' * k m) (by positivity) hkr₀ y hyW).1
      have hball : μ (ball y (δ' * k m)) ≤ μ (cube y (δ' * k m)) :=
        measure_mono (ball_subset_cube y _)
      have hfin : μ (cube y (δ' * k m)) ≠ ∞ :=
        (measure_mono (hcubeK y hy)).trans_lt hμK |>.ne
      rw [hsmul, ENNReal.toReal_mul, ENNReal.toReal_natCast]
      have h1 : (δ' * k m) ^ βp ≤ (μ (cube y (δ' * k m))).toReal :=
        (ENNReal.ofReal_le_iff_le_toReal hfin).mp (hlow.trans hball)
      calc c₁ * (m : ℝ) ^ (1 / 2 : ℝ) = (m : ℝ) * (δ' * k m) ^ βp :=
            (mul_rpow_scale hmpos hδ'.le hβp).symm
        _ ≤ (m : ℝ) * (μ (cube y (δ' * k m))).toReal :=
            mul_le_mul_of_nonneg_left h1 hmpos.le
    · -- Counting the cubes.
      apply ENNReal.ofReal_le_ofReal
      rw [← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      have hcard : (hYfin.toFinset.card : ℝ) ≤ (2 * R / k m + 1) ^ d := by
        rw [← Set.ncard_eq_toFinset_card _ hYfin]
        refine le_trans ?_ (ncard_grid_inter_closedBall_le hkpos hR)
        exact_mod_cast Set.ncard_le_ncard (inter_subset_inter_right _ hregion)
          (finite_grid_inter_closedBall hkpos R)
      refine hcard.trans ?_
      have hle : 2 * R / k m + 1 ≤ (2 * R + 1) * (m : ℝ) ^ ((1 : ℝ) / (2 * βp)) := by
        have hinv : (k m)⁻¹ = (m : ℝ) ^ ((1 : ℝ) / (2 * βp)) := by
          rw [hkdef, ← Real.rpow_neg hmpos.le, neg_div, neg_neg]
        have hone : 1 ≤ (k m)⁻¹ := one_le_inv_iff₀.mpr ⟨hkpos, hk1⟩
        rw [← hinv, div_eq_mul_inv]
        nlinarith
      calc (2 * R / k m + 1) ^ d ≤ ((2 * R + 1) * (m : ℝ) ^ ((1 : ℝ) / (2 * βp))) ^ d :=
            pow_le_pow_left₀ (by positivity) hle d
        _ = C₁ * (m : ℝ) ^ ((d : ℝ) / (2 * βp)) := by
            rw [mul_pow, hC₁, ← Real.rpow_mul_natCast hmpos.le]
            congr 2
            ring
  have hFb : ∀ᶠ m : ℕ in atTop, P (Fbad m) ≤ ENNReal.ofReal (C₂ * (m : ℝ) ^ (-6 : ℝ)) := by
    filter_upwards [hscale] with m hm
    obtain ⟨hm1, -, -, -, -, hrr₀, hrρ, -, -⟩ := hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
    have hrpos : 0 < r m := Real.rpow_pos_of_pos hmpos _
    have hXfin : (grid (r m) ∩ cthickening ρ U).Finite :=
      (finite_grid_inter_closedBall hrpos R).subset (inter_subset_inter_right _ hregion)
    have hset : Fbad m =
        {ω | ∃ x ∈ hXfin.toFinset, ¬ (Λ m ω ∩ cube x (2 * r m)).Subsingleton} := by
      ext ω; simp only [hFbad, Set.mem_ofPred_eq, Set.Finite.mem_toFinset]
    have hcubeK : ∀ x ∈ hXfin.toFinset, cube x (2 * r m) ⊆ K := fun x hx =>
      (cube_subset_closedBall x (by positivity)).trans
        (hballK ((Set.Finite.mem_toFinset _).mp hx).2 (by positivity) hrρ)
    rw [hset]
    set M : ℝ := (3 * sd) ^ βm * (m : ℝ) ^ (-7 : ℝ) with hM
    refine ((hΛ m).measure_exists_double_le hXfin.toFinset (2 * r m) M
      (fun x hx => hfinK m (hcubeK x hx)) (fun x hx => ?_)).trans ?_
    · have hxW : x ∈ W := hKW (hballK ((Set.Finite.mem_toFinset _).mp hx).2 le_rfl hρ.le
        (mem_closedBall_self le_rfl))
      have hup := (hbd (3 * sd * r m) (by positivity) hrr₀ x hxW).2
      have hsub : cube x (2 * r m) ⊆ ball x (3 * sd * r m) :=
        (cube_subset_closedBall x (by positivity)).trans
          (closedBall_subset_ball (by nlinarith))
      have hfin : μ (ball x (3 * sd * r m)) ≠ ∞ := (hup.trans_lt ENNReal.ofReal_lt_top).ne
      rw [hsmul, ENNReal.toReal_mul, ENNReal.toReal_natCast]
      calc (m : ℝ) * (μ (cube x (2 * r m))).toReal
          ≤ (m : ℝ) * (μ (ball x (3 * sd * r m))).toReal :=
            mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hfin (measure_mono hsub)) hmpos.le
        _ ≤ (m : ℝ) * (3 * sd * r m) ^ βm :=
            mul_le_mul_of_nonneg_left (ENNReal.toReal_le_of_le_ofReal (by positivity) hup)
              hmpos.le
        _ = M := mul_rpow_scale' hmpos (by positivity) hβm
    · apply ENNReal.ofReal_le_ofReal
      have hsum : ∑ x ∈ hXfin.toFinset, (((m : ℝ≥0∞) • μ) (cube x (2 * r m))).toReal ≤
          (m : ℝ) * (5 ^ d * (μ K).toReal) := by
        have hfinμ : ∀ x ∈ hXfin.toFinset, μ (cube x (2 * r m)) ≠ ∞ := fun x hx =>
          (measure_mono (hcubeK x hx)).trans_lt hμK |>.ne
        simp only [hsmul, ENNReal.toReal_mul, ENNReal.toReal_natCast, ← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ hmpos.le
        rw [← ENNReal.toReal_sum hfinμ]
        have hover := sum_measure_le_of_ncard_le μ hXfin.toFinset (fun x => cube x (2 * r m))
          (fun x _ => measurableSet_cube x _) (M := 5 ^ d) (fun y => ?_)
        · have hunion : (⋃ x ∈ hXfin.toFinset, cube x (2 * r m)) ⊆ K :=
            iUnion₂_subset fun x hx => hcubeK x hx
          have hbound : ∑ x ∈ hXfin.toFinset, μ (cube x (2 * r m)) ≤ (5 ^ d : ℝ≥0∞) * μ K :=
            hover.trans (by push_cast; gcongr)
          refine (ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hμK.ne) hbound).trans ?_
          rw [ENNReal.toReal_mul]
          simp
        · -- Bounded overlap of the cubes.
          have hfinY : {x | x ∈ grid (r m) ∧ y ∈ cube x (2 * r m)}.Finite := by
            refine (finite_grid_inter_closedBall hrpos (‖y‖ + 2 * r m * sd)).subset ?_
            rintro x ⟨hxG, hyx⟩
            refine ⟨hxG, mem_closedBall_zero_iff.mpr ?_⟩
            have h1 : dist y x ≤ 2 * r m * sd := dist_le_mul_sqrt y x (by positivity) hyx
            calc ‖x‖ ≤ ‖y‖ + dist y x := by
                  rw [dist_comm, dist_eq_norm]
                  exact norm_le_insert' x y |>.trans (by rw [norm_sub_rev])
              _ ≤ _ := by linarith
          have h1 : {i | i ∈ hXfin.toFinset ∧ y ∈ cube i (2 * r m)} ⊆
              {x | x ∈ grid (r m) ∧ y ∈ cube x (2 * r m)} := fun x hx =>
            ⟨((Set.Finite.mem_toFinset _).mp hx.1).1, hx.2⟩
          have h2 := ncard_grid_cube_mem_le hrpos y
          have h3 := Set.ncard_le_ncard h1 hfinY
          exact_mod_cast (show ((({i | i ∈ hXfin.toFinset ∧ y ∈ cube i (2 * r m)}).ncard : ℕ) :
            ℝ) ≤ 5 ^ d from (by exact_mod_cast h3 : _ ≤ (_ : ℝ)).trans h2)
      calc M * ∑ x ∈ hXfin.toFinset, (((m : ℝ≥0∞) • μ) (cube x (2 * r m))).toReal
          ≤ M * ((m : ℝ) * (5 ^ d * (μ K).toReal)) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = C₂ * (m : ℝ) ^ (-6 : ℝ) := by
            rw [hM, hC₂]
            have : (m : ℝ) ^ (-7 : ℝ) * (m : ℝ) = (m : ℝ) ^ (-6 : ℝ) := by
              rw [← Real.rpow_add_one hmpos.ne']
              norm_num
            calc (3 * sd) ^ βm * (m : ℝ) ^ (-7 : ℝ) * ((m : ℝ) * (5 ^ d * (μ K).toReal))
                = (3 * sd) ^ βm * 5 ^ d * (μ K).toReal * ((m : ℝ) ^ (-7 : ℝ) * (m : ℝ)) := by
                  ring
              _ = _ := by rw [this]
  -- Borel–Cantelli.
  set b : ℕ → ℝ := fun m =>
    C₁ * ((m : ℝ) ^ ((d : ℝ) / (2 * βp)) * Real.exp (-(c₁ * (m : ℝ) ^ (1 / 2 : ℝ)))) +
      C₂ * (m : ℝ) ^ (-6 : ℝ) with hb
  have hbsum : Summable b :=
    ((summable_rpow_mul_exp_neg_rpow _ hc₁pos).mul_left C₁).add
      ((Real.summable_nat_rpow.mpr (by norm_num)).mul_left C₂)
  have hbnn : ∀ m, 0 ≤ b m := fun m => by
    have : 0 ≤ (μ K).toReal := ENNReal.toReal_nonneg
    positivity
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp (hEb.and hFb)
  set g : ℕ → ℝ := fun m => b m + if m < m₀ then 1 else 0 with hg
  have hgsum : Summable g := hbsum.add (summable_of_ne_finset_zero (s := Finset.range m₀)
    (fun m hm => by simp only [Finset.mem_range] at hm; simp [hm]))
  have hgnn : ∀ m, 0 ≤ g m := fun m => add_nonneg (hbnn m) (by split_ifs <;> norm_num)
  have hbad : ∀ m, P (Ebad m ∪ Fbad m) ≤ ENNReal.ofReal (g m) := by
    intro m
    by_cases hm : m < m₀
    · refine prob_le_one.trans ?_
      rw [hg]
      simp only [hm, ite_true]
      exact ENNReal.one_le_ofReal.mpr (by linarith [hbnn m])
    · obtain ⟨h1, h2⟩ := hm₀ m (not_lt.mp hm)
      refine (measure_union_le _ _).trans ?_
      refine (add_le_add h1 h2).trans ?_
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      simp only [hg, hb, hm, ite_false, add_zero, le_refl]
  have htsum : (∑' m, P (Ebad m ∪ Fbad m)) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbad)
    rw [← ENNReal.ofReal_tsum_of_nonneg hgnn hgsum]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem htsum] with ω hω
  filter_upwards [hω, hscale] with m hm hsc
  obtain ⟨hm1, -, -, h3k, h2r, -, -, -, hlast⟩ := hsc
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  have hE : ∀ y ∈ grid (k m) ∩ cthickening ρ U, (Λ m ω ∩ cube y (δ' * k m)).Nonempty := by
    intro y hy
    by_contra h
    exact hm (Or.inl ⟨y, hy, not_nonempty_iff_eq_empty.mp h⟩)
  have hF : ∀ x ∈ grid (r m) ∩ cthickening ρ U, (Λ m ω ∩ cube x (2 * r m)).Subsingleton := by
    intro x hx
    by_contra h
    exact hm (Or.inr ⟨x, hx, h⟩)
  have hkpos : 0 < k m := Real.rpow_pos_of_pos hmpos _
  refine ⟨fun s hs hcell => ?_, fun y hy => ?_⟩
  · obtain ⟨hin, hout⟩ := cell_between_balls_of_counts hd hδ0 (by linarith) hδ5
      hkpos (Real.rpow_pos_of_pos hmpos _) h3k h2r hE hF s hs hcell
    exact ⟨ball_subset_closedBall.trans hin, hout.trans (ball_subset_ball hlast)⟩
  · -- Density: a point of `Λ_m` in the cube of the nearest grid point.
    obtain ⟨g, hgG, hgy⟩ := exists_grid_near hkpos y
    have hgy' : dist g y ≤ k m / 2 * sd := dist_le_mul_sqrt g y (by positivity) hgy
    have hgU : g ∈ cthickening ρ U :=
      mem_cthickening_of_dist_le g y ρ U hy
        (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Rg) hkpos.le])
    obtain ⟨s, hsΛ, hsc⟩ := hE g ⟨hgG, hgU⟩
    have hsg : dist s g ≤ δ' * k m * sd := dist_le_mul_sqrt s g (by positivity) hsc
    have hδ'le : δ' ≤ 1 / 4 := min_le_right _ _
    have hks : 0 < k m * sd := mul_pos hkpos hsd
    refine ⟨s, hsΛ, ?_⟩
    calc dist s y ≤ dist s g + dist g y := dist_triangle _ _ _
      _ < 4 * k m * sd := by nlinarith
      _ ≤ _ := hlast

/-- **Proposition 1.1**, first part (corrected): almost surely, for all large `m`, every Voronoi
cell of `Λ_m` meeting `U` lies between the balls of radii `m^{-8/β⁻}` and `m^{-1/(3β⁺)}`. -/
theorem voronoi_cells_between_balls (hd : 1 ≤ d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hUb : Bornology.IsBounded U) {μ : Measure (EuclideanSpace ℝ (Fin d))} {βp βm : ℝ}
    (hβp : 0 < βp) (hβm : 0 < βm) {W : Set (EuclideanSpace ℝ (Fin d))}
    (hW : IsOpen W) (hUW : closure U ⊆ W) (hμ : HolderMassBounds μ W βp βm)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Λ : ℕ → Ω → Set (EuclideanSpace ℝ (Fin d)))
    (hΛ : ∀ m : ℕ, IsPoissonPointProcess P (Λ m) ((m : ℝ≥0∞) • μ)) :
    ∀ᵐ ω ∂P, ∀ᶠ m in atTop, ∀ s ∈ Λ m ω, (cell (Λ m ω) s ∩ U).Nonempty →
      ball s ((m : ℝ) ^ (-8 / βm)) ⊆ cell (Λ m ω) s ∧
        cell (Λ m ω) s ⊆ ball s ((m : ℝ) ^ (-1 / (3 * βp))) := by
  filter_upwards [voronoi_cells_between_balls_aux hd hUb hβp hβm hW hUW hμ P Λ hΛ] with ω hω
  exact hω.mono fun _ hm => hm.1

end SpherePackings
