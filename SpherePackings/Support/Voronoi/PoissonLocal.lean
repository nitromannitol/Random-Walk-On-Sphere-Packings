module

-- Built on Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne (commit cf73d6e).
public import SpherePackings.Support.Voronoi.PoissonTilings

@[expose] public section

/-!
# Proposition 1.1 for the process restricted to `W`

The proofs use the Poisson process only through its points in the neighbourhood `W` of
`closure U` where the mass bounds hold.  So it suffices that `Λ_m ∩ W` be a Poisson point process of
intensity `m μ|_W` and that `Λ_m` be locally finite; this follows from `Λ_m` being a Poisson point
process of intensity `m μ` (`IsPoissonPointProcess.restrict_inter`), and it allows `μ` to have atoms
outside `W`.
-/

open MeasureTheory Metric Filter Set
open scoped ENNReal NNReal Topology

namespace SpherePackings

open BouRabeeGwynne Voronoi

variable {d : ℕ}

/-- Intersecting with a set `W` that contains `B` does not change the points of `A` in `B`. -/
private lemma restrict_inter_eq_of_subset {A W B : Set (EuclideanSpace ℝ (Fin d))} (hB : B ⊆ W) :
    (A ∩ W) ∩ B = A ∩ B := by
  rw [Set.inter_assoc, Set.inter_eq_right.mpr hB]

/-- The points of a Poisson point process in a measurable set `W` form a Poisson point process with
the restricted intensity. -/
theorem IsPoissonPointProcess.restrict_inter {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Λ : Ω → Set (EuclideanSpace ℝ (Fin d))} {ν : Measure (EuclideanSpace ℝ (Fin d))}
    (h : IsPoissonPointProcess P Λ ν) {W : Set (EuclideanSpace ℝ (Fin d))} (hW : MeasurableSet W) :
    IsPoissonPointProcess P (fun ω => Λ ω ∩ W) (ν.restrict W) := by
  refine ⟨fun B hB ω => ?_, fun B hB hνB => ?_, fun B hB hνB => ?_, fun n B hB hνB hdisj => ?_⟩
  · show (Λ ω ∩ W ∩ B).Finite
    exact (h.finite B hB ω).subset fun x hx => ⟨hx.1.1, hx.2⟩
  · rw [Measure.restrict_apply hB] at hνB
    filter_upwards [h.ae_finite (B ∩ W) (hB.inter hW) hνB] with ω hω
    show (Λ ω ∩ W ∩ B).Finite
    rwa [Set.inter_assoc, Set.inter_comm W B]
  · show ProbabilityTheory.HasLaw (fun ω => (Λ ω ∩ W ∩ B).ncard)
      (ProbabilityTheory.poissonMeasure ((ν.restrict W) B).toNNReal) P
    rw [Measure.restrict_apply hB] at hνB ⊢
    have e : (fun ω => (Λ ω ∩ W ∩ B).ncard) = fun ω => (Λ ω ∩ (B ∩ W)).ncard :=
      funext fun ω => by rw [Set.inter_assoc, Set.inter_comm W B]
    rw [e]
    exact h.hasLaw (B ∩ W) (hB.inter hW) hνB
  · show ProbabilityTheory.iIndepFun (fun i ω => (Λ ω ∩ W ∩ B i).ncard) P
    have hν' : ∀ i, ν (B i ∩ W) ≠ ∞ := fun i => by
      rw [← Measure.restrict_apply (hB i)]; exact hνB i
    have hdisj' : Pairwise (Function.onFun Disjoint fun i => B i ∩ W) := fun i j hij =>
      Disjoint.mono inter_subset_left inter_subset_left (hdisj hij : Disjoint (B i) (B j))
    have e : ∀ i ω, Λ ω ∩ W ∩ B i = Λ ω ∩ (B i ∩ W) := fun i ω => by
      rw [Set.inter_assoc, Set.inter_comm W (B i)]
    simp only [e]
    exact h.indep n (fun i => B i ∩ W) (fun i => (hB i).inter hW) hν' hdisj'

theorem voronoi_cells_between_balls_aux_local (hd : 1 ≤ d) {U : Set (EuclideanSpace ℝ (Fin d))} (hUb : Bornology.IsBounded U)
    {μ : Measure (EuclideanSpace ℝ (Fin d))} {βp βm : ℝ} (hβp : 0 < βp) (hβm : 0 < βm) {W : Set (EuclideanSpace ℝ (Fin d))}
    (hW : IsOpen W) (hUW : closure U ⊆ W) (hμ : HolderMassBounds μ W βp βm)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Λ : ℕ → Ω → Set (EuclideanSpace ℝ (Fin d))) (hΛ : ∀ m : ℕ, IsPoissonPointProcess P (fun ω => Λ m ω ∩ W) ((m : ℝ≥0∞) • μ.restrict W)) :
    ∀ᵐ ω ∂P, ∀ᶠ m in atTop, (∀ s ∈ Λ m ω, (cell (Λ m ω) s ∩ U).Nonempty →
      ball s ((m : ℝ) ^ (-8 / βm)) ⊆ cell (Λ m ω) s ∧
        cell (Λ m ω) s ⊆ ball s ((m : ℝ) ^ (-1 / (3 * βp)))) ∧
      ∀ y ∈ U, ∃ s ∈ Λ m ω, dist s y < (m : ℝ) ^ (-1 / (3 * βp)) := by
  -- Local finiteness is not needed: the proof only uses the counts of `Λ m ω ∩ W` in cubes, so
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
  -- Every cube below lies in `K ⊆ W`, where the restricted intensity is the intensity itself.
  have hsmulW : ∀ (m : ℕ) {B : Set (EuclideanSpace ℝ (Fin d))}, B ⊆ K →
      ((m : ℝ≥0∞) • μ.restrict W) B = (m : ℝ≥0∞) * μ B := fun m {B} hB => by
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_eq_self μ (hB.trans hKW)]
  have hfinK : ∀ (m : ℕ) {B : Set (EuclideanSpace ℝ (Fin d))}, B ⊆ K →
      ((m : ℝ≥0∞) • μ.restrict W) B ≠ ∞ := fun m {B} hB => by
    rw [hsmulW m hB]
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
    -- The points of `Λ m ω ∩ W` in these cubes are the points of `Λ m ω`.
    have hsub : Ebad m ⊆ {ω | ∃ y ∈ hYfin.toFinset, (Λ m ω ∩ W) ∩ cube y (δ' * k m) = ∅} := by
      rw [hset]
      rintro ω ⟨y, hy, hω⟩
      exact ⟨y, hy, by rw [restrict_inter_eq_of_subset ((hcubeK y hy).trans hKW)]; exact hω⟩
    refine (measure_mono hsub).trans (((hΛ m).measure_exists_empty_le hYfin.toFinset (δ' * k m)
      (c₁ * (m : ℝ) ^ (1 / 2 : ℝ)) (fun y hy => hfinK m (hcubeK y hy)) (fun y hy => ?_)).trans ?_)
    · -- The mass of each cube.
      have hyW : y ∈ W := hKW (hballK ((Set.Finite.mem_toFinset _).mp hy).2 le_rfl hρ.le
        (mem_closedBall_self le_rfl))
      have hlow := (hbd (δ' * k m) (by positivity) hkr₀ y hyW).1
      have hball : μ (ball y (δ' * k m)) ≤ μ (cube y (δ' * k m)) :=
        measure_mono (ball_subset_cube y _)
      have hfin : μ (cube y (δ' * k m)) ≠ ∞ :=
        (measure_mono (hcubeK y hy)).trans_lt hμK |>.ne
      rw [hsmulW m (hcubeK y hy), ENNReal.toReal_mul, ENNReal.toReal_natCast]
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
    have hsub : Fbad m ⊆
        {ω | ∃ x ∈ hXfin.toFinset, ¬ ((Λ m ω ∩ W) ∩ cube x (2 * r m)).Subsingleton} := by
      rw [hset]
      rintro ω ⟨x, hx, hω⟩
      exact ⟨x, hx, by rw [restrict_inter_eq_of_subset ((hcubeK x hx).trans hKW)]; exact hω⟩
    set M : ℝ := (3 * sd) ^ βm * (m : ℝ) ^ (-7 : ℝ) with hM
    refine (measure_mono hsub).trans (((hΛ m).measure_exists_double_le hXfin.toFinset (2 * r m) M
      (fun x hx => hfinK m (hcubeK x hx)) (fun x hx => ?_)).trans ?_)
    · have hxW : x ∈ W := hKW (hballK ((Set.Finite.mem_toFinset _).mp hx).2 le_rfl hρ.le
        (mem_closedBall_self le_rfl))
      have hup := (hbd (3 * sd * r m) (by positivity) hrr₀ x hxW).2
      have hsubB : cube x (2 * r m) ⊆ ball x (3 * sd * r m) :=
        (cube_subset_closedBall x (by positivity)).trans
          (closedBall_subset_ball (by nlinarith))
      have hfin : μ (ball x (3 * sd * r m)) ≠ ∞ := (hup.trans_lt ENNReal.ofReal_lt_top).ne
      rw [hsmulW m (hcubeK x hx), ENNReal.toReal_mul, ENNReal.toReal_natCast]
      calc (m : ℝ) * (μ (cube x (2 * r m))).toReal
          ≤ (m : ℝ) * (μ (ball x (3 * sd * r m))).toReal :=
            mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hfin (measure_mono hsubB)) hmpos.le
        _ ≤ (m : ℝ) * (3 * sd * r m) ^ βm :=
            mul_le_mul_of_nonneg_left (ENNReal.toReal_le_of_le_ofReal (by positivity) hup)
              hmpos.le
        _ = M := mul_rpow_scale' hmpos (by positivity) hβm
    · apply ENNReal.ofReal_le_ofReal
      have hsum : ∑ x ∈ hXfin.toFinset, (((m : ℝ≥0∞) • μ.restrict W) (cube x (2 * r m))).toReal ≤
          (m : ℝ) * (5 ^ d * (μ K).toReal) := by
        have hfinμ : ∀ x ∈ hXfin.toFinset, μ (cube x (2 * r m)) ≠ ∞ := fun x hx =>
          (measure_mono (hcubeK x hx)).trans_lt hμK |>.ne
        have hcongr : ∑ x ∈ hXfin.toFinset, (((m : ℝ≥0∞) • μ.restrict W) (cube x (2 * r m))).toReal =
            ∑ x ∈ hXfin.toFinset, (m : ℝ) * (μ (cube x (2 * r m))).toReal :=
          Finset.sum_congr rfl fun x hx => by
            rw [hsmulW m (hcubeK x hx), ENNReal.toReal_mul, ENNReal.toReal_natCast]
        rw [hcongr, ← Finset.mul_sum]
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
      calc M * ∑ x ∈ hXfin.toFinset, (((m : ℝ≥0∞) • μ.restrict W) (cube x (2 * r m))).toReal
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

theorem voronoi_cells_between_balls_local (hd : 1 ≤ d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hUb : Bornology.IsBounded U) {μ : Measure (EuclideanSpace ℝ (Fin d))} {βp βm : ℝ}
    (hβp : 0 < βp) (hβm : 0 < βm) {W : Set (EuclideanSpace ℝ (Fin d))}
    (hW : IsOpen W) (hUW : closure U ⊆ W) (hμ : HolderMassBounds μ W βp βm)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Λ : ℕ → Ω → Set (EuclideanSpace ℝ (Fin d)))
    (hΛ : ∀ m : ℕ, IsPoissonPointProcess P (fun ω => Λ m ω ∩ W) ((m : ℝ≥0∞) • μ.restrict W)) :
    ∀ᵐ ω ∂P, ∀ᶠ m in atTop, ∀ s ∈ Λ m ω, (cell (Λ m ω) s ∩ U).Nonempty →
      ball s ((m : ℝ) ^ (-8 / βm)) ⊆ cell (Λ m ω) s ∧
        cell (Λ m ω) s ⊆ ball s ((m : ℝ) ^ (-1 / (3 * βp))) := by
  filter_upwards [voronoi_cells_between_balls_aux_local hd hUb hβp hβm hW hUW hμ P Λ hΛ]
    with ω hω
  exact hω.mono fun _ hm => hm.1

theorem voronoi_tilings_hypotheses_local (hd : 1 ≤ d) {U : Set (Euc d)} (hU : IsDomain U)
    (hUb : Bornology.IsBounded U) {μ : Measure (Euc d)} {βp βm : ℝ} (hβp : 0 < βp)
    (hβm : 0 < βm) {W : Set (Euc d)} (hW : IsOpen W) (hUW : closure U ⊆ W)
    (hμ : HolderMassBounds μ W βp βm)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Λ : ℕ → Ω → Set (Euc d)) (hΛ : ∀ m : ℕ, IsPoissonPointProcess P (fun ω => Λ m ω ∩ W) ((m : ℝ≥0∞) • μ.restrict W))
    (hlf : ∀ m ω (B : Set (EuclideanSpace ℝ (Fin d))), Bornology.IsBounded B → (Λ m ω ∩ B).Finite) :
    ∀ᵐ ω ∂P, ∃ G : TilingSequence d, HasAmbientCollar U G.domain ∧
      (∀ᶠ m in atTop, IsVoronoiTilingOf (G.tiling m) (Λ m ω) G.domain) ∧
      Nonempty (NearestVertexData G) ∧ (∀ N : NearestVertexData G, N.ApproximationCondition) ∧
      RegularityII G := by
  -- The neighbourhood `D` and the compact set `K` carrying everything.
  obtain ⟨ρ₀, hρ₀, hρ₀W⟩ := hUb.isCompact_closure.exists_cthickening_subset_open hW hUW
  set ρ := ρ₀ / 2 with hρdef
  have hρ : 0 < ρ := half_pos hρ₀
  obtain ⟨D, hDdef⟩ : ∃ D : Set (Euc d), D = thickening ρ U := ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K : Set (Euc d), K = cthickening ρ₀ U := ⟨_, rfl⟩
  have hKW : K ⊆ W := by rw [hKdef, ← cthickening_closure]; exact hρ₀W
  have hKc : IsCompact K :=
    hKdef ▸ isCompact_of_isClosed_isBounded isClosed_cthickening hUb.cthickening
  have hμK : μ K < ∞ := HolderMassBounds.measure_lt_top hμ hKc hKW
  have hDb : Bornology.IsBounded D := hDdef ▸ hUb.thickening
  have hDopen : IsOpen D := hDdef ▸ isOpen_thickening
  have hDW : closure D ⊆ W := hDdef ▸ (closure_thickening_subset_cthickening ρ U).trans
    ((cthickening_mono (by linarith) U).trans (hKdef ▸ hKW))
  have hUD : HasAmbientCollar U D := by
    rw [HasAmbientCollar, hDopen.interior_eq]
    exact hDdef ▸ closure_subset_thickening hρ U
  obtain ⟨z₀, hz₀⟩ := hU.2.1
  have hz₀D : z₀ ∈ D := hDdef ▸ self_subset_thickening hρ U hz₀
  -- Proposition 1.1 (first part) for `D`.
  filter_upwards [voronoi_cells_between_balls_aux_local hd hDb hβp hβm hW hDW hμ P Λ hΛ]
    with ω hω
  set rr : ℕ → ℝ := fun m => (m : ℝ) ^ (-8 / βm) with hrr
  set RR : ℕ → ℝ := fun m => (m : ℝ) ^ (-1 / (3 * βp)) with hRR
  have hRR0 : Tendsto RR atTop (𝓝 0) := by
    have := tendsto_natCast_rpow_neg (a := 1 / (3 * βp)) (by positivity)
    simpa only [hRR, neg_div] using this
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp (hω.and ((eventually_ge_atTop 1).and
    (hRR0.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ρ / 6)))))
  have hmaxT : Tendsto (fun n : ℕ => max n m₀) atTop atTop :=
    tendsto_atTop_atTop_of_monotone (fun _ _ h => max_le_max h le_rfl) fun b => ⟨b, le_max_left _ _⟩
  -- Good Voronoi data from `m₀` on.
  have hgood : ∀ m, m₀ ≤ m → GoodVoronoi (Λ m ω) D (rr m / 2) (RR m) := by
    intro m hm
    obtain ⟨⟨hcells, hdense⟩, hm1, hRsmall⟩ := hm₀ m hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
    have hRpos : 0 < RR m := Real.rpow_pos_of_pos hmpos _
    have hfin6 : (Λ m ω ∩ cthickening (6 * RR m) D).Finite := by
      exact hlf m ω _ hDb.cthickening
    refine ⟨by positivity, hRpos, hDb, fun s hs => ?_, fun s hs => ?_, hfin6, fun y hy => ?_⟩
    · exact (closedBall_subset_ball (half_lt_self (Real.rpow_pos_of_pos hmpos _))).trans
        (hcells s hs.1 hs.2).1
    · exact (hcells s hs.1 hs.2).2.trans ball_subset_closedBall
    · obtain ⟨s₀, hs₀, hdist⟩ := hdense y hy
      refine exists_mem_cell_of_near hs₀ hdist (hfin6.subset ?_)
      refine inter_subset_inter_right _ fun x hx => ?_
      exact mem_cthickening_of_dist_le x y _ D hy
        ((mem_closedBall.mp hx).trans (by linarith))
  -- The tiling sequence.
  let G : TilingSequence d :=
    { domain := D
      tiling := fun n => voronoiTiling (Λ (max n m₀) ω) D (hgood (max n m₀) (le_max_right _ _))
      common_domain := fun n => voronoiTiling_domain _ _ _ }
  have hGt : ∀ n, G.tiling n =
      voronoiTiling (Λ (max n m₀) ω) D (hgood (max n m₀) (le_max_right _ _)) := fun _ => rfl
  have hne : ∀ n, Nonempty (G.tiling n).V := fun n =>
    ⟨(exists_vertex_dist_le (hgood (max n m₀) (le_max_right _ _)) hz₀D).choose⟩
  -- Every nearest vertex is close.
  have hnear : ∀ (N : NearestVertexData G) n, ∀ z ∈ D,
      dist ((G.tiling n).pos (N.vertex n z)) z ≤ RR (max n m₀) := by
    intro N n z hz
    obtain ⟨v, hv⟩ := exists_vertex_dist_le (hgood (max n m₀) (le_max_right _ _)) hz
    rw [dist_comm]
    exact (N.isNearest n z hz v).trans hv
  have hRRmax : Tendsto (fun n => RR (max n m₀)) atTop (𝓝 0) :=
    hRR0.comp hmaxT
  have hmesh : ∀ n, (G.tiling n).mesh ≤ ENNReal.ofReal (2 * RR (max n m₀)) := fun n =>
    voronoiTiling_mesh_le (hgood (max n m₀) (le_max_right _ _))
  refine ⟨G, hUD, ?_, ?_, ?_, ?_⟩
  · -- Eventually the tiling is the Voronoi tiling of `Λ_m`.
    filter_upwards [eventually_ge_atTop m₀] with n hn
    have e : Λ n ω = Λ (max n m₀) ω := by rw [max_eq_left hn]
    show IsVoronoiTilingOf (voronoiTiling (Λ (max n m₀) ω) D _) (Λ n ω) D
    rw [e]
    exact voronoiTiling_isVoronoiTilingOf _
  · -- A choice of nearest vertices.
    classical
    refine ⟨{ vertex := fun n z => if hz : z ∈ D then
                (exists_nearest_vertex (hgood (max n m₀) (le_max_right _ _)) hz).choose
              else Classical.choice (hne n)
              isNearest := fun n z hz v => ?_ }⟩
    change z ∈ D at hz
    simp only [hz, dite_true]
    exact (exists_nearest_vertex (hgood (max n m₀) (le_max_right _ _)) hz).choose_spec v
  · -- The approximation condition (1.3), for every choice of nearest vertices.
    intro N
    have hbound : ∀ n, (G.tiling n).mesh + N.uniformError n ≤
        ENNReal.ofReal (3 * RR (max n m₀)) := by
      intro n
      have hR : 0 ≤ RR (max n m₀) :=
        (Real.rpow_pos_of_pos (by exact_mod_cast (hm₀ _ (le_max_right n m₀)).2.1) _).le
      have hu : N.uniformError n ≤ ENNReal.ofReal (RR (max n m₀)) :=
        iSup_le fun z => ENNReal.ofReal_le_ofReal (hnear N n z.1 z.2)
      calc _ ≤ ENNReal.ofReal (2 * RR (max n m₀)) + ENNReal.ofReal (RR (max n m₀)) :=
            add_le_add (hmesh n) hu
        _ = _ := by rw [← ENNReal.ofReal_add (by positivity) hR]; ring_nf
    have hlim : Tendsto (fun n => ENNReal.ofReal (3 * RR (max n m₀))) atTop (𝓝 0) := by
      have := (hRRmax.const_mul 3)
      rw [mul_zero] at this
      simpa using ENNReal.tendsto_ofReal this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => bot_le) hbound
  · -- Hypothesis (II): the smallest tile has volume at least `exp(-q_n)`, `q_n = O(log n)`.
    have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    set c₀ : ℝ := Real.sqrt Real.pi ^ d / Real.Gamma (d / 2 + 1) with hc₀
    have hc₀pos : 0 < c₀ := by
      rw [hc₀]
      exact div_pos (pow_pos (Real.sqrt_pos.mpr Real.pi_pos) _)
        (Real.Gamma_pos_of_pos (by positivity))
    set ρn : ℕ → ℝ := fun n => rr (max n m₀) / 2 with hρn
    have hρnpos : ∀ n, 0 < ρn n := fun n =>
      half_pos (Real.rpow_pos_of_pos (by exact_mod_cast (hm₀ _ (le_max_right n m₀)).2.1) _)
    set q : ℕ → ℝ := fun n => -Real.log (ρn n ^ d * c₀) with hq
    have hvol : ∀ n, ENNReal.ofReal (ρn n ^ d * c₀) = volume (ball (0 : Euc d) (ρn n)) := by
      intro n
      rw [EuclideanSpace.volume_ball, Fintype.card_fin, ← ENNReal.ofReal_pow (hρnpos n).le,
        ← ENNReal.ofReal_mul (pow_nonneg (hρnpos n).le _)]
    -- `q_n ≥ 0` eventually.
    have hqnn : ∀ᶠ n in atTop, 0 ≤ q n := by
      have hsmall : Tendsto (fun n => ρn n ^ d * c₀) atTop (𝓝 0) := by
        have hρ0 : Tendsto ρn atTop (𝓝 0) := by
          have hrr0 : Tendsto rr atTop (𝓝 0) := by
            have := tendsto_natCast_rpow_neg (a := 8 / βm) (by positivity)
            simpa only [hrr, neg_div] using this
          have := (hrr0.comp hmaxT).div_const 2
          simpa [hρn] using this
        have := (hρ0.pow d).mul_const c₀
        rwa [zero_pow (by omega), zero_mul] at this
      filter_upwards [hsmall.eventually (gt_mem_nhds one_pos)] with n hn
      rw [hq, neg_nonneg]
      exact Real.log_nonpos (by positivity) hn.le
    refine ⟨q, ?_, ?_⟩
    · -- `mesh · q → 0`.
      have hq_eq : ∀ n, q n = (d : ℝ) * (8 / βm) * Real.log ((max n m₀ : ℕ) : ℝ) +
          ((d : ℝ) * Real.log 2 - Real.log c₀) := by
        intro n
        have hm1 : (1 : ℝ) ≤ (max n m₀ : ℕ) := by exact_mod_cast (hm₀ _ (le_max_right n m₀)).2.1
        have hmpos : (0 : ℝ) < (max n m₀ : ℕ) := by linarith
        show -Real.log (ρn n ^ d * c₀) = _
        rw [Real.log_mul (pow_pos (hρnpos n) _).ne' hc₀pos.ne', Real.log_pow]
        show -((d : ℝ) * Real.log ((max n m₀ : ℕ) ^ (-8 / βm) / 2) + Real.log c₀) = _
        rw [Real.log_div (Real.rpow_pos_of_pos hmpos _).ne' two_ne_zero, Real.log_rpow hmpos]
        ring
      have hlog : Tendsto (fun n : ℕ => RR n * Real.log n) atTop (𝓝 0) := by
        have h := (isLittleO_log_rpow_atTop (r := 1 / (3 * βp)) (by positivity)).tendsto_div_nhds_zero
        have h' := h.comp tendsto_natCast_atTop_atTop
        refine h'.congr' ?_
        filter_upwards [eventually_ge_atTop 1] with n hn
        have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
        simp only [Function.comp_apply, hRR, Real.rpow_neg hnpos.le, neg_div]
        rw [div_eq_inv_mul]
      have hmain : Tendsto (fun n : ℕ => 2 * RR (max n m₀) * q n) atTop (𝓝 0) := by
        have h1 : Tendsto (fun n : ℕ => 2 * (d : ℝ) * (8 / βm) * (RR (max n m₀) *
            Real.log (max n m₀ : ℕ))) atTop (𝓝 0) := by
          have := (hlog.comp hmaxT).const_mul
            (2 * (d : ℝ) * (8 / βm))
          rw [mul_zero] at this
          exact this
        have h2 := (hRRmax.const_mul (2 * ((d : ℝ) * Real.log 2 - Real.log c₀)))
        rw [mul_zero] at h2
        have := h1.add h2
        rw [add_zero] at this
        refine this.congr fun n => ?_
        rw [hq_eq n]
        push_cast
        ring
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmain ?_ ?_
      · filter_upwards [hqnn] with n hn
        exact mul_nonneg ENNReal.toReal_nonneg hn
      · filter_upwards [hqnn] with n hn
        refine mul_le_mul_of_nonneg_right ?_ hn
        have hR : 0 ≤ 2 * RR (max n m₀) := by
          have : 0 < RR (max n m₀) := Real.rpow_pos_of_pos
            (by exact_mod_cast (hm₀ _ (le_max_right n m₀)).2.1) _
          positivity
        exact ENNReal.toReal_le_of_le_ofReal hR (hmesh n)
    · filter_upwards [hqnn] with n hn
      refine ⟨hn, ?_⟩
      obtain v := (hne n).some
      have hcell_fin : ((G.tiling n).cell v).volume ≠ ∞ := by
        rw [ConvexPolytope.volume, EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
        exact ((G.tiling n).cell v).compact.measure_lt_top.ne
      have hmin_fin : (G.tiling n).minTileVolume ≠ ∞ :=
        ne_top_of_le_ne_top hcell_fin (iInf_le _ v)
      have hle : ENNReal.ofReal (ρn n ^ d * c₀) ≤ (G.tiling n).minTileVolume := by
        rw [hvol n]
        exact volume_ball_le_minTileVolume (hgood (max n m₀) (le_max_right _ _))
      have hpos : 0 < ρn n ^ d * c₀ := mul_pos (pow_pos (hρnpos n) _) hc₀pos
      rw [hq, neg_neg, Real.exp_log hpos]
      exact (ENNReal.ofReal_le_iff_le_toReal hmin_fin).mp hle

theorem voronoi_tilings_theoremAB_local (hd : 1 ≤ d) {U : Set (Euc d)} (hU : IsDomain U)
    (hUb : Bornology.IsBounded U) {μ : Measure (Euc d)} {βp βm : ℝ} (hβp : 0 < βp)
    (hβm : 0 < βm) {W : Set (Euc d)} (hW : IsOpen W) (hUW : closure U ⊆ W)
    (hμ : HolderMassBounds μ W βp βm)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Λ : ℕ → Ω → Set (Euc d)) (hΛ : ∀ m : ℕ, IsPoissonPointProcess P (fun ω => Λ m ω ∩ W) ((m : ℝ≥0∞) • μ.restrict W))
    (hlf : ∀ m ω (B : Set (EuclideanSpace ℝ (Fin d))), Bornology.IsBounded B → (Λ m ω ∩ B).Finite) :
    ∀ᵐ ω ∂P, ∃ G : TilingSequence d, HasAmbientCollar U G.domain ∧
      (∀ᶠ m in atTop, IsVoronoiTilingOf (G.tiling m) (Λ m ω) G.domain) ∧
      -- Theorem B(a)
      (∀ hC : Euc d → ℝ, HarmonicNearClosure hC U →
        DirichletApproximationTarget G U hC (fun n v => hC ((G.tiling n).pos v))) ∧
      -- Theorem B(b)
      (IsLipschitzDomain U → ∀ hC : Euc d → ℝ, IsHarmonicOn hC U → ContinuousOnClosure hC U →
        Nonempty (NearestClosureBoundaryChoices G U) ∧
        ∀ S : NearestClosureBoundaryChoices G U,
          (∀ n v, S.point n v ∈ frontier U) ∧
          (∀ᶠ n in atTop, ∀ v : (G.tiling n).boundaryVertices U,
            dist ((G.tiling n).pos v) (S.point n v) ≤ 2 * (G.tiling n).mesh.toReal) ∧
          DirichletApproximationTarget G U hC (S.boundaryData hC)) ∧
      -- Theorem A
      (IsLipschitzDomain U → ∀ N : NearestVertexData G,
        ∃ ν : Measure (BrownianPath d),
          IsStandardBrownianLaw ν ∧
          (∀ z ∈ U,
            AEMeasurable (stoppedBrownianCurve U z) ν ∧
            (∀ᵐ ω ∂ν, continuousExitTime U z ω ≠ ∞) ∧
            IsProbabilityMeasure (stoppedBrownianLaw U z ν)) ∧
          ∃ walkLaw : ℕ → Euc d → Measure (CurveSpace d),
            (∀ᶠ n in atTop, ∀ z ∈ U,
              IsStoppedTilingWalkLaw (G.tiling n) U (N.vertex n z) (walkLaw n z)) ∧
            ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ z ∈ U,
              levyProkhorovEDist (walkLaw n z) (stoppedBrownianLaw U z ν) ≤
                ENNReal.ofReal η) := by
  filter_upwards [voronoi_tilings_hypotheses_local hd hU hUb hβp hβm hW hUW hμ P Λ hΛ hlf]
    with ω hω
  obtain ⟨G, hcollar, hvor, ⟨N₀⟩, happrox, hII⟩ := hω
  have hreg : PaperRegularity G := Or.inr (Or.inl hII)
  refine ⟨G, hcollar, hvor, fun hC hh => ?_, fun hL hC hh hc => ?_, fun hL N => ?_⟩
  · exact theoremB_part_a d G N₀ U hC hd hU hUb hcollar (happrox N₀) hreg hh
  · exact theoremB_part_b d G N₀ U hC hd hL hUb hcollar (happrox N₀) hreg hh hc
  · exact theoremA_proved d hd G N U hL hUb hcollar (happrox N) hreg

end SpherePackings
