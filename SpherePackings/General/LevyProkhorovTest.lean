module

-- Built on Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne (commit cf73d6e).
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.MetricSpace.Thickening

@[expose] public section

/-!
# The Lévy–Prokhorov distance from finitely many test functions

For a compact set `S` of a metric space and `ρ > 0` there are finitely many continuous functions
with values in `[0, 1]` such that, for finite measures `μ`, `ν` with `μ` concentrated on `S`, if all
their integrals against `μ` and `ν` are within `θ`, then the Lévy–Prokhorov distance of `μ` and `ν`
is at most `2 ρ + 2 θ`.  The functions are a cutoff at distance `ρ/2` from `S` and the truncated
sums of tents over the subsets of a `ρ/4`-net of `S`.  Nothing here depends on the paper.
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace SpherePackings

section Tents

variable {E : Type*} [PseudoMetricSpace E]

/-- The tent of height one and radius `ρ` at `y`. -/
noncomputable def tent (y : E) (ρ : ℝ) (x : E) : ℝ := max 0 (1 - dist x y / ρ)

lemma continuous_tent (y : E) (ρ : ℝ) : Continuous (tent y ρ) :=
  continuous_const.max (continuous_const.sub ((continuous_id.dist continuous_const).div_const ρ))

lemma tent_nonneg (y : E) (ρ : ℝ) (x : E) : 0 ≤ tent y ρ x := le_max_left _ _

lemma tent_eq_zero_of_le {y x : E} {ρ : ℝ} (hρ : 0 < ρ) (h : ρ ≤ dist x y) : tent y ρ x = 0 := by
  have : 1 - dist x y / ρ ≤ 0 := by
    rw [sub_nonpos, le_div_iff₀ hρ, one_mul]
    exact h
  exact max_eq_left this

lemma quarter_le_tent {y x : E} {ρ : ℝ} (hρ : 0 < ρ) (h : dist x y < 3 * ρ / 4) :
    1 / 4 ≤ tent y ρ x := by
  have : 1 / 4 ≤ 1 - dist x y / ρ := by
    have h' : dist x y / ρ < 3 / 4 := by
      rw [div_lt_iff₀ hρ]
      linarith
    linarith
  exact this.trans (le_max_right _ _)

/-- The truncated sum of four times the tents at the points of `I`. -/
noncomputable def tentSum (I : Finset E) (ρ : ℝ) (x : E) : ℝ :=
  min 1 (4 * ∑ y ∈ I, tent y ρ x)

lemma continuous_tentSum (I : Finset E) (ρ : ℝ) : Continuous (tentSum I ρ) :=
  continuous_const.min (continuous_const.mul (continuous_finsetSum _ fun y _ => continuous_tent y ρ))

lemma tentSum_nonneg (I : Finset E) (ρ : ℝ) (x : E) : 0 ≤ tentSum I ρ x :=
  le_min zero_le_one (mul_nonneg (by norm_num) (Finset.sum_nonneg fun y _ => tent_nonneg y ρ x))

lemma tentSum_le_one (I : Finset E) (ρ : ℝ) (x : E) : tentSum I ρ x ≤ 1 := min_le_left _ _

lemma tentSum_eq_one {I : Finset E} {ρ : ℝ} (hρ : 0 < ρ) {x y : E} (hy : y ∈ I)
    (h : dist x y < 3 * ρ / 4) : tentSum I ρ x = 1 := by
  apply min_eq_left
  have h1 := quarter_le_tent hρ h
  have h2 : tent y ρ x ≤ ∑ z ∈ I, tent z ρ x :=
    Finset.single_le_sum (fun z _ => tent_nonneg z ρ x) hy
  linarith

/-- Where the tent sum is positive, some tent is positive. -/
lemma exists_mem_dist_lt_of_tentSum_pos {I : Finset E} {ρ : ℝ} (hρ : 0 < ρ) {x : E}
    (h : 0 < tentSum I ρ x) : ∃ y ∈ I, dist x y < ρ := by
  by_contra hne
  simp only [not_exists, not_and, not_lt] at hne
  have : ∑ y ∈ I, tent y ρ x = 0 :=
    Finset.sum_eq_zero fun y hy => tent_eq_zero_of_le hρ (hne y hy)
  have h0 : tentSum I ρ x = 0 := by
    simp only [tentSum, this, mul_zero]
    exact min_eq_right zero_le_one
  linarith

/-- The cutoff at distance `ρ / 2` from `S`. -/
noncomputable def farCutoff (S : Set E) (ρ : ℝ) (x : E) : ℝ := min 1 (infDist x S / (ρ / 2))

lemma continuous_farCutoff (S : Set E) (ρ : ℝ) : Continuous (farCutoff S ρ) :=
  continuous_const.min ((continuous_infDist_pt S).div_const _)

lemma farCutoff_nonneg (S : Set E) {ρ : ℝ} (hρ : 0 < ρ) (x : E) : 0 ≤ farCutoff S ρ x :=
  le_min zero_le_one (div_nonneg infDist_nonneg (by linarith))

lemma farCutoff_le_one (S : Set E) (ρ : ℝ) (x : E) : farCutoff S ρ x ≤ 1 := min_le_left _ _

lemma farCutoff_eq_zero {S : Set E} {ρ : ℝ} {x : E} (hx : x ∈ S) : farCutoff S ρ x = 0 := by
  simp [farCutoff, infDist_zero_of_mem hx]

lemma farCutoff_eq_one {S : Set E} (hS : S.Nonempty) {ρ : ℝ} (hρ : 0 < ρ) {x : E}
    (hx : x ∉ thickening (ρ / 2) S) : farCutoff S ρ x = 1 := by
  apply min_eq_left
  rw [le_div_iff₀ (by linarith), one_mul]
  rw [mem_thickening_iff_infDist_lt hS] at hx
  exact not_lt.mp hx

end Tents

variable {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]

lemma integrable_of_continuous_bounded {μ : Measure E} [IsFiniteMeasure μ] {g : E → ℝ}
    (hg : Continuous g) (h0 : ∀ x, 0 ≤ g x) (h1 : ∀ x, g x ≤ 1) : Integrable g μ :=
  (integrable_const (1 : ℝ)).mono' hg.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]; exact h1 x)

/-- `μ.real A ≤ ∫ g dμ` when `g ≥ 0` and `g = 1` on `A`. -/
lemma measureReal_le_integral {μ : Measure E} [IsFiniteMeasure μ] {A : Set E}
    (hA : MeasurableSet A) {g : E → ℝ} (hg : Continuous g) (h0 : ∀ x, 0 ≤ g x)
    (h1 : ∀ x, g x ≤ 1) (hone : ∀ x ∈ A, g x = 1) : μ.real A ≤ ∫ x, g x ∂μ := by
  rw [← integral_indicator_one hA]
  apply integral_mono ((integrable_const (1 : ℝ)).indicator hA)
    (integrable_of_continuous_bounded hg h0 h1)
  intro x
  by_cases hx : x ∈ A
  · simp [Set.indicator_of_mem hx, hone x hx]
  · simp [Set.indicator_of_notMem hx, h0 x]

/-- `∫ g dμ ≤ μ.real A` when `0 ≤ g ≤ 1` and `g = 0` off `A`. -/
lemma integral_le_measureReal {μ : Measure E} [IsFiniteMeasure μ] {A : Set E}
    (hA : MeasurableSet A) {g : E → ℝ} (hg : Continuous g) (h0 : ∀ x, 0 ≤ g x)
    (h1 : ∀ x, g x ≤ 1) (hzero : ∀ x, x ∉ A → g x = 0) : ∫ x, g x ∂μ ≤ μ.real A := by
  rw [← integral_indicator_one hA]
  apply integral_mono (integrable_of_continuous_bounded hg h0 h1)
    ((integrable_const (1 : ℝ)).indicator hA)
  intro x
  by_cases hx : x ∈ A
  · simp [Set.indicator_of_mem hx, h1 x]
  · simp [Set.indicator_of_notMem hx, hzero x hx]

/-- **Finitely many test functions control the Lévy–Prokhorov distance** to measures concentrated
on a nonempty compact set. -/
theorem exists_test_family_levyProkhorov {S : Set E} (hS : IsCompact S) (hSne : S.Nonempty)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ (ι : Type) (_ : Fintype ι) (g : ι → E → ℝ), (∀ i, Continuous (g i)) ∧
      (∀ i x, 0 ≤ g i x ∧ g i x ≤ 1) ∧
      ∀ (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν] {θ : ℝ}, 0 ≤ θ → μ Sᶜ = 0 →
        (∀ i, |∫ x, g i x ∂ν - ∫ x, g i x ∂μ| ≤ θ) →
        levyProkhorovEDist μ ν ≤ ENNReal.ofReal (2 * ρ + 2 * θ) := by
  classical
  obtain ⟨t, -, htfin, hcover⟩ := hS.finite_cover_balls (e := ρ / 4) (by positivity)
  let T : Finset E := htfin.toFinset
  let pt : Fin T.card → E := fun k => (T.equivFin.symm k : E)
  have hnet : ∀ s ∈ S, ∃ k, dist s (pt k) < ρ / 4 := by
    intro s hs
    obtain ⟨y, hy, hsy⟩ := mem_iUnion₂.mp (hcover hs)
    refine ⟨T.equivFin ⟨y, htfin.mem_toFinset.mpr hy⟩, ?_⟩
    simpa [pt] using mem_ball.mp hsy
  let g : Option (Finset (Fin T.card)) → E → ℝ := fun
    | none => farCutoff S ρ
    | some I => tentSum (I.image pt) ρ
  have hcont : ∀ i, Continuous (g i) := by
    rintro (_ | I)
    · exact continuous_farCutoff S ρ
    · exact continuous_tentSum _ ρ
  have hbound : ∀ i x, 0 ≤ g i x ∧ g i x ≤ 1 := by
    rintro (_ | I) x
    · exact ⟨farCutoff_nonneg S hρ x, farCutoff_le_one S ρ x⟩
    · exact ⟨tentSum_nonneg _ ρ x, tentSum_le_one _ ρ x⟩
  refine ⟨Option (Finset (Fin T.card)), inferInstance, g, hcont, hbound, ?_⟩
  intro μ ν _ _ θ hθ hμS htest
  -- the net points within `3ρ/4` of a set
  let idx (B : Set E) : Finset (Fin T.card) :=
    Finset.univ.filter (fun k => infDist (pt k) B ≤ 3 * ρ / 4)
  have hone : ∀ (B : Set E), ∀ x ∈ B ∩ thickening (ρ / 2) S, g (some (idx B)) x = 1 := by
    rintro B x ⟨hxB, hxS⟩
    obtain ⟨s, hs, hxs⟩ := (infDist_lt_iff hSne).mp ((mem_thickening_iff_infDist_lt hSne).mp hxS)
    obtain ⟨k, hk⟩ := hnet s hs
    have hxk : dist x (pt k) < 3 * ρ / 4 := by
      linarith [dist_triangle x s (pt k)]
    have hkB : k ∈ idx B := by
      simp only [idx, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (infDist_le_dist_of_mem hxB).trans (by rw [dist_comm]; exact hxk.le)
    exact tentSum_eq_one hρ (Finset.mem_image_of_mem pt hkB) hxk
  have hzero : ∀ (B : Set E), B.Nonempty → ∀ x, x ∉ thickening (2 * ρ) B →
      g (some (idx B)) x = 0 := by
    intro B hB x hx
    by_contra hne
    have hpos : 0 < g (some (idx B)) x := lt_of_le_of_ne (hbound (some (idx B)) x).1 (Ne.symm hne)
    obtain ⟨y, hy, hxy⟩ := exists_mem_dist_lt_of_tentSum_pos hρ hpos
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
    simp only [idx, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    apply hx
    rw [mem_thickening_iff_infDist_lt hB]
    linarith [infDist_le_infDist_add_dist (x := x) (y := pt k) (s := B)]
  have hint : ∀ i, Integrable (g i) μ := fun i =>
    integrable_of_continuous_bounded (hcont i) (fun x => (hbound i x).1) (fun x => (hbound i x).2)
  -- the cutoff has zero integral against `μ`
  have hfar0 : ∫ x, g none x ∂μ = 0 := by
    apply integral_eq_zero_of_ae
    have hae : ∀ᵐ x ∂μ, x ∈ S := by
      rw [ae_iff]
      simpa [Set.compl_def] using hμS
    filter_upwards [hae] with x hx
    exact farCutoff_eq_zero hx
  have hmeasS : MeasurableSet (thickening (ρ / 2) S) := isOpen_thickening.measurableSet
  -- the two real inequalities
  have hgap : ∀ B : Set E,
      ∫ x, g (some (idx B)) x ∂μ ≤ ∫ x, g (some (idx B)) x ∂ν + θ ∧
        ∫ x, g (some (idx B)) x ∂ν ≤ ∫ x, g (some (idx B)) x ∂μ + θ := by
    intro B
    have h := abs_le.mp (htest (some (idx B)))
    constructor <;> linarith [h.1, h.2]
  have ha : ∀ B : Set E, MeasurableSet B → B.Nonempty →
      μ.real B ≤ ν.real (thickening (2 * ρ) B) + θ := by
    intro B hB hBne
    have hsub : B \ thickening (ρ / 2) S ⊆ Sᶜ := fun x hx hxS =>
      hx.2 (self_subset_thickening (by positivity) S hxS)
    have hnull : μ (B \ thickening (ρ / 2) S) = 0 := measure_mono_null hsub hμS
    have h1 : μ.real B = μ.real (B ∩ thickening (ρ / 2) S) := by
      have h := measure_inter_add_sdiff B hmeasS (μ := μ)
      rw [hnull, add_zero] at h
      rw [measureReal_def, measureReal_def, h]
    calc μ.real B = μ.real (B ∩ thickening (ρ / 2) S) := h1
      _ ≤ ∫ x, g (some (idx B)) x ∂μ :=
          measureReal_le_integral (hB.inter hmeasS) (hcont (some (idx B))) (fun x => (hbound (some (idx B)) x).1)
            (fun x => (hbound (some (idx B)) x).2) (hone B)
      _ ≤ ∫ x, g (some (idx B)) x ∂ν + θ := (hgap B).1
      _ ≤ ν.real (thickening (2 * ρ) B) + θ := by
          gcongr
          exact integral_le_measureReal isOpen_thickening.measurableSet (hcont (some (idx B)))
            (fun x => (hbound (some (idx B)) x).1) (fun x => (hbound (some (idx B)) x).2) (hzero B hBne)
  have hb : ∀ B : Set E, MeasurableSet B → B.Nonempty →
      ν.real B ≤ μ.real (thickening (2 * ρ) B) + 2 * θ := by
    intro B hB hBne
    have h1 : ν.real B ≤ ν.real (B ∩ thickening (ρ / 2) S) + ν.real (thickening (ρ / 2) S)ᶜ := by
      rw [← measureReal_inter_add_sdiff (s := B) (μ := ν) hmeasS]
      have : ν.real (B \ thickening (ρ / 2) S) ≤ ν.real (thickening (ρ / 2) S)ᶜ :=
        measureReal_mono (fun x hx => hx.2)
      linarith
    have h2 : ν.real (thickening (ρ / 2) S)ᶜ ≤ θ := by
      calc ν.real (thickening (ρ / 2) S)ᶜ ≤ ∫ x, g none x ∂ν :=
            measureReal_le_integral hmeasS.compl (hcont none) (fun x => (hbound none x).1)
              (fun x => (hbound none x).2) (fun x hx => farCutoff_eq_one hSne hρ hx)
        _ ≤ ∫ x, g none x ∂μ + θ := by
            have h := abs_le.mp (htest none)
            linarith [h.2]
        _ = θ := by rw [hfar0, zero_add]
    have h3 : ν.real (B ∩ thickening (ρ / 2) S) ≤ μ.real (thickening (2 * ρ) B) + θ := by
      calc ν.real (B ∩ thickening (ρ / 2) S) ≤ ∫ x, g (some (idx B)) x ∂ν :=
            measureReal_le_integral (hB.inter hmeasS) (hcont (some (idx B))) (fun x => (hbound (some (idx B)) x).1)
              (fun x => (hbound (some (idx B)) x).2) (hone B)
        _ ≤ ∫ x, g (some (idx B)) x ∂μ + θ := (hgap B).2
        _ ≤ μ.real (thickening (2 * ρ) B) + θ := by
            gcongr
            exact integral_le_measureReal isOpen_thickening.measurableSet (hcont (some (idx B)))
              (fun x => (hbound (some (idx B)) x).1) (fun x => (hbound (some (idx B)) x).2) (hzero B hBne)
    linarith
  -- conversion to the Lévy–Prokhorov distance
  apply levyProkhorovEDist_le_of_forall
  intro ε B hε hεtop hB
  rcases B.eq_empty_or_nonempty with rfl | hBne
  · simp
  have hεr : 2 * ρ + 2 * θ < ε.toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hεtop.ne).mp hε
  have hthick : thickening (2 * ρ) B ⊆ thickening ε.toReal B :=
    thickening_mono (by linarith) B
  have hθε : ENNReal.ofReal (2 * θ) ≤ ε :=
    (ENNReal.ofReal_le_ofReal (by linarith)).trans hε.le
  have hθε' : ENNReal.ofReal θ ≤ ε :=
    (ENNReal.ofReal_le_ofReal (by linarith)).trans hθε
  constructor
  · calc μ B = ENNReal.ofReal (μ.real B) := (ofReal_measureReal (measure_ne_top μ B)).symm
      _ ≤ ENNReal.ofReal (ν.real (thickening (2 * ρ) B) + θ) :=
          ENNReal.ofReal_le_ofReal (ha B hB hBne)
      _ = ν (thickening (2 * ρ) B) + ENNReal.ofReal θ := by
          rw [ENNReal.ofReal_add measureReal_nonneg hθ, ofReal_measureReal (measure_ne_top _ _)]
      _ ≤ ν (thickening ε.toReal B) + ε := add_le_add (measure_mono hthick) hθε'
  · calc ν B = ENNReal.ofReal (ν.real B) := (ofReal_measureReal (measure_ne_top ν B)).symm
      _ ≤ ENNReal.ofReal (μ.real (thickening (2 * ρ) B) + 2 * θ) :=
          ENNReal.ofReal_le_ofReal (hb B hB hBne)
      _ = μ (thickening (2 * ρ) B) + ENNReal.ofReal (2 * θ) := by
          rw [ENNReal.ofReal_add measureReal_nonneg (by linarith),
            ofReal_measureReal (measure_ne_top _ _)]
      _ ≤ μ (thickening ε.toReal B) + ε := add_le_add (measure_mono hthick) hθε

end SpherePackings
