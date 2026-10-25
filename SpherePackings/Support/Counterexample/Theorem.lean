module

public import SpherePackings.Support.Counterexample.WalkLawExists
public import SpherePackings.Support.Counterexample.Covering
public import SpherePackings.Support.Counterexample.Harmonic
public import SpherePackings.Support.Counterexample.BrownianAsymmetry
public import SpherePackings.Support.LevyProkhorovIntegral
public import BouRabeeGwynne.HarmonicMeasureBridge
public import BouRabeeGwynne.LevyProkhorovMaps

@[expose] public section

/-!
# Theorem 6.1: a sphere packing on which simple random walk is not asymptotically Brownian

`rw-spheres.tex:1791-1872`.  On the packing of `Counterexample.Construction` (dimension `k + 3`),
consider simple random walk started at the origin, with the centres scaled by `1/n`, stopped on
leaving the unit ball.  The function `levelValue / n` is harmonic for the walk and differs by at most
`1/n` from `g(x) = x₀ + min x₀ 0` at the scaled centres; so the mean of `g` at the exit point is at
most `1/n` in absolute value.  For Brownian motion this mean is a fixed negative number
(`integral_ballExitLaw_asymmetry_neg`).  Since `g` is Lipschitz, Lévy–Prokhorov convergence of the
stopped laws would force the two means to agree in the limit.

This replaces the paper's hitting-probability computation (the probability `2/3` of reaching the
right before the left) with the harmonic function behind it, and uses the modified packing of
`Construction.lean` in dimension at least four.
-/

open MeasureTheory Metric Filter Set
open scoped ENNReal Topology BoundedContinuousFunction

namespace SpherePackings.Counterexample

open BouRabeeGwynne

variable {k : ℕ}

/-- The asymmetry test function `g(x) = x₀ + min x₀ 0`. -/
def asym (x : Euc (k + 3)) : ℝ := x 0 + min (x 0) 0

/-- `g` clamped to `[-3, 3]`, as a bounded continuous function. -/
noncomputable def asymB : Euc (k + 3) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => max (-3) (min 3 (asym x)), by unfold asym; fun_prop⟩ 6 fun x y => by
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      rw [abs_le]
      constructor <;>
      · have h1 := le_max_left (-3 : ℝ) (min 3 (asym x))
        have h2 := le_max_left (-3 : ℝ) (min 3 (asym y))
        have h3 : max (-3 : ℝ) (min 3 (asym x)) ≤ 3 := max_le (by norm_num) (min_le_left _ _)
        have h4 : max (-3 : ℝ) (min 3 (asym y)) ≤ 3 := max_le (by norm_num) (min_le_left _ _)
        linarith

lemma asymB_apply (x : Euc (k + 3)) : asymB x = max (-3) (min 3 (asym x)) := rfl

lemma asymB_eq_of_abs_le {x : Euc (k + 3)} (hx : |x 0| ≤ 3 / 2) : asymB x = asym x := by
  rw [asymB_apply, asym]
  rw [abs_le] at hx
  have h1 : -3 ≤ x 0 + min (x 0) 0 := by
    have := min_le_left (x 0) 0
    have := le_min (show -3 / 2 ≤ x 0 by linarith) (show (-3 / 2 : ℝ) ≤ 0 by norm_num)
    linarith
  have h2 : x 0 + min (x 0) 0 ≤ 3 := by
    have := min_le_left (x 0) 0
    linarith
  rw [min_eq_right h2, max_eq_right h1]

lemma abs_asymB_sub_le (x y : Euc (k + 3)) : |asymB x - asymB y| ≤ 2 * dist x y := by
  rw [asymB_apply, asymB_apply]
  have hmax : ∀ a b c : ℝ, |max c a - max c b| ≤ |a - b| := fun a b c => by
    rw [max_comm c a, max_comm c b]; exact abs_max_sub_max_le_abs a b c
  have hmin : ∀ a b c : ℝ, |min c a - min c b| ≤ |a - b| := fun a b c =>
    (abs_min_sub_min_le_max c a c b).trans (by simp)
  have hx : |x 0 - y 0| ≤ dist x y := by
    have := PiLp.dist_apply_le x y 0
    rwa [Real.dist_eq] at this
  have hasym : |asym x - asym y| ≤ 2 * |x 0 - y 0| := by
    unfold asym
    have := abs_min_sub_min_le_max (x 0) 0 (y 0) 0
    rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)] at this
    calc |x 0 + min (x 0) 0 - (y 0 + min (y 0) 0)|
        = |(x 0 - y 0) + (min (x 0) 0 - min (y 0) 0)| := by ring_nf
      _ ≤ |x 0 - y 0| + |min (x 0) 0 - min (y 0) 0| := abs_add_le _ _
      _ ≤ 2 * |x 0 - y 0| := by linarith
  calc _ ≤ |min 3 (asym x) - min 3 (asym y)| := hmax _ _ _
    _ ≤ |asym x - asym y| := hmin _ _ _
    _ ≤ 2 * |x 0 - y 0| := hasym
    _ ≤ 2 * dist x y := by linarith

/-- The scaled harmonic level function is within `1/n` of `g` at the scaled centres. -/
lemma abs_asym_smul_center_sub_le {c : ℝ} (hc : 0 < c) (a : Idx k) :
    |asym (c • center k a) - c * (levelValue k a : ℝ)| ≤ c := by
  have hs7 : 2 ≤ Real.sqrt 7 ∧ Real.sqrt 7 ≤ 3 := by
    constructor
    · rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    · rw [show (3 : ℝ) = Real.sqrt 9 by rw [show (9 : ℝ) = 3 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
  cases a with
  | inl x =>
    have h0 : (c • center k (.inl x)) 0 = c * (2 * (x.1 0 : ℝ)) := by
      simp [center]
    have hle : c * (2 * (x.1 0 : ℝ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hc.le (by have := x.2; exact_mod_cast (by omega : 2 * x.1 0 ≤ 0))
    rw [asym, h0, min_eq_left hle]
    simp only [levelValue, Int.cast_mul, Int.cast_ofNat]
    rw [show c * (2 * (x.1 0 : ℝ)) + c * (2 * (x.1 0 : ℝ)) - c * (4 * (x.1 0 : ℝ)) = 0 by ring,
      abs_zero]
    exact hc.le
  | inr y =>
    have h0 : (c • center k (.inr y)) 0 = c * (Real.sqrt 7 / 2 + (y.1 0 : ℝ)) := by
      simp [center, smallOffset]; ring
    have hy0 : (0 : ℝ) ≤ y.1 0 := by exact_mod_cast y.2.1
    have hge : 0 ≤ c * (Real.sqrt 7 / 2 + (y.1 0 : ℝ)) :=
      mul_nonneg hc.le (by linarith [Real.sqrt_nonneg 7])
    rw [asym, h0, min_eq_right hge]
    simp only [levelValue, Int.cast_add, Int.cast_one]
    rw [show c * (Real.sqrt 7 / 2 + (y.1 0 : ℝ)) + 0 - c * ((y.1 0 : ℝ) + 1) =
      c * (Real.sqrt 7 / 2 - 1) by ring, abs_mul, abs_of_pos hc]
    have : |Real.sqrt 7 / 2 - 1| ≤ 1 := abs_le.mpr ⟨by linarith [hs7.1], by linarith [hs7.2]⟩
    calc c * |Real.sqrt 7 / 2 - 1| ≤ c * 1 := mul_le_mul_of_nonneg_left this hc.le
      _ = c := mul_one c

/-- A neighbour of an interior sphere lies in the closed region. -/
lemma tangent_mem_closedRegion {c ρ : ℝ} {a b : (packing k).ι}
    (ha : a ∈ (packing k).interiorSpheres c (ball 0 ρ)) (hab : (packing k).Tangent a b) :
    b ∈ (packing k).closedRegion c (ball 0 ρ) := by
  by_cases hb : b ∈ (packing k).interiorSpheres c (ball 0 ρ)
  · exact Or.inl hb
  · exact Or.inr ⟨hb, a, ha, hab⟩

lemma radius_add_le_two (a b : (packing k).ι) : (packing k).radius a + (packing k).radius b ≤ 2 := by
  change radius k a + radius k b ≤ 2
  rcases a with x | y <;> rcases b with x' | y' <;> norm_num [radius]

/-- Scaled centres of the closed region and the origin lie within `1 + 2c` of the origin. -/
lemma norm_smul_center_le {c : ℝ} (hc : 0 < c) {a : (packing k).ι}
    (ha : a ∈ (packing k).closedRegion c (ball 0 1) ∪ {(origin k : (packing k).ι)}) :
    ‖c • (packing k).center a‖ ≤ 1 + 2 * c := by
  rcases ha with (ha | ⟨-, i, hi, hia⟩) | ha
  · exact (mem_ball_zero_iff.mp ha).le.trans (by linarith)
  · have hdist : dist ((packing k).center i) ((packing k).center a) ≤ 2 := by
      rw [hia.2]
      exact radius_add_le_two i a
    have hi' : ‖c • (packing k).center i‖ < 1 := mem_ball_zero_iff.mp hi
    have hsm : ‖c • (packing k).center a - c • (packing k).center i‖ =
        c * dist ((packing k).center i) ((packing k).center a) := by
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hc, dist_comm, dist_eq_norm]
    calc ‖c • (packing k).center a‖
        ≤ ‖c • (packing k).center i‖ + ‖c • (packing k).center a - c • (packing k).center i‖ :=
          norm_le_insert' _ _
      _ ≤ 1 + 2 * c := by rw [hsm]; nlinarith
  · obtain rfl : a = origin k := ha
    have : (packing k).center (origin k) = 0 := by
      change center k (origin k) = 0
      ext j; simp [center, origin]
    rw [this, smul_zero, norm_zero]
    positivity

/-- **The walk side.** For `n ≥ 4`, the mean of the test function at the exit point of the scaled
simple random walk is at most `1/n` in absolute value. -/
theorem abs_integral_walk_endPoint_le {n : ℕ} (hn : 4 ≤ n) {ν : Measure (CurveSpace (k + 3))}
    (hν : (packing k).IsStoppedSRWLaw ((n : ℝ)⁻¹) (ball 0 1) (origin k) ν) :
    |∫ x, asymB x ∂(ν.map CurveSpace.endPoint)| ≤ (n : ℝ)⁻¹ := by
  classical
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  set c : ℝ := (n : ℝ)⁻¹ with hcdef
  have hc : 0 < c := inv_pos.mpr hnpos
  have hc4 : c ≤ 1 / 4 := by
    rw [hcdef, one_div]
    exact inv_anti₀ (by norm_num) (by exact_mod_cast hn)
  obtain ⟨R, hR, h⟩ := hν
  let _ : MeasurableSpace R := ⊤
  obtain ⟨hpos, start, hstart, -, -, -, hνeq⟩ := h
  set N := (packing k).unitNetwork (R : Set (packing k).ι) with hN
  set A : Set R := {v | c • (packing k).center v.val ∈ ball 0 1} with hA
  have hsub : (packing k).closedRegion c (ball 0 1) ⊆ (R : Set (packing k).ι) := by
    rw [hR]; exact subset_union_left
  have haccess : N.BoundaryAccessible A := boundaryAccessible_unitNetwork hc 1 R hsub
  set HM := N.discreteHarmonicMeasure A hpos start with hHM
  have hend : ν.map CurveSpace.endPoint =
      HM.map fun v : R => c • (packing k).center v.val := by
    rw [hνeq]
    exact N.stoppedPolygonalCurve_map_endPoint _ A hpos start
  rw [hend, integral_map (measurable_of_finite _).aemeasurable
    asymB.continuous.aestronglyMeasurable]
  -- The harmonic level function.
  set f : ↥(R : Set (packing k).ι) → ℝ := fun v => c * (levelValue k v.val : ℝ) with hf
  have hlap : ∀ v ∈ A, N.laplacian f v = 0 := by
    intro v hv
    have hvint : v.val ∈ (packing k).interiorSpheres c (ball 0 1) := hv
    have hnbr : ∀ b ∈ (nbrs_finite v.val).toFinset, b ∈ R := fun b hb => by
      have hb' : (packing k).Tangent v.val b := (Set.Finite.mem_toFinset (nbrs_finite v.val)).mp hb
      exact hsub (tangent_mem_closedRegion hvint hb')
    have hsum : N.laplacian f v = ∑ b ∈ (nbrs_finite v.val).toFinset,
        (c * (levelValue k b : ℝ) - c * (levelValue k v.val : ℝ)) := by
      unfold FiniteConductanceNetwork.laplacian
      rw [← Finset.sum_filter_add_sum_filter_not _
        (fun w => (packing k).Tangent v.val w.val)]
      have hzero : ∑ w ∈ Finset.univ.filter
          (fun w : (R : Set (packing k).ι) => ¬ (packing k).Tangent v.val w.val),
          N.a v w * (f w - f v) = 0 := by
        refine Finset.sum_eq_zero fun w hw => ?_
        rw [Finset.mem_filter] at hw
        simp [hN, SpherePacking.unitNetwork, hw.2]
      rw [hzero, add_zero]
      refine Finset.sum_nbij' (fun w => w.val)
        (fun b => if hb : b ∈ R then ⟨b, hb⟩ else start) ?_ ?_ ?_ ?_ ?_
      · intro w hw
        rw [Finset.mem_filter] at hw
        exact (Set.Finite.mem_toFinset _).mpr hw.2
      · intro b hb
        rw [Finset.mem_filter]
        simp only [dite_eq_left (hnbr b hb)]
        exact ⟨Finset.mem_univ _, (Set.Finite.mem_toFinset (nbrs_finite (v.val : Idx k))).mp hb⟩
      · intro w _
        simp
      · intro b hb
        simp [dite_eq_left (hnbr b hb)]
      · intro w hw
        rw [Finset.mem_filter] at hw
        simp [hN, SpherePacking.unitNetwork, hw.2, hf]
    rw [hsum]
    simp_rw [← mul_sub]
    rw [← Finset.mul_sum]
    have := sum_levelValue_sub_eq_zero (v.val : Idx k)
    have hcast : ∑ b ∈ (nbrs_finite v.val).toFinset,
        ((levelValue k b : ℝ) - (levelValue k v.val : ℝ)) = 0 := by
      exact_mod_cast this
    rw [hcast, mul_zero]
  have hsol : N.SolvesDirichlet A f f := ⟨hlap, fun _ _ => rfl⟩
  have hmean := N.integral_discreteHarmonicMeasure_of_solvesDirichlet A hpos haccess hsol start
  have hf0 : f start = 0 := by
    simp only [hf, hstart, origin, levelValue, Int.cast_mul]
    simp
  rw [hf0] at hmean
  -- Pointwise comparison of `asymB` with the harmonic function.
  have hpt : ∀ v : (R : Set (packing k).ι), |asymB (c • (packing k).center v.val) - f v| ≤ c := by
    intro v
    have hvR : (v.val : (packing k).ι) ∈
        (packing k).closedRegion c (ball 0 1) ∪ {(origin k : (packing k).ι)} :=
      (Set.ext_iff.mp hR v.val).mp v.2
    have hnorm := norm_smul_center_le hc hvR
    have h0 : |(c • (packing k).center v.val) 0| ≤ 3 / 2 := by
      have := PiLp.norm_apply_le (c • (packing k).center v.val) 0
      rw [Real.norm_eq_abs] at this
      linarith
    rw [asymB_eq_of_abs_le h0]
    exact abs_asym_smul_center_sub_le hc v.val
  have hint : ∫ v, asymB (c • (packing k).center v.val) ∂HM =
      ∫ v, (asymB (c • (packing k).center v.val) - f v) ∂HM + ∫ v, f v ∂HM := by
    rw [← integral_add Integrable.of_finite Integrable.of_finite]
    congr 1; ext v; ring
  show |∫ v, asymB (c • (packing k).center v.val) ∂HM| ≤ c
  rw [hint, hmean, add_zero]
  have := norm_integral_le_of_norm_le_const (μ := HM)
    (ae_of_all _ fun v => (Real.norm_eq_abs _).trans_le (hpt v))
  rw [probReal_univ, mul_one] at this
  exact this

/-- **The asymmetry.** The Brownian exit mean of the test function is negative. -/
lemma integral_asymB_ballExitLaw_neg {μ : Measure (BrownianPath (k + 3))}
    (hμ : IsStandardBrownianLaw μ) : ∫ x, asymB x ∂ballExitLaw μ < 0 := by
  have h := integral_ballExitLaw_asymmetry_neg (by omega : 1 ≤ k + 3) hμ
  have heq : (fun x : Euc (k + 3) => asymB x) =ᵐ[ballExitLaw μ]
      fun x => x ⟨0, by omega⟩ + min (x ⟨0, by omega⟩) 0 := by
    filter_upwards [ballExitLaw_ae_norm (by omega : 1 ≤ k + 3) hμ] with x hx
    have h0 : |x 0| ≤ 3 / 2 := by
      have := PiLp.norm_apply_le x 0
      rw [Real.norm_eq_abs, hx] at this
      linarith
    rw [asymB_eq_of_abs_le h0]
    rfl
  rw [integral_congr_ae heq]
  exact h

/-- **Non-convergence.** The stopped scaled walks do not converge to stopped Brownian motion in the
Lévy–Prokhorov distance for curves modulo time parametrization. -/
theorem not_tendsto_levyProkhorov {μ : Measure (BrownianPath (k + 3))}
    (hμ : IsStandardBrownianLaw μ) (walkLaw : ℕ → Measure (CurveSpace (k + 3)))
    (hwalk : ∀ᶠ n : ℕ in atTop,
      (packing k).IsStoppedSRWLaw ((n : ℝ)⁻¹) (ball 0 1) (origin k) (walkLaw n)) :
    ¬ Tendsto (fun n => levyProkhorovEDist (walkLaw n) (stoppedBrownianLaw (ball 0 1) 0 μ))
      atTop (𝓝 0) := by
  intro hlim
  have : IsProbabilityMeasure μ := hμ.1
  have hBM := stoppedBrownianLaw_isProbabilityMeasure (isOpen_ball : IsOpen (ball (0 : Euc (k + 3)) 1)) 0 μ
  set J := ∫ x, asymB x ∂ballExitLaw μ with hJ
  have hJneg : J < 0 := integral_asymB_ballExitLaw_neg hμ
  set ε : ℝ := -J / (8 * (1 + ‖(asymB : Euc (k + 3) →ᵇ ℝ)‖)) with hε
  have hεpos : 0 < ε := div_pos (by linarith) (by positivity)
  have hev : ∀ᶠ n in atTop, levyProkhorovEDist (walkLaw n) (stoppedBrownianLaw (ball 0 1) 0 μ) <
      ENNReal.ofReal ε := (tendsto_order.1 hlim).2 _ (ENNReal.ofReal_pos.mpr hεpos)
  have hsmall : ∀ᶠ n : ℕ in atTop, (n : ℝ)⁻¹ < -J / 4 :=
    (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).eventually
      (gt_mem_nhds (by linarith))
  obtain ⟨n, hn⟩ := (hwalk.and (hev.and (hsmall.and (eventually_ge_atTop 4)))).exists
  obtain ⟨hwn, hlp, hninv, hn4⟩ := hn
  have hνprob : IsProbabilityMeasure (walkLaw n) := by
    obtain ⟨R, hR, h⟩ := hwn
    let _ : MeasurableSpace R := ⊤
    obtain ⟨-, -, -, -, -, hprob, -⟩ := h
    exact hprob
  have hνend : IsProbabilityMeasure ((walkLaw n).map CurveSpace.endPoint) :=
    (Measure.isProbabilityMeasure_map_iff
      CurveSpace.continuous_endPoint.measurable.aemeasurable).mpr hνprob
  have hρ := ballExitLaw_isProbabilityMeasure hμ
  have hlp' : levyProkhorovEDist ((walkLaw n).map CurveSpace.endPoint) (ballExitLaw μ) <
      ENNReal.ofReal ε := (levyProkhorovEDist_endpoint_map_le _ _).trans_lt hlp
  have hcomp := SpherePackings.abs_integral_sub_integral_le_of_levyProkhorovEDist_lt _ _ hεpos
    (δ := 2 * ε) hlp' asymB (fun x y hxy => (abs_asymB_sub_le x y).trans (by linarith))
  have hwalkb := abs_integral_walk_endPoint_le hn4 hwn
  have hnorm : 0 ≤ ‖(asymB : Euc (k + 3) →ᵇ ℝ)‖ := norm_nonneg _
  have hbound : 2 * ε + 2 * ε * ‖(asymB : Euc (k + 3) →ᵇ ℝ)‖ = -J / 4 := by
    rw [hε]; field_simp; ring
  have := abs_sub_abs_le_abs_sub (∫ x, asymB x ∂ballExitLaw μ)
    (∫ x, asymB x ∂((walkLaw n).map CurveSpace.endPoint))
  rw [abs_sub_comm] at this
  have hJabs : |J| = -J := abs_of_neg hJneg
  rw [← hJ, hJabs] at this
  linarith

end SpherePackings.Counterexample

namespace SpherePackings

open BouRabeeGwynne Counterexample

/-- **Theorem 6.1** (`theorem:counter-example`).  For every `d ≥ 3` there is a packing of `ℝ^d` by
spheres of radii `1` and `1/2`, each tangent to a bounded number of others, and in dimension three
with every sphere covered, on which simple random walk does not converge to Brownian motion modulo time parametrization in the scaling limit: the
walks started at the centre `0`, with positions scaled by `1/n` and stopped on leaving the unit
ball, exist, and their laws do not converge to the law of Brownian motion from `0` stopped on
leaving the unit ball, in the Lévy–Prokhorov distance for curves modulo time parametrization.  In
dimension at least four the packing used does not cover `ℝ^d`. -/
theorem simpleRandomWalk_counterexample (d : ℕ) (hd : 3 ≤ d) :
    ∃ P : SpherePacking d,
      (∀ i, P.radius i = 1 ∨ P.radius i = 1 / 2) ∧
      (∃ D : ℕ, ∀ i, {j | P.Tangent i j}.Finite ∧ {j | P.Tangent i j}.ncard ≤ D) ∧
      (d = 3 → ∀ i, P.Covered i) ∧
      ∃ i₀ : P.ι, P.center i₀ = 0 ∧
        (∃ walkLaw : ℕ → Measure (CurveSpace d), ∀ n : ℕ, 1 ≤ n →
          P.IsStoppedSRWLaw ((n : ℝ)⁻¹) (ball 0 1) i₀ (walkLaw n)) ∧
        ∀ μ : Measure (BrownianPath d), IsStandardBrownianLaw μ →
        ∀ walkLaw : ℕ → Measure (CurveSpace d),
          (∀ᶠ n : ℕ in atTop, P.IsStoppedSRWLaw ((n : ℝ)⁻¹) (ball 0 1) i₀ (walkLaw n)) →
          ¬ Tendsto (fun n => levyProkhorovEDist (walkLaw n) (stoppedBrownianLaw (ball 0 1) 0 μ))
            atTop (𝓝 0) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 3 := ⟨d - 3, by omega⟩
  refine ⟨packing k, fun i => ?_, ⟨2 * (k + 3) + 4, fun i => ⟨nbrs_finite i, ncard_nbrs_le i⟩⟩,
    fun h3 => ?_, origin k, ?_, ?_, fun μ hμ walkLaw hwalk => not_tendsto_levyProkhorov hμ walkLaw hwalk⟩
  · change radius k i = 1 ∨ radius k i = 1 / 2
    rcases i with x | y
    · exact Or.inl rfl
    · exact Or.inr rfl
  · obtain rfl : k = 0 := by omega
    exact packing_covered
  · change Counterexample.center k (origin k) = 0
    ext j; simp [Counterexample.center, origin]
  · classical
    refine ⟨fun n => if h : 1 ≤ n then
      (exists_isStoppedSRWLaw (k := k) (inv_pos.mpr (by exact_mod_cast h : (0 : ℝ) < n)) 1).choose
      else 0, fun n hn => ?_⟩
    simp only [hn, dite_true]
    exact (exists_isStoppedSRWLaw (k := k) (inv_pos.mpr (by exact_mod_cast hn : (0 : ℝ) < n))
      1).choose_spec

end SpherePackings
