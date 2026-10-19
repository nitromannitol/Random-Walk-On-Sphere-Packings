import SpherePackings.Support.Voronoi.PoissonTilings
import SpherePackings.Support.Guards.LatticeVoronoi

/-!
# The hypotheses of Theorems A and B are satisfiable

The Voronoi tilings of the lattices `(n+1)⁻¹ ℤ^d`, restricted to the ball of radius `2`, form a
sequence of orthogonal tilings with the ambient collar for the unit ball, the approximation
condition (1.3) for every choice of nearest vertices, and hypothesis (II).
-/

open MeasureTheory Metric Filter Set
open scoped ENNReal Topology

namespace SpherePackings

open BouRabeeGwynne Voronoi

/-- The volume `√π ^ d / Γ(d/2 + 1)` of the Euclidean unit ball in `ℝ^d`. -/
private noncomputable def unitBallVolume (d : ℕ) : ℝ :=
  Real.sqrt Real.pi ^ d / Real.Gamma ((d : ℝ) / 2 + 1)

private lemma unitBallVolume_pos (d : ℕ) : 0 < unitBallVolume d :=
  div_pos (pow_pos (Real.sqrt_pos.mpr Real.pi_pos) _)
    (Real.Gamma_pos_of_pos (by positivity))

/-- The ball of radius `ρ ≥ 0` has volume `ρ ^ d` times that of the unit ball. -/
private lemma volume_ball_eq_ofReal {d : ℕ} (hd : 0 < d) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    volume (ball (0 : Euc d) ρ) = ENNReal.ofReal (ρ ^ d * unitBallVolume d) := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  rw [unitBallVolume, EuclideanSpace.volume_ball, Fintype.card_fin, ← ENNReal.ofReal_pow hρ,
    ← ENNReal.ofReal_mul (pow_nonneg hρ _)]

/-- The logarithm of `(1 / x / 2) ^ d * c` in terms of `log x` and `log c`. -/
private lemma neg_log_volume (d : ℕ) {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    -Real.log ((1 / x / 2) ^ d * c) = d * Real.log x + (d * Real.log 2 - Real.log c) := by
  have hy : 0 < 1 / x / 2 := div_pos (div_pos one_pos hx) two_pos
  rw [Real.log_mul (pow_pos hy d).ne' hc.ne', Real.log_pow, one_div,
    Real.log_div (inv_ne_zero hx.ne') two_ne_zero, Real.log_inv]
  ring

/-- **Hypotheses of Theorems A and B for lattices.** The Voronoi tilings of `(n+1)⁻¹ ℤ^d` on the
ball of radius `2` form a sequence of tilings with ambient collar `ball 0 1`, come with nearest
vertices satisfying (1.3) for every choice, and satisfy hypothesis (II). -/
theorem exists_lattice_tilingSequence_finite {d : ℕ} (hd : 1 ≤ d) :
    ∃ G : TilingSequence d, HasAmbientCollar (ball (0 : Euc d) 1) G.domain ∧
      Nonempty (NearestVertexData G) ∧ (∀ N : NearestVertexData G, N.ApproximationCondition) ∧
      RegularityII G ∧ ∀ n, Finite (G.tiling n).V := by
  have hdpos : 0 < d := by omega
  have hd0 : d ≠ 0 := by omega
  -- The ambient ball `D` and the mesh scales `h n = 1 / (n + 1)`.
  obtain ⟨D, hD⟩ : ∃ D : Set (Euc d), D = ball (0 : Euc d) 2 := ⟨_, rfl⟩
  have hDb : Bornology.IsBounded D := by
    rw [hD]
    exact Metric.isBounded_ball
  have hz0 : (0 : Euc d) ∈ D := by
    rw [hD]
    exact mem_ball_self two_pos
  obtain ⟨h, hh⟩ : ∃ h : ℕ → ℝ, ∀ n, h n = 1 / ((n : ℝ) + 1) := ⟨_, fun n => rfl⟩
  have hpos : ∀ n, 0 < h n := fun n => by
    rw [hh]
    positivity
  have htend : Tendsto h atTop (𝓝 0) := by
    have hfun : h = fun n : ℕ => 1 / ((n : ℝ) + 1) := funext hh
    rw [hfun]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hgood : ∀ n, GoodVoronoi (grid (h n)) D (h n / 2) (h n * Real.sqrt d) :=
    fun n => goodVoronoi_grid hd (hpos n) hDb
  let G : TilingSequence d :=
    { domain := D
      tiling := fun n => voronoiTiling (grid (h n)) D (hgood n)
      common_domain := fun n => voronoiTiling_domain _ _ _ }
  have hne : ∀ n, Nonempty (G.tiling n).V := fun n =>
    ⟨(exists_vertex_dist_le (hgood n) hz0).choose⟩
  -- Every nearest vertex is within the outer radius.
  have hnear : ∀ (N : NearestVertexData G) (n : ℕ) (z : Euc d), z ∈ D →
      dist ((G.tiling n).pos (N.vertex n z)) z ≤ h n * Real.sqrt d := by
    intro N n z hz
    obtain ⟨v, hv⟩ := exists_vertex_dist_le (hgood n) hz
    rw [dist_comm]
    exact (N.isNearest n z hz v).trans hv
  have hmesh : ∀ n, (G.tiling n).mesh ≤ ENNReal.ofReal (2 * (h n * Real.sqrt d)) :=
    fun n => voronoiTiling_mesh_le (hgood n)
  -- The collar `closure (ball 0 1) ⊆ closedBall 0 1 ⊆ ball 0 2 = interior D`.
  have hcollar : HasAmbientCollar (ball (0 : Euc d) 1) G.domain := by
    show closure (ball (0 : Euc d) 1) ⊆ interior D
    rw [hD, isOpen_ball.interior_eq]
    exact closure_ball_subset_closedBall.trans (closedBall_subset_ball (by norm_num))
  -- Nearest vertices exist.
  have hN : Nonempty (NearestVertexData G) := by
    classical
    refine ⟨{ vertex := fun n z => if hz : z ∈ D then
                (exists_nearest_vertex (hgood n) hz).choose else Classical.choice (hne n)
              isNearest := fun n z hz v => ?_ }⟩
    change z ∈ D at hz
    simp only [hz, dite_true]
    exact (exists_nearest_vertex (hgood n) hz).choose_spec v
  -- The approximation condition (1.3): mesh plus uniform error is at most `3 h √d → 0`.
  have hRtend : Tendsto (fun n => ENNReal.ofReal (3 * (h n * Real.sqrt d))) atTop (𝓝 0) := by
    have h3 := (htend.mul_const (Real.sqrt d)).const_mul 3
    rw [zero_mul, mul_zero] at h3
    have := ENNReal.tendsto_ofReal h3
    rwa [ENNReal.ofReal_zero] at this
  have happrox : ∀ N : NearestVertexData G, N.ApproximationCondition := by
    intro N
    have hbound : ∀ n, (G.tiling n).mesh + N.uniformError n ≤
        ENNReal.ofReal (3 * (h n * Real.sqrt d)) := by
      intro n
      have hR : 0 ≤ h n * Real.sqrt d := mul_nonneg (hpos n).le (Real.sqrt_nonneg _)
      have hu : N.uniformError n ≤ ENNReal.ofReal (h n * Real.sqrt d) :=
        iSup_le fun z => ENNReal.ofReal_le_ofReal (hnear N n z.1 z.2)
      calc (G.tiling n).mesh + N.uniformError n
          ≤ ENNReal.ofReal (2 * (h n * Real.sqrt d)) + ENNReal.ofReal (h n * Real.sqrt d) :=
            add_le_add (hmesh n) hu
        _ = ENNReal.ofReal (3 * (h n * Real.sqrt d)) := by
            rw [← ENNReal.ofReal_add (by linarith : (0 : ℝ) ≤ 2 * (h n * Real.sqrt d)) hR]
            congr 1
            ring
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hRtend
      (fun _ => bot_le) hbound
  -- Hypothesis (II), with `q n = -log ((h n / 2) ^ d * c₀)`, `c₀` the volume of the unit ball.
  have hRII : RegularityII G := by
    obtain ⟨q, hq⟩ : ∃ q : ℕ → ℝ, ∀ n, q n = -Real.log ((h n / 2) ^ d * unitBallVolume d) :=
      ⟨_, fun n => rfl⟩
    have hq_eq : ∀ n, q n = d * Real.log ((n : ℝ) + 1) +
        (d * Real.log 2 - Real.log (unitBallVolume d)) := by
      intro n
      rw [hq, hh]
      exact neg_log_volume d (unitBallVolume_pos d) (by positivity)
    have hsmall : Tendsto (fun n => (h n / 2) ^ d * unitBallVolume d) atTop (𝓝 0) := by
      have := ((htend.div_const 2).pow d).mul_const (unitBallVolume d)
      rwa [zero_div, zero_pow hd0, zero_mul] at this
    -- `q n ≥ 0` eventually, since `(h n / 2) ^ d * c₀ → 0`.
    have hqnn : ∀ᶠ n in atTop, 0 ≤ q n := by
      filter_upwards [hsmall.eventually (gt_mem_nhds one_pos)] with n hn
      rw [hq, neg_nonneg]
      exact Real.log_nonpos
        (mul_nonneg (pow_nonneg (half_pos (hpos n)).le _) (unitBallVolume_pos d).le) hn.le
    -- `log x / x → 0`, transported to `h n * log (n + 1) → 0`.
    have hlogx : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
      have := (isLittleO_log_rpow_atTop (r := 1) one_pos).tendsto_div_nhds_zero
      simpa only [Real.rpow_one] using this
    have hlog : Tendsto (fun n : ℕ => h n * Real.log ((n : ℝ) + 1)) atTop (𝓝 0) := by
      have hshift : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
        tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
      refine Tendsto.congr (fun n => ?_) (hlogx.comp hshift)
      simp only [Function.comp_apply, hh n]
      ring
    have hmain : Tendsto (fun n : ℕ => 2 * (h n * Real.sqrt d) * q n) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => (d : ℝ) * (h n * Real.log ((n : ℝ) + 1)) +
          (d * Real.log 2 - Real.log (unitBallVolume d)) * h n) atTop (𝓝 0) := by
        have := (hlog.const_mul (d : ℝ)).add
          (htend.const_mul (d * Real.log 2 - Real.log (unitBallVolume d)))
        simpa only [mul_zero, add_zero] using this
      have h2 := h1.const_mul (2 * Real.sqrt d)
      rw [mul_zero] at h2
      refine h2.congr fun n => ?_
      rw [hq_eq n]
      ring
    refine ⟨q, ?_, ?_⟩
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmain ?_ ?_
      · filter_upwards [hqnn] with n hn
        exact mul_nonneg ENNReal.toReal_nonneg hn
      · filter_upwards [hqnn] with n hn
        refine mul_le_mul_of_nonneg_right ?_ hn
        have hR : 0 ≤ 2 * (h n * Real.sqrt d) := by
          have := mul_nonneg (hpos n).le (Real.sqrt_nonneg (d : ℝ))
          linarith
        exact ENNReal.toReal_le_of_le_ofReal hR (hmesh n)
    · filter_upwards [hqnn] with n hn
      refine ⟨hn, ?_⟩
      obtain v := (hne n).some
      have hcell_fin : ((G.tiling n).cell v).volume ≠ ∞ := by
        rw [ConvexPolytope.volume, EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
        exact ((G.tiling n).cell v).compact.measure_lt_top.ne
      have hmin_fin : (G.tiling n).minTileVolume ≠ ∞ :=
        ne_top_of_le_ne_top hcell_fin (iInf_le _ v)
      have hle : ENNReal.ofReal ((h n / 2) ^ d * unitBallVolume d) ≤
          (G.tiling n).minTileVolume := by
        rw [← volume_ball_eq_ofReal hdpos (half_pos (hpos n)).le]
        exact volume_ball_le_minTileVolume (hgood n)
      have hpos' : 0 < (h n / 2) ^ d * unitBallVolume d :=
        mul_pos (pow_pos (half_pos (hpos n)) _) (unitBallVolume_pos d)
      rw [hq, neg_neg, Real.exp_log hpos']
      exact (ENNReal.ofReal_le_iff_le_toReal hmin_fin).mp hle
  -- every tiling has finitely many vertices: active points lie within `R` of the bounded `D`
  have hfin : ∀ n, Finite (G.tiling n).V := by
    intro n
    change Finite (activePoints (grid (h n)) D)
    apply Set.Finite.to_subtype
    apply (hgood n).finite.subset
    rintro s ⟨hsS, y, hyc, hyD⟩
    refine ⟨hsS, ?_⟩
    have hR : 0 < h n * Real.sqrt d := (hgood n).R_pos
    have hdist : dist s y ≤ h n * Real.sqrt d := by
      rw [dist_comm]
      exact mem_closedBall.mp ((hgood n).outer s ⟨hsS, y, hyc, hyD⟩ hyc)
    exact cthickening_mono (by linarith) D (mem_cthickening_of_dist_le s y _ D hyD hdist)
  exact ⟨G, hcollar, hN, happrox, hRII, hfin⟩

/-- The hypotheses of Theorems A and B are satisfiable. -/
theorem exists_lattice_tilingSequence {d : ℕ} (hd : 1 ≤ d) :
    ∃ G : TilingSequence d, HasAmbientCollar (ball (0 : Euc d) 1) G.domain ∧
      Nonempty (NearestVertexData G) ∧ (∀ N : NearestVertexData G, N.ApproximationCondition) ∧
      RegularityII G := by
  obtain ⟨G, h1, h2, h3, h4, -⟩ := exists_lattice_tilingSequence_finite hd
  exact ⟨G, h1, h2, h3, h4⟩

end SpherePackings
