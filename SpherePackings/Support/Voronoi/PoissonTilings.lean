import SpherePackings.Support.Voronoi.PoissonCells
import SpherePackings.Support.Voronoi.TilingProps
import SpherePackings.Support.TheoremBPartB.Proof
import BouRabeeGwynne.TheoremAProved

/-!
# Proposition 1.1, second part: Theorems A and B for Poisson–Voronoi tilings

`rw-spheres.tex:371-381` ("In particular, the conclusions of Theorem B and, if `U` is Lipschitz,
Theorem A, hold for the graphs `G_Vor(Λ_m)`") and `rw-spheres.tex:1760-1764`.

Fix a neighbourhood `D = thickening ρ U` of `closure U`.  Almost surely, for all large `m`, the
Voronoi cells of `Λ_m` meeting `D` lie between balls of radii `m^{-8/β⁻}/2` and `m^{-1/(3β⁺)}`, and
every point of `D` is near a point of `Λ_m`; so these cells form an orthogonal tiling of `D`
(`Voronoi.voronoiTiling`).  From such an index `m₀` on, the sequence of these tilings (and before it
the tiling at `m₀`) satisfies the hypotheses of Theorems A and B with hypothesis (II): the mesh is at
most `2 m^{-1/(3β⁺)}`, every nearest vertex is within `m^{-1/(3β⁺)}`, and the smallest tile has
volume at least a constant times `m^{-8d/β⁻}`, which is `exp(-O(log m))`.

The vertices of the tiling are the points of `Λ_m` whose cells meet `D`, rather than all of `Λ_m`;
the Dirichlet problem on `U` and the walk stopped on leaving `U` only involve cells meeting `U`.
-/

open MeasureTheory Metric Filter Set
open scoped ENNReal NNReal Topology

namespace SpherePackings

open BouRabeeGwynne Voronoi

variable {d : ℕ}

/-- `T` is the Voronoi tiling of `D` by the point set `S`: its vertices are the points of `S` whose
Voronoi cells meet `D`, and its tiles are those cells. -/
def IsVoronoiTilingOf (T : OrthogonalTiling d) (S D : Set (Euc d)) : Prop :=
  T.domain = D ∧ range T.pos = activePoints S D ∧ ∀ v, (T.cell v).carrier = cell S (T.pos v)

lemma voronoiTiling_isVoronoiTilingOf {S D : Set (Euc d)} {r R : ℝ} (h : GoodVoronoi S D r R) :
    IsVoronoiTilingOf (voronoiTiling S D h) S D :=
  ⟨voronoiTiling_domain S D h,
    Set.ext fun _ => ⟨fun ⟨v, hv⟩ => hv ▸ voronoiTiling_pos S D h v,
      fun hs => voronoiTiling_pos_surjective S D h hs⟩,
    voronoiTiling_cell S D h⟩

/-- A point within `R` of a finite-near set `S` lies in the Voronoi cell of a nearest point. -/
lemma exists_mem_cell_of_near {S : Set (Euc d)} {y s₀ : Euc d} {R : ℝ} (hs₀ : s₀ ∈ S)
    (hy : dist s₀ y < R) (hfin : (S ∩ closedBall y R).Finite) : ∃ s ∈ S, y ∈ cell S s := by
  obtain ⟨s, ⟨hsS, hsB⟩, hmin⟩ := Set.exists_min_image _ (fun s => dist s y) hfin
    ⟨s₀, hs₀, mem_closedBall.mpr hy.le⟩
  refine ⟨s, hsS, fun s' hs' => ?_⟩
  by_cases hs'B : s' ∈ closedBall y R
  · exact hmin s' ⟨hs', hs'B⟩
  · have h1 : R < dist s' y := by
      rw [mem_closedBall, not_le] at hs'B; exact hs'B
    have h2 : dist s y ≤ dist s₀ y :=
      hmin s₀ ⟨hs₀, mem_closedBall.mpr hy.le⟩
    linarith

/-- **Proposition 1.1**, second part: almost surely the Voronoi tilings of `Λ_m` (eventually)
satisfy the hypotheses of Theorems A and B, with hypothesis (II). -/
theorem voronoi_tilings_hypotheses (hd : 1 ≤ d) {U : Set (Euc d)} (hU : IsDomain U)
    (hUb : Bornology.IsBounded U) {μ : Measure (Euc d)} {βp βm : ℝ} (hβp : 0 < βp)
    (hβm : 0 < βm) {W : Set (Euc d)} (hW : IsOpen W) (hUW : closure U ⊆ W)
    (hμ : HolderMassBounds μ W βp βm)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Λ : ℕ → Ω → Set (Euc d)) (hΛ : ∀ m : ℕ, IsPoissonPointProcess P (Λ m) ((m : ℝ≥0∞) • μ)) :
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
  filter_upwards [voronoi_cells_between_balls_aux hd hDb hβp hβm hW hDW hμ P Λ hΛ] with ω hω
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
      exact (hΛ m).finite _ hDb.cthickening ω
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

/-- **Proposition 1.1**, "in particular" clause: almost surely the conclusions of Theorem B and,
when `U` is Lipschitz, of Theorem A hold for the Voronoi tilings of `Λ_m`. -/
theorem voronoi_tilings_theoremAB (hd : 1 ≤ d) {U : Set (Euc d)} (hU : IsDomain U)
    (hUb : Bornology.IsBounded U) {μ : Measure (Euc d)} {βp βm : ℝ} (hβp : 0 < βp)
    (hβm : 0 < βm) {W : Set (Euc d)} (hW : IsOpen W) (hUW : closure U ⊆ W)
    (hμ : HolderMassBounds μ W βp βm)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Λ : ℕ → Ω → Set (Euc d)) (hΛ : ∀ m : ℕ, IsPoissonPointProcess P (Λ m) ((m : ℝ≥0∞) • μ)) :
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
  filter_upwards [voronoi_tilings_hypotheses hd hU hUb hβp hβm hW hUW hμ P Λ hΛ] with ω hω
  obtain ⟨G, hcollar, hvor, ⟨N₀⟩, happrox, hII⟩ := hω
  have hreg : PaperRegularity G := Or.inr (Or.inl hII)
  refine ⟨G, hcollar, hvor, fun hC hh => ?_, fun hL hC hh hc => ?_, fun hL N => ?_⟩
  · exact theoremB_part_a d G N₀ U hC hd hU hUb hcollar (happrox N₀) hreg hh
  · exact theoremB_part_b d G N₀ U hC hd hL hUb hcollar (happrox N₀) hreg hh hc
  · exact theoremA_proved d hd G N U hL hUb hcollar (happrox N) hreg

end SpherePackings
