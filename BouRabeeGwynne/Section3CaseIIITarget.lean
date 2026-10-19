-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/Section3CaseIIITarget.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.HypIIIErrorBound
import BouRabeeGwynne.Section3CompactCollar
import BouRabeeGwynne.Section3WellPosed
import BouRabeeGwynne.CoordinateHyperplane

/-! The actual hypothesis III branch of Theorem B(a). -/

open scoped Classical Topology ENNReal
open MeasureTheory

namespace BouRabeeGwynne

/-- The original local diameter hypothesis gives uniform approximation by
actual discrete Dirichlet solutions. The corrected iteration, its geometric
mass decay, and the boundary correction costs are proved upstream. -/
theorem theoremB_part_a_caseIII {d : ℕ} (hd : 1 ≤ d)
    (G : TilingSequence d) (N : NearestVertexData G) (U : Set (Euc d))
    (hC : Euc d → ℝ) (hU : Bornology.IsBounded U)
    (hUD : HasAmbientCollar U G.domain) (happrox : N.ApproximationCondition)
    (hIII : RegularityIII G) (hh : HarmonicNearClosure hC U) :
    DirichletApproximationTarget G U hC (fun n v => hC ((G.tiling n).pos v)) := by
  obtain ⟨e, he, hnorm⟩ : ∃ e : Euc d, e ≠ 0 ∧ ‖e‖ = 1 := by
    cases d with
    | zero => omega
    | succ n => exact ⟨coordinateAxis (0 : Fin (n + 1)),
        coordinateAxis_ne_zero 0, norm_coordinateAxis 0⟩
  refine ⟨N.eventually_uniqueDirichletExtension hd e he happrox hU hUD _, ?_⟩
  obtain ⟨Q, W, ρ, M, hρ, hM, hQc, hW, hhW, hUQ, hQW, hQD, hthick, huc, hH⟩ :=
    hh.exists_compact_collar hU hUD
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  have hQfinite : μHE[d] Q ≠ ∞ := by
    have hm : (μHE[d] : Measure (Euc d)) = volume := by
      simpa using InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := Euc d)
    rw [hm]
    exact hQc.measure_lt_top.ne
  obtain ⟨B, hB⟩ := hQc.exists_bound_of_continuousOn
    (f := fun x : Euc d => x) continuous_id.continuousOn
  let D := max B 1
  have hD0 : 0 ≤ D := zero_le_one.trans (le_max_right _ _)
  have hnormQ : ∀ x ∈ Q, ‖x‖ ≤ D := fun x hx => (hB x hx).trans (le_max_left _ _)
  let I := (d : ℝ) * (μHE[d] Q).toReal
  have hI : 0 ≤ I := mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg
  let H := (d : ℝ) * ‖e‖ * (D - -D)
  have hH0 : 0 ≤ H := mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) (by linarith)
  let K := 12 * H + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hwidth : 12 * H ≤ K := by dsimp [K]; linarith
  obtain ⟨α, hα, C, hCfinite, hreg⟩ := hIII
  let J := C.toReal * (2 * I) ^ α
  let r := (1 / 2 : ℝ) ^ α
  have hJ : 0 ≤ J := mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (by positivity) α)
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) α
  have hr1 : r < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα
  let ε := fun n => (G.tiling n).mesh.toReal
  have hε0 : ∀ n, 0 ≤ ε n := fun _ => ENNReal.toReal_nonneg
  have hεlim : Filter.Tendsto ε Filter.atTop (𝓝 0) := by
    simpa only [ε, Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (N.mesh_tendsto_zero happrox)
  have hsmall : ∀ᶠ n in Filter.atTop, 144 * M ^ 2 * ε n ^ 2 ≤ 1 := by
    have hlim : Filter.Tendsto (fun n => 144 * M ^ 2 * ε n ^ 2)
        Filter.atTop (𝓝 0) := by
      simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero] using
        (hεlim.pow 2).const_mul (144 * M ^ 2)
    exact ((tendsto_order.mp hlim).2 1 (by norm_num)).mono (fun _ h => h.le)
  let P (n : ℕ) (δ : ℕ → ℝ) : Prop :=
    (∀ i, 0 ≤ δ i ∧ δ i ≤ ε n ∧ δ i ≤ J * r ^ i) ∧
    ∀ hD : (G.tiling n).V → ℝ,
      (G.tiling n).SolvesDirichlet U (fun v => hC ((G.tiling n).pos v)) hD →
      ∀ v ∈ (G.tiling n).interiorVertices U,
        |hD v - hC ((G.tiling n).pos v)| ≤ hypIIICost K (3 * M) (ε n) δ
  have hex : ∀ᶠ n in Filter.atTop, ∃ δ, P n δ := by
    filter_upwards [N.eventually_closedVertices_finite happrox hU hUD,
      N.eventually_closedRegion_in_compact_collar happrox hρ hthick, hsmall, hreg]
      with n hfin hn hsmalln hregn
    let T := G.tiling n
    let R := T.closedVertices U
    let A := T.finiteInterior U
    letI : Fintype R := hfin.fintype
    by_cases hempty : A = ∅
    · refine ⟨fun _ => 0, (fun i => ⟨le_rfl, hε0 n,
        mul_nonneg hJ (pow_nonneg hr0 i)⟩), ?_⟩
      intro hD hsol v hv
      have hvR : (⟨v, T.interiorVertices_subset_closedVertices U hv⟩ : R) ∈ A := hv
      exact False.elim (by simpa only [hempty, Set.mem_empty_iff_false] using hvR)
    obtain ⟨v₀, hv₀⟩ := Set.nonempty_iff_ne_empty.mpr hempty
    have hcellQ : ∀ v : R, (T.cell v).carrier ⊆ Q := fun v => (hn.2 v v.property).1
    have hballQ : ∀ v : R, Metric.closedBall (T.pos v) (2 * T.mesh.toReal) ⊆ Q :=
      fun v => (hn.2 v v.property).2
    have hcellD : ∀ v ∈ A, (T.cell v).carrier ⊆ interior T.domain := by
      intro v _
      simpa only [T, G.common_domain n] using (hcellQ v).trans hQD
    have hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R := by
      intro v hv w hvw
      exact T.neighbor_mem_closedVertices hv hvw
    have ha := T.finiteNetwork_boundaryAccessible_of_cell_interior hd e he R A hneighbors hcellD
    have hε : 0 < T.mesh.toReal :=
      T.mesh_toReal_pos_of_accessible_vertex R A ha hn.1 hv₀
    have hheight : ∀ v ∈ A, ∀ x ∈ (T.cell v).carrier,
        inner ℝ e x / inner ℝ e e ∈ Set.Icc (-D) D := by
      intro v hv x hx
      rw [real_inner_self_eq_norm_sq, hnorm, one_pow, div_one]
      apply abs_le.mp
      calc
        |inner ℝ e x| ≤ ‖e‖ * ‖x‖ := abs_real_inner_le_norm _ _
        _ = ‖x‖ := by rw [hnorm, one_mul]
        _ ≤ D := hnormQ x (hcellQ v hx)
    have hmass : T.incidentMass R A ≤ I :=
      T.incidentMass_le_dim_mul_volume hd R A hQfinite hcellQ
    have hlength : ∀ v w : R, T.adj v w → ‖T.pos w - T.pos v‖ ≤ 2 * T.mesh.toReal := by
      intro v w hvw
      simpa only [dist_eq_norm, norm_sub_rev] using T.toTilingData.edge_dist_le_two_mesh hvw hn.1
    have hdiam : ∀ v ∈ A, Metric.diam (T.cell v).carrier ≤ T.mesh.toReal := by
      intro v _
      have hdia : (T.cell v).diamENN ≤ T.mesh :=
        le_iSup (fun w : T.V => (T.cell w).diamENN) v
      simpa only [ConvexPolytope.diamENN, ENNReal.toReal_ofReal Metric.diam_nonneg] using
        ENNReal.toReal_mono hn.1 hdia
    let S := T.correctedRegions R A ha hC K M T.mesh.toReal
    let δ := fun i => T.toTilingData.regionDiameter R (S i).val
    have hsub (i : ℕ) : (S i).val ⊆ A := (S i).property
    have hdecay : ∀ i, T.incidentMass R (S i).val ≤ I * (1 / 2 : ℝ) ^ i := by
      intro i
      exact (T.correctedRegions_mass_le_geometric hd R A ha hneighbors hcellD hC e he
        (-D) D (by linarith) hheight hK hMpos hε hwidth hsmalln hlength hdiam hW hhW
        (fun v _ => (hballQ v).trans hQW) (fun v _ x hx => hH x (hballQ v hx)) i).trans
          (mul_le_mul_of_nonneg_right hmass (pow_nonneg (by norm_num) i))
    have hgeom : ∀ i, δ i ≤ J * r ^ i :=
      T.regionDiameter_le_geometric_of_mass R (fun i => (S i).val)
        (fun i v hv => hneighbors v (hsub i hv)) hα.le hCfinite
        (fun i v hv => hregn v) hI hdecay
    refine ⟨δ, (fun i => ⟨T.toTilingData.regionDiameter_nonneg R (S i).val,
      T.toTilingData.regionDiameter_le R (S i).val hε.le
        (fun v hv => hdiam v (hsub i hv)), hgeom i⟩), ?_⟩
    intro hD hsol v hv
    let vR : R := ⟨v, T.interiorVertices_subset_closedVertices U hv⟩
    have heq := (T.finiteNetwork R).dirichlet_unique A ha
      (T.solvesDirichlet_restrict hsol)
      ((T.finiteNetwork R).dirichletSolution_spec A ha (fun v : R => hC (T.pos v)))
    have heqv := congrFun heq vR
    change hD v = _ at heqv
    rw [heqv]
    exact T.dirichlet_error_le_hypIIICost hd R A ha hneighbors hcellD hC e he
      (-D) D (by linarith) hheight hK hMpos hε hwidth hsmalln hlength hdiam hW hhW
      (fun v _ => (hballQ v).trans hQW) (fun v _ x hx => hH x (hballQ v hx))
      hα hCfinite (fun v _ => hregn v) hI hmass vR
  let δ : ℕ → ℕ → ℝ := fun n => if hn : ∃ f, P n f then Classical.choose hn else fun _ => 0
  have hδgood {n : ℕ} (hn : ∃ f, P n f) : P n (δ n) := by
    simpa only [δ, dif_pos hn] using Classical.choose_spec hn
  have hδbounds (n i : ℕ) : 0 ≤ δ n i ∧ δ n i ≤ ε n ∧ δ n i ≤ J * r ^ i := by
    by_cases hn : ∃ f, P n f
    · exact (hδgood hn).1 i
    · simp only [δ, dif_neg hn]
      exact ⟨le_rfl, hε0 n, mul_nonneg hJ (pow_nonneg hr0 i)⟩
  have hcostlim := hypIIICost_tendsto_zero ε δ hK.le (by positivity : 0 ≤ 3 * M)
    hJ hr0 hr1 hε0 hεlim (fun n i => (hδbounds n i).1)
    (fun n i => (hδbounds n i).2.1) (fun n i => (hδbounds n i).2.2)
  intro η hη
  filter_upwards [hex, (tendsto_order.mp hcostlim).2 η hη] with n hn hcost
  intro hD hsol v hv
  exact ((hδgood hn).2 hD hsol v hv).trans hcost.le

end BouRabeeGwynne
