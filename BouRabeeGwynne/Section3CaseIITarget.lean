module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/Section3CaseIITarget.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.Section3CaseII
public import BouRabeeGwynne.Section3CompactCollar
public import BouRabeeGwynne.Section3WellPosed
public import BouRabeeGwynne.CoordinateHyperplane

@[expose] public section

/-! The actual small-tile branch of Theorem B(a). -/

open scoped Classical Topology ENNReal
open MeasureTheory

namespace BouRabeeGwynne

lemma exists_unit_euc {d : ℕ} (hd : 1 ≤ d) :
    ∃ e : Euc d, e ≠ 0 ∧ ‖e‖ = 1 := by
  cases d with
  | zero => omega
  | succ n =>
    exact ⟨coordinateAxis (0 : Fin (n + 1)), coordinateAxis_ne_zero 0, norm_coordinateAxis 0⟩

/-- Hypothesis II gives the actual uniform Dirichlet limit. The cutoff is
applied to the actual geometric mass decay; no convergence or error estimate
is assumed as an input. Empty discrete interiors are handled without dividing
by a zero mesh. -/
theorem theoremB_part_a_caseII {d : ℕ} (hd : 1 ≤ d)
    (G : TilingSequence d) (N : NearestVertexData G) (U : Set (Euc d))
    (hC : Euc d → ℝ) (hU : Bornology.IsBounded U)
    (hUD : HasAmbientCollar U G.domain) (happrox : N.ApproximationCondition)
    (hII : RegularityII G) (hh : HarmonicNearClosure hC U) :
    DirichletApproximationTarget G U hC (fun n v => hC ((G.tiling n).pos v)) := by
  obtain ⟨e, he, hnorm⟩ := exists_unit_euc hd
  refine ⟨N.eventually_uniqueDirichletExtension hd e he happrox hU hUD _, ?_⟩
  obtain ⟨Q, W, ρ, M, hρ, hM, hQc, hW, hhW, hUQ, hQW, hQD, hthick, huc, hH⟩ :=
    hh.exists_compact_collar hU hUD
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hQfinite : μHE[d] Q ≠ ∞ := by
    have hm : (μHE[d] : Measure (Euc d)) = volume := by
      simpa using InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := Euc d)
    rw [hm]
    exact hQc.measure_lt_top.ne
  obtain ⟨B, hB⟩ := hQc.exists_bound_of_continuousOn
    (continuous_id.continuousOn : ContinuousOn (fun x : Euc d => x) Q)
  let D := max B 1
  have hD0 : 0 ≤ D := zero_le_one.trans (le_max_right _ _)
  have hnormQ : ∀ x ∈ Q, ‖x‖ ≤ D := fun x hx => (hB x hx).trans (le_max_left _ _)
  let K := max (2 * (d : ℝ) * (μHE[d] Q).toReal) 1
  have hK : 1 ≤ K := le_max_right _ _
  let C := 3 * M
  have hC0 : 0 ≤ C := mul_nonneg (by norm_num) hM0
  let H := (d : ℝ) * ‖e‖ * (D - -D)
  have hH0 : 0 ≤ H := mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) (by linarith)
  let Z := caseIIThresholdCoefficient H C
  have hZ : 0 < Z := caseIIThresholdCoefficient_pos hH0 hC0
  obtain ⟨q, hq, hqrange⟩ := hII
  have hmeshlim : Filter.Tendsto (fun n => (G.tiling n).mesh.toReal)
      Filter.atTop (𝓝 0) := by
    simpa only [ENNReal.toReal_zero, Function.comp_def] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (N.mesh_tendsto_zero happrox)
  have hcutlim := geometricVolumeCutoff_mul_mesh_tendsto_zero hK
    (fun n => (G.tiling n).mesh.toReal) q (fun _ => ENNReal.toReal_nonneg)
    (hqrange.mono (fun _ h => h.1)) hmeshlim hq
  have hcostlim : Filter.Tendsto
      (fun n => (Z + 2) * ((geometricVolumeCutoff K (q n) : ℝ) *
        (G.tiling n).mesh.toReal)) Filter.atTop (𝓝 0) := by
    simpa only [mul_zero] using hcutlim.const_mul (Z + 2)
  have hsmall : ∀ᶠ n in Filter.atTop, C * (G.tiling n).mesh.toReal < 1 / 2 := by
    have hlim : Filter.Tendsto (fun n => C * (G.tiling n).mesh.toReal)
        Filter.atTop (𝓝 0) := by simpa only [mul_zero] using hmeshlim.const_mul C
    exact (tendsto_order.mp hlim).2 _ (by norm_num)
  have hcollar := N.eventually_closedRegion_in_compact_collar happrox hρ hthick
  have hfinite := N.eventually_closedVertices_finite happrox hU hUD
  intro η hη
  have hcost : ∀ᶠ n in Filter.atTop,
      (Z + 2) * ((geometricVolumeCutoff K (q n) : ℝ) * (G.tiling n).mesh.toReal) < η :=
    (tendsto_order.mp hcostlim).2 _ hη
  filter_upwards [hfinite, hcollar, hsmall, hqrange, hcost]
    with n hfin hn hsmalln hqn hcostn
  intro hD hsol v hv
  let T := G.tiling n
  let R := T.closedVertices U
  let A := T.finiteInterior U
  letI : Fintype R := hfin.fintype
  let vR : R := ⟨v, T.interiorVertices_subset_closedVertices U hv⟩
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
  have hε : 0 < T.mesh.toReal := T.mesh_toReal_pos_of_accessible_vertex R A ha hn.1 (v := vR) hv
  have hheight : ∀ v ∈ A, ∀ x ∈ (T.cell v).carrier,
      inner ℝ e x / inner ℝ e e ∈ Set.Icc (-D) D := by
    intro v hv x hx
    rw [real_inner_self_eq_norm_sq, hnorm, one_pow, div_one]
    have hinner : |inner ℝ e x| ≤ D := by
      calc
        _ ≤ ‖e‖ * ‖x‖ := abs_real_inner_le_norm _ _
        _ = ‖x‖ := by rw [hnorm, one_mul]
        _ ≤ D := hnormQ x (hcellQ v hx)
    exact abs_le.mp hinner
  have hmass : 2 * T.incidentMass R A ≤ K := by
    calc
      _ ≤ 2 * ((d : ℝ) * (μHE[d] Q).toReal) :=
        mul_le_mul_of_nonneg_left (T.incidentMass_le_dim_mul_volume hd R A hQfinite hcellQ)
          zero_le_two
      _ ≤ K := by
        dsimp [K]
        simpa only [mul_assoc] using
          (le_max_left (2 * (d : ℝ) * (μHE[d] Q).toReal) 1)
  have hfactor : (d : ℝ) * ‖e‖ * (D - -D) * (3 * M * T.mesh.toReal) /
      (Z * T.mesh.toReal) + ((2 * T.mesh.toReal) ^ 2 / (2 * T.mesh.toReal) ^ 2) *
        (3 * M * T.mesh.toReal) ^ 2 ≤ 1 / 2 :=
    caseII_mesh_scaled_contraction hH0 hC0 hε hsmalln.le
  have hbound := T.dirichlet_error_le_volume_cutoff_of_harmonic hd R A ha hneighbors hcellD
    hC (fun w => hD w) (T.solvesDirichlet_restrict hsol) e he (-D) D
    (by linarith) hheight hM0 (mul_pos hZ hε) (mul_pos (by norm_num) hε) hn.1
    (fun v w hvw => by simpa only [dist_eq_norm, norm_sub_rev] using
      T.toTilingData.edge_dist_le_two_mesh hvw hn.1)
    hW hhW (fun w => (hballQ w).trans hQW) (fun w x hx => hH x (hballQ w hx))
    hfactor hK hmass hqn.2 vR
  have hcosteq : (geometricVolumeCutoff K (q n) : ℝ) *
      (Z * T.mesh.toReal + 2 * T.mesh.toReal) =
      (Z + 2) * ((geometricVolumeCutoff K (q n) : ℝ) * T.mesh.toReal) := by ring
  exact hbound.trans (hcosteq.le.trans hcostn.le)

end BouRabeeGwynne
