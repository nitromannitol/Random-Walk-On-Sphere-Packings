module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/Section3PlanarTarget.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.Section3PlanarEstimate
public import BouRabeeGwynne.Section3CompactCollar
public import BouRabeeGwynne.Section3HarmonicInput
public import BouRabeeGwynne.Section3InternalMass
public import BouRabeeGwynne.Section3WellPosed

@[expose] public section

/-! The planar branch of the actual Theorem B(a) target. -/

open scoped Classical Topology ENNReal
open MeasureTheory

namespace BouRabeeGwynne

/-- The planar case of the approved Theorem B(a) target, including eventual
finite existence and uniqueness and uniform error for every actual solution.
All geometric mass and harmonic energy estimates are proved upstream. -/
theorem theoremB_part_a_planar (G : TilingSequence 2) (N : NearestVertexData G)
    (U : Set (Euc 2)) (hC : Euc 2 → ℝ)
    (hU : Bornology.IsBounded U) (hUD : HasAmbientCollar U G.domain)
    (happrox : N.ApproximationCondition) (hh : HarmonicNearClosure hC U) :
    DirichletApproximationTarget G U hC (fun n v => hC ((G.tiling n).pos v)) := by
  refine ⟨N.eventually_uniqueDirichletExtension (by norm_num)
    (coordinateAxis (0 : Fin 2)) (coordinateAxis_ne_zero 0) happrox hU hUD _, ?_⟩
  obtain ⟨Q, W, ρ, M, hρ, hM, hQc, hW, hhW, hUQ, hQW, hQD, hthick, huc, hH⟩ :=
    hh.exists_compact_collar hU hUD
  have hQfinite : μHE[2] Q ≠ ∞ := by
    have hm : (μHE[2] : Measure (Euc 2)) = volume := by
      simpa using InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := Euc 2)
    rw [hm]
    exact hQc.measure_lt_top.ne
  let K : ℝ := 2 * (μHE[2] Q).toReal
  have hK : 0 ≤ K := mul_nonneg zero_le_two ENNReal.toReal_nonneg
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hmeshlim : Filter.Tendsto (fun n => (G.tiling n).mesh.toReal)
      Filter.atTop (𝓝 0) := by
    simpa only [ENNReal.toReal_zero, Function.comp_def] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (N.mesh_tendsto_zero happrox)
  have hcollar := N.eventually_closedRegion_in_compact_collar happrox hρ hthick
  have hfinite := N.eventually_closedVertices_finite happrox hU hUD
  intro η hη
  have hhalf : 0 < η / 2 := half_pos hη
  obtain ⟨r₀, hr₀, hcontrol⟩ := Metric.uniformContinuousOn_iff.mp huc (η / 2) hhalf
  let r := r₀ / 16
  have hr : 0 < r := div_pos hr₀ (by norm_num)
  have hsmallmesh : ∀ᶠ n in Filter.atTop, (G.tiling n).mesh.toReal < r₀ / 2 :=
    (tendsto_order.mp hmeshlim).2 _ (half_pos hr₀)
  have hratio : Filter.Tendsto
      (fun n => (3 * M * (G.tiling n).mesh.toReal) * K / (η / 2))
      Filter.atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul, zero_div] using
      ((hmeshlim.const_mul (3 * M)).mul_const K).div_const (η / 2)
  have hsmallcolumn : ∀ᶠ n in Filter.atTop,
      (3 * M * (G.tiling n).mesh.toReal) * K / (η / 2) < r :=
    (tendsto_order.mp hratio).2 _ hr
  filter_upwards [hfinite, hcollar, hsmallmesh, hsmallcolumn]
    with n hfin hn hsmall hcolumn
  intro hD hsol v hv
  let T := G.tiling n
  let R := T.closedVertices U
  let A := T.finiteInterior U
  letI : Fintype R := hfin.fintype
  have hcellQ : ∀ v : R, (T.cell v).carrier ⊆ Q := fun v => (hn.2 v v.property).1
  have hballQ : ∀ v : R, Metric.closedBall (T.pos v) (2 * T.mesh.toReal) ⊆ Q :=
    fun v => (hn.2 v v.property).2
  have hcellD : ∀ v ∈ A, (T.cell v).carrier ⊆ interior T.domain := by
    intro v _
    simpa only [T, G.common_domain n] using (hcellQ v).trans hQD
  have hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R := by
    intro v hv w hvw
    exact T.neighbor_mem_closedVertices hv hvw
  have ha := T.finiteNetwork_boundaryAccessible_of_cell_interior (by norm_num)
    (coordinateAxis (0 : Fin 2)) (coordinateAxis_ne_zero 0) R A hneighbors hcellD
  have hsolR := T.solvesDirichlet_restrict hsol
  have hzero : ∀ w : R, w ∉ A → (hD - fun w => hC (T.pos w)) w = 0 := by
    intro w hw
    exact sub_eq_zero.mpr (hsolR.2 w hw)
  have henergy : T.incidentEnergy R A (hD - fun w => hC (T.pos w)) ≤
      (3 * M * T.mesh.toReal) ^ 2 * T.incidentMass R A := by
    rw [T.incidentEnergy_eq_networkEnergy R A _ hzero]
    exact T.harmonic_error_energy_le_incidentMass (by norm_num) R A
      (fun w => hD w) hC hn.1 hM0 hsolR hcellD hneighbors hW hhW
      (fun w => (hballQ w).trans hQW) (fun w x hx => hH x (hballQ w hx))
  have hmass : T.incidentMass R A ≤ K :=
    T.incidentMass_le_dim_mul_volume (by norm_num) R A hQfinite hcellQ
  have hmod : ∀ v w : R, dist (T.pos w) (T.pos v) ≤ T.mesh.toReal + 8 * r →
      |hC (T.pos w) - hC (T.pos v)| ≤ η / 2 := by
    intro v w hwv
    have hp (u : R) : T.pos u ∈ Q :=
      hcellQ u (interior_subset (T.pos_mem_interior u))
    have hdist : dist (T.pos w) (T.pos v) < r₀ := by
      dsimp [r] at hwv
      linarith
    simpa only [Real.dist_eq] using (hcontrol _ (hp w) _ (hp v) hdist).le
  have hbound := T.planar_error_le_of_energy_bound R A ha hneighbors hcellD hD
    (fun w => hC (T.pos w)) hsolR (by positivity) hK hhalf hhalf.le
    henergy hmass hcolumn hn.1 hmod
    ⟨v, T.interiorVertices_subset_closedVertices U hv⟩ hv
  linarith

end BouRabeeGwynne
