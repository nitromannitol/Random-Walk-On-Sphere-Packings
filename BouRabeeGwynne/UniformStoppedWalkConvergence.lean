-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/UniformStoppedWalkConvergence.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.TheoremACouplingSetup
import BouRabeeGwynne.CouplingPartitions
import BouRabeeGwynne.NearestCouplingStarts
import BouRabeeGwynne.TilingStoppedLawComparison
import BouRabeeGwynne.AmbientStoppedWalkLaw
import BouRabeeGwynne.CouplingErrorBudget

/-! Uniform convergence of the actual stopped tiling-walk laws. The fixed
geometry and skeleton length precede the fine partitions and the eventual
tiling index; the final estimate is uniform over every starting point in U. -/

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped unitInterval NNReal ENNReal

namespace BouRabeeGwynne

local instance uniformOptionMeasurableSpace {X : Type*} : MeasurableSpace (Option X) := ⊤

theorem NearestVertexData.eventually_stoppedWalkLaw_levyProkhorov_le
    {d : ℕ} (hd : 1 ≤ d) {G : TilingSequence d} (N : NearestVertexData G)
    {U : Set (Euc d)} (hU : IsOpen U) (hL : HasLipschitzBoundary U)
    (hUb : Bornology.IsBounded U) (hUD : HasAmbientCollar U G.domain)
    (happrox : N.ApproximationCondition) (hreg : PaperRegularity G)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n in atTop, ∀ z ∈ U, ∀ ν : Measure (CurveSpace d),
      IsStoppedTilingWalkLaw (G.tiling n) U (N.vertex n z) ν →
        levyProkhorovEDist ν (stoppedBrownianLaw U z μ) ≤ ENNReal.ofReal η := by
  classical
  letI : IsProbabilityMeasure μ := hμ.1
  obtain ⟨δ, r, W, Q, centers, K, hδ, hr, hrδ, hrη, hW, hWb, hUW, hWD,
      hQ, hCQ, hcenters, hcover, hballs, hballsQ, hprob⟩ :=
    exists_theoremA_coupling_setup hd hU hUb hL hUD hμ hη
  have hBW : ∀ j : centers, ball j.val r ⊆ W :=
    fun j => ball_subset_closedBall.trans (hballs j.val j.property)
  have hstep := coupling_step_error_budget hη K
  obtain ⟨m, E, hE, hdE, select, hs, δ₀, hδ₀, hmargin, hactive, hdiam, hcouple⟩ :=
    exists_eventual_walkBrownian_coupling_partitions hd G N happrox hreg hμ
      centers hr hWb hWD hQ hCQ hBW (fun j => hballsQ j.val j.property) hcover
      hr hstep.1 K
  have hnone : ∀ i x, select i x = none → x ∉ thickening δ U := by
    intro i x hx hxin
    exact hactive i x (thickening_subset_cthickening δ U hxin) hx
  have hmarginB : ∀ i x j, brownianSelectorForWalk select i x = some j →
      ball x (r / 2) ⊆ ball j.val r := fun i x j => hmargin (i - 1) x j
  have hnoneB : ∀ i x, brownianSelectorForWalk select i x = none →
      x ∉ thickening δ U := fun i x => hnone (i - 1) x
  obtain ⟨q, hq, hwalkBudget, hbrownianBudget, hmiddleBudget, hsmall, htotal⟩ :=
    exists_coupling_stopped_error_budget hη hr hrη
  have hstarts := N.eventually_nearest_coupling_starts happrox hUD centers hr
    (lt_min hδ₀ hr) (fun z hz => hcover z (self_subset_cthickening U hz)) hballs
  filter_upwards [hcouple, N.eventually_mesh_finite_le happrox (by positivity : 0 < r / 4),
    hstarts] with n hn hmesh hnstarts
  obtain ⟨hfin, hn⟩ := hn
  letI : Fintype ((G.tiling n).closedVertices W) := hfin.fintype
  letI : MeasurableSpace ((G.tiling n).closedVertices W) := ⊤
  obtain ⟨haccess, hA, hB, hfailure⟩ := hn
  intro z hz ν hν
  obtain ⟨initial, v, hvval, hv, hzball, hnear⟩ := hnstarts z hz
  let P := TimePartition.uniform K
  have hprobz := hprob z hz initial (brownianSelectorForWalk select)
    (fun i => (hs (i - 1)).mono le_rfl le_top) hmarginB hnoneB P
  have hΓ : Measurable (fun ω k => brownianSkeletonExcursion
      (fun c : centers => ball c.val r) z initial (brownianSelectorForWalk select) k ω) :=
    Measurable.of_eval fun k => measurable_brownianSkeletonExcursion
      (fun c : centers => ball c.val r) (fun _ => isOpen_ball) z initial
      (fun i => hs (i - 1)) k
  have hset : MeasurableSet {γ : ℕ → Bool × C(unitInterval, Euc d) |
      pastedBrownianCurve P γ ∈
        unitCurveExitOscillationBad (innerDomain U (6 * r)) (thickening δ U) (η / 10)} :=
    (measurableSet_unitCurveExitOscillationBad (isOpen_innerDomain U (6 * r))
      isOpen_thickening (η / 10)).preimage (measurable_pastedBrownianCurve P)
  have hosc := hprobz.2
  rw [Measure.map_apply hΓ hset] at hosc
  have hfail := hfailure initial v z hv hzball (hnear.trans (min_le_left _ _))
  rw [hstep.2] at hfail
  have hbuffer : 6 * r + 2 * (G.tiling n).mesh.toReal < δ := by linarith [hmesh.2]
  have hpoint : (2 * r + 2 * (G.tiling n).mesh.toReal) + r + 2 * r ≤ 6 * r := by
    linarith [hmesh.2]
  have hcompare := (G.tiling n).levyProkhorov_actual_tiling_stopped_laws_le hd hWb
    (fun c : centers => c.val) hr hBW hmesh.1 hA hB haccess μ hμ select hs hmargin
    m E hE hdE initial v z (closedBall_subset_ball (half_lt_self hr) hv)
    (closedBall_subset_ball (half_lt_self hr) hzball) K P hU
    (by positivity : 0 < 6 * r) hbuffer hnone (fun i _ => hdiam i)
    (hnear.trans (min_le_right _ _)) hpoint hfail
    (by simpa only [brownianSkeletonExcursion_flag] using hprobz.1)
    (by simpa only [two_mul, pastedBrownianCurve, Set.preimage_setOf_eq] using hosc)
    q q q hq hq hwalkBudget hbrownianBudget hmiddleBudget hsmall
  have hν' : IsStoppedTilingWalkLaw (G.tiling n) U v.val ν := by
    simpa only [hvval] using hν
  rw [(G.tiling n).isStoppedTilingWalkLaw_eq_ambient U _
    ((G.tiling n).closedVertices_mono hUW) ((G.tiling n).finiteInterior W)
    (fun _ hw => hUW hw) hA v hν']
  exact hcompare.trans htotal

end BouRabeeGwynne
