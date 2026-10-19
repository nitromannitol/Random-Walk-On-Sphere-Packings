-- Built on Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne (commit cf73d6e).
import BouRabeeGwynne.TheoremACouplingSetup
import BouRabeeGwynne.CouplingErrorBudget
import SpherePackings.Support.Section4General.CouplingPartitions
import SpherePackings.Support.Section4General.NearestStarts
import SpherePackings.General.Walk.BallStoppedLawComparison

/-!
# Theorem 4.1

Theorem 4.1 of rw-spheres.tex (`theorem:general-clt`, lines 1481–1488), for any sequence of
nearest-neighbour walks on graphs with vertices in `ℝ^d` under Assumption D as printed: for a
bounded Lipschitz domain `U ⊆ D`, the walk started at the nearest vertex `z^n` of `z`, interpolated
and stopped at its first exit from `V_n[U]`, converges to Brownian motion from `z` stopped at its
exit from `U`, as curves modulo time parametrization, uniformly over `z ∈ U`.  The walk eventually
exits `V_n[U]` almost surely.

The proof is leobon12's proof of Theorem A (finite ball couplings with partitions of the exit
points, `exists_theoremA_coupling_setup`) with the tiling inputs replaced: the exit laws from balls
converge by Proposition 4.2, the walk steps are bounded on the good event only, and the collar of
`U` comes from the `δ`-neighbourhood of `D` in Assumption D.
-/

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped unitInterval NNReal ENNReal

namespace SpherePackings

open BouRabeeGwynne

local instance theorem41OptionMeasurableSpace {X : Type*} : MeasurableSpace (Option X) := ⊤

variable {d : ℕ}

/-- **Theorem 4.1** (`theorem:general-clt`). -/
theorem theorem41_general (hd : 1 ≤ d) (W : ℕ → NearestNeighbourWalk d)
    (near : ∀ n, Euc d → (W n).V) (hnear : ∀ n, (W n).IsNearestVertex (near n))
    {D : Set (Euc d)} {δD : ℝ} (hAD : AssumptionD W near D δD)
    {U : Set (Euc d)} (hU : IsOpen U) (hL : HasLipschitzBoundary U)
    (hUb : Bornology.IsBounded U) (hUD : U ⊆ D)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) :
    (∀ᶠ n in atTop, ∀ a : (W n).V, ∀ᵐ ω ∂MarkovChain.law (W n).kernel a,
      FiniteConductanceNetwork.exitTime ((W n).inner U) ω ≠ ⊤) ∧
    ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ z ∈ U,
      levyProkhorovEDist ((W n).stoppedWalkLaw U (near n z)) (stoppedBrownianLaw U z μ) ≤
        ENNReal.ofReal η := by
  classical
  have hUD' : U ⊆ cthickening δD D := hUD.trans (self_subset_cthickening D)
  refine ⟨eventually_ae_exit W near hAD hUb hUD', ?_⟩
  intro η hη
  have : IsProbabilityMeasure μ := hμ.1
  have hδD : 0 < δD := hAD.2.1
  -- the collar of `U` in the `δ`-neighbourhood of `D`
  have hcollar : HasAmbientCollar U (thickening δD D) := by
    change closure U ⊆ interior (thickening δD D)
    rw [isOpen_thickening.interior_eq]
    exact (closure_mono hUD).trans (closure_subset_thickening hδD D)
  obtain ⟨δ, r, Wset, Q, centers, K, hδ, hr, hrδ, hrη, hWo, hWb, hUW, hWD,
      hQ, hCQ, hcenters, hcover, hballs, hballsQ, hprob⟩ :=
    exists_theoremA_coupling_setup hd hU hUb hL hcollar hμ hη
  have hWsub : Wset ⊆ cthickening δD D := fun x hx =>
    thickening_subset_cthickening δD D (interior_subset (hWD (subset_closure hx)))
  have hballD : ∀ j : centers, closedBall j.val r ⊆ cthickening δD D :=
    fun j => (hballs j.val j.property).trans hWsub
  have hstep := coupling_step_error_budget hη K
  obtain ⟨m, E, hE, hdE, select, hs, δ₀, hδ₀, hmargin, hactive, hdiam, hcouple⟩ :=
    exists_eventual_walkBrownian_coupling_partitions_general hd W near hnear hAD hμ centers hr
      hQ hCQ hballD (fun j => hballsQ j.val j.property) hcover (by positivity : 0 < r / 4)
      hstep.1 K
  have hnone : ∀ i x, select i x = none → x ∉ thickening δ U := by
    intro i x hx hxin
    exact hactive i x (thickening_subset_cthickening δ U hxin) hx
  have hmarginB : ∀ i x j, brownianSelectorForWalk select i x = some j →
      ball x (r / 2) ⊆ ball j.val r := fun i x j => hmargin (i - 1) x j
  have hnoneB : ∀ i x, brownianSelectorForWalk select i x = none →
      x ∉ thickening δ U := fun i x => hnone (i - 1) x
  obtain ⟨q, hq, hwalkBudget, hbrownianBudget, hmiddleBudget, hsmall, htotal⟩ :=
    exists_coupling_stopped_error_budget hη hr hrη
  have hstarts := eventually_near_coupling_starts W near hAD hUb hUD' centers hr
    (lt_min hδ₀ (by positivity : 0 < r / 4))
    (fun z hz => hcover z (self_subset_cthickening U hz))
  filter_upwards [hcouple, hstarts, eventually_ae_exit W near hAD hWb hWsub]
    with n hfailure hnstarts hexW
  intro z hz
  obtain ⟨initial, hvball, hzball, hnear'⟩ := hnstarts z hz
  -- the chain absorbed outside `V[W]`
  have hA : MeasurableSet ((W n).inner Wset) := (W n).measurableSet_inner Wset
  have hexit : ∀ w, ∀ᵐ ω ∂MarkovChain.law (MarkovChain.absorbedKernel (W n).kernel hA) w,
      FiniteConductanceNetwork.exitTime ((W n).inner Wset) ω ≠ ⊤ :=
    fun w => MarkovChain.ae_exit_absorbed_of_free (W n).kernel subset_rfl hA hA w (hexW w)
  have hBA : ∀ j : centers, {w : (W n).V | (w : Euc d) ∈ ball j.val r} ⊆ (W n).inner Wset := by
    intro j w hw
    rw [(W n).inner_of_isOpen hWo]
    exact (ball_subset_closedBall.trans (hballs j.val j.property)) hw
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
  have hfail := hfailure initial (near n z) z hvball hzball (hnear'.trans (min_le_left _ _))
  rw [hstep.2] at hfail
  have hmax : max (2 * r) (2 * (r / 4) + 2 * r) = 2 * (r / 4) + 2 * r :=
    max_eq_right (by linarith)
  have hbuffer : 6 * r + 2 * max (2 * r) (2 * (r / 4) + 2 * r) < δ := by
    rw [hmax]
    linarith
  have hpoint : max (2 * r) (2 * (r / 4) + 2 * r) + r / 4 + 2 * r ≤ 6 * r := by
    rw [hmax]
    linarith
  have hcompare := MarkovChain.levyProkhorov_ball_stopped_laws_le (W n).kernel hd Subtype.val
    ((W n).measurableEmbedding_val_of_isNearestVertex (hnear n)) (fun c : centers => c.val) hr
    hBA hA hexit μ hμ select hs hmargin m E hE hdE initial (near n z) z
    (closedBall_subset_ball (half_lt_self hr) hvball)
    (closedBall_subset_ball (half_lt_self hr) hzball) K P hU (by positivity : 0 < 6 * r)
    hbuffer hnone (fun i _ => hdiam i) (hnear'.trans (min_le_right _ _)) hpoint hfail
    (by simpa only [brownianSkeletonExcursion_flag] using hprobz.1)
    (by simpa only [two_mul, pastedBrownianCurve, Set.preimage_ofPred_eq] using hosc)
    q q q hq hq hwalkBudget hbrownianBudget hmiddleBudget hsmall
  -- the walk stopped at its exit from `V[U]` moves as the chain absorbed outside `V[W]`
  have hUA : (W n).inner U ⊆ (W n).inner Wset := fun w hw => interior_mono hUW hw
  have hlaw : (W n).stoppedWalkLaw U (near n z) =
      (MarkovChain.law (MarkovChain.absorbedKernel (W n).kernel hA) (near n z)).map
        (stoppedPolygonalCurve (Subtype.val : (W n).V → Euc d) (Subtype.val ⁻¹' U)) := by
    rw [NearestNeighbourWalk.stoppedWalkLaw, ← MarkovChain.law_absorbed_map_eq_law_map (W n).kernel
      hUA hA ((W n).measurableSet_inner U)
      (MarkovChain.measurable_stoppedPolygonalCurve measurable_subtype_coe
        ((W n).measurableSet_inner U))
      (MarkovChain.stoppedPolygonalCurve_stoppedWalkPath _ _) (near n z),
      (W n).inner_of_isOpen hU]
    rfl
  rw [hlaw]
  exact hcompare.trans htotal

/-- **Theorem 4.1** for a bounded Lipschitz domain `U ⊆ D`, as printed. -/
theorem theorem41 (hd : 1 ≤ d) (W : ℕ → NearestNeighbourWalk d)
    (near : ∀ n, Euc d → (W n).V) (hnear : ∀ n, (W n).IsNearestVertex (near n))
    {D : Set (Euc d)} {δ : ℝ} (hAD : AssumptionD W near D δ)
    {U : Set (Euc d)} (hU : IsLipschitzDomain U) (hUb : Bornology.IsBounded U) (hUD : U ⊆ D)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) :
    (∀ᶠ n in atTop, ∀ a : (W n).V, ∀ᵐ ω ∂MarkovChain.law (W n).kernel a,
      FiniteConductanceNetwork.exitTime ((W n).inner U) ω ≠ ⊤) ∧
    ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ z ∈ U,
      levyProkhorovEDist ((W n).stoppedWalkLaw U (near n z)) (stoppedBrownianLaw U z μ) ≤
        ENNReal.ofReal η :=
  theorem41_general hd W near hnear hAD hU.1.1 hU.2 hUb hUD hμ

end SpherePackings
