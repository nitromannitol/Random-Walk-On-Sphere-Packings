module

public import BouRabeeGwynne.HarmonicNearClosureBrownianExit
public import Mathlib.Topology.TietzeExtension

@[expose] public section

/-!
# Brownian exit representation for boundary-continuous harmonic functions

A function harmonic on a bounded open set `U` and continuous on `closure U` equals the
expectation of its value at the point where Brownian motion first leaves `U`.  This is the
continuum half of "the solution of the Dirichlet problem can be expressed in terms of the
random walk" in the proof of Theorem B(b) (`rw-spheres.tex:1494-1496`).

The proof exhausts `U` by the open sets `{x | 1/(k+1) < infDist x Uᶜ}`.  On the closure of each,
the function is harmonic nearby, so the representation of
`BouRabeeGwynne.standardBrownianLaw_integral_stopped_endPoint_harmonicNearClosure` applies; the
exit points converge to the exit point from `U`, and dominated convergence concludes.
-/

open MeasureTheory Filter Metric Set
open scoped ENNReal NNReal Topology

namespace SpherePackings

open BouRabeeGwynne

variable {d : ℕ}

/-- The inner approximations `{x | 1/(k+1) < infDist x Uᶜ}` of `U`. -/
def innerApprox (U : Set (Euc d)) (k : ℕ) : Set (Euc d) :=
  {x | 1 / ((k : ℝ) + 1) < infDist x Uᶜ}

lemma isOpen_innerApprox (U : Set (Euc d)) (k : ℕ) : IsOpen (innerApprox U k) :=
  isOpen_lt continuous_const (continuous_infDist_pt _)

lemma closure_innerApprox_subset {U : Set (Euc d)} (k : ℕ) :
    closure (innerApprox U k) ⊆ U := by
  intro x hx
  have hle : 1 / ((k : ℝ) + 1) ≤ infDist x Uᶜ :=
    closure_lt_subset_le continuous_const (continuous_infDist_pt _) hx
  by_contra hxU
  have hzero : infDist x Uᶜ = 0 := infDist_zero_of_mem hxU
  have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  linarith

lemma innerApprox_subset {U : Set (Euc d)} (k : ℕ) : innerApprox U k ⊆ U :=
  subset_closure.trans (closure_innerApprox_subset k)

lemma infDist_eq_of_mem_frontier_innerApprox {U : Set (Euc d)} {k : ℕ} {x : Euc d}
    (hx : x ∈ frontier (innerApprox U k)) : infDist x Uᶜ = 1 / ((k : ℝ) + 1) := by
  have h1 : 1 / ((k : ℝ) + 1) ≤ infDist x Uᶜ :=
    closure_lt_subset_le continuous_const (continuous_infDist_pt _) hx.1
  have h2 : x ∉ innerApprox U k := by
    intro hin
    exact hx.2 ((isOpen_innerApprox U k).interior_eq.symm ▸ hin)
  exact le_antisymm (not_lt.mp h2) h1

/-- A point of an open set eventually lies in its inner approximations. -/
lemma eventually_mem_innerApprox {U : Set (Euc d)} (hU : IsOpen U) (hUc : Uᶜ.Nonempty)
    {z : Euc d} (hz : z ∈ U) : ∀ᶠ k in atTop, z ∈ innerApprox U k := by
  have hpos : 0 < infDist z Uᶜ :=
    (hU.isClosed_compl.notMem_iff_infDist_pos hUc).mp (fun h => h hz)
  have hlim : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  exact (hlim.eventually (gt_mem_nhds hpos)).mono fun _ hk => hk

/-- The exit time from a smaller set is smaller. -/
lemma continuousExitTime_mono_set {V W : Set (Euc d)} (hVW : V ⊆ W) (z : Euc d)
    (ω : BrownianPath d) : continuousExitTime V z ω ≤ continuousExitTime W z ω :=
  le_iInf fun t => continuousExitTime_le_of_not_mem fun h => t.2 (hVW h)

lemma innerApprox_mono (U : Set (Euc d)) : Monotone (innerApprox U) := by
  intro k m hkm x hx
  have hle : 1 / ((m : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hkm 1)
  exact lt_of_le_of_lt hle hx

/-- The exit points from the inner approximations converge to the exit point from `U`. -/
theorem tendsto_exitPoint_innerApprox {U : Set (Euc d)} (hU : IsOpen U) (hUc : Uᶜ.Nonempty)
    {z : Euc d} {ω : BrownianPath d} (hz : z ∈ U) (h0 : ω 0 = 0)
    (hfin : continuousExitTime U z ω ≠ ∞) :
    Tendsto (fun k => z + ω (continuousExitTime (innerApprox U k) z ω).toNNReal) atTop
      (𝓝 (z + ω (continuousExitTime U z ω).toNNReal)) := by
  set τ := continuousExitTime U z ω with hτ
  let t : ℕ → ℝ≥0 := fun k => (continuousExitTime (innerApprox U k) z ω).toNNReal
  have hle : ∀ k, continuousExitTime (innerApprox U k) z ω ≤ τ := fun k =>
    continuousExitTime_mono_set (innerApprox_subset k) z ω
  have hfin_k : ∀ k, continuousExitTime (innerApprox U k) z ω ≠ ∞ := fun k =>
    ne_top_of_le_ne_top hfin (hle k)
  have ht_le : ∀ k, t k ≤ τ.toNNReal := fun k => ENNReal.toNNReal_mono hfin (hle k)
  have hmono : Monotone t := by
    intro k m hkm
    exact ENNReal.toNNReal_mono (hfin_k m)
      (continuousExitTime_mono_set (innerApprox_mono U hkm) z ω)
  have hbdd : BddAbove (range t) := ⟨τ.toNNReal, by rintro _ ⟨k, rfl⟩; exact ht_le k⟩
  have htend : Tendsto t atTop (𝓝 (⨆ k, t k)) := tendsto_atTop_ciSup hmono hbdd
  have hpath : Tendsto (fun k => z + ω (t k)) atTop (𝓝 (z + ω (⨆ k, t k))) :=
    tendsto_const_nhds.add ((ω.continuous.tendsto _).comp htend)
  -- The limit point lies outside `U`.
  have hdist : Tendsto (fun k => infDist (z + ω (t k)) Uᶜ) atTop
      (𝓝 (infDist (z + ω (⨆ k, t k)) Uᶜ)) :=
    ((continuous_infDist_pt _).tendsto _).comp hpath
  have hdist' : ∀ᶠ k in atTop, infDist (z + ω (t k)) Uᶜ = 1 / ((k : ℝ) + 1) := by
    filter_upwards [eventually_mem_innerApprox hU hUc hz] with k hk
    have hstart : z + ω 0 ∈ innerApprox U k := by simpa only [h0, add_zero] using hk
    exact infDist_eq_of_mem_frontier_innerApprox
      (continuousExitTime_mem_frontier (isOpen_innerApprox U k) hstart (hfin_k k))
  have hzero : infDist (z + ω (⨆ k, t k)) Uᶜ = 0 := by
    have hlim : Tendsto (fun k => infDist (z + ω (t k)) Uᶜ) atTop (𝓝 0) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat).congr' (hdist'.mono fun _ hk => hk.symm)
    exact tendsto_nhds_unique hdist hlim
  have hout : z + ω (⨆ k, t k) ∉ U := by
    intro hin
    exact ((hU.isClosed_compl.mem_iff_infDist_zero hUc).mpr hzero) hin
  have hsup : (⨆ k, t k) = τ.toNNReal := by
    apply le_antisymm (ciSup_le ht_le)
    have := continuousExitTime_le_of_not_mem hout
    rw [← hτ] at this
    exact (ENNReal.toNNReal_le_toNNReal hfin ENNReal.coe_ne_top).mpr this |>.trans_eq
      (ENNReal.toNNReal_coe _)
  rw [hsup] at hpath
  exact hpath

/-- **Brownian representation for boundary-continuous data.** A function harmonic on a bounded
open set `U` and continuous on `closure U` is the mean of its values at the Brownian exit point
from `U`. -/
theorem integral_stoppedBrownian_endPoint_of_continuousOn (hd : 1 ≤ d)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {U : Set (Euc d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {h : Euc d → ℝ} (hh : IsHarmonicOn h U) (hc : ContinuousOn h (closure U))
    {z : Euc d} (hz : z ∈ U) :
    (∫ x, h x ∂((stoppedBrownianLaw U z μ).map CurveSpace.endPoint)) = h z := by
  have : IsProbabilityMeasure μ := hμ.1
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hUc : Uᶜ.Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hne
    exact NormedSpace.unbounded_univ ℝ (Euc d) (hne ▸ hUb)
  -- A continuous extension of `h` from `closure U`.
  obtain ⟨H, hH⟩ := ContinuousMap.exists_restrict_eq isClosed_closure
    (⟨fun x : closure U => h x, continuousOn_iff_continuous_domRestrict.mp hc⟩ : C(closure U, ℝ))
  have hHeq : ∀ x ∈ closure U, H x = h x := fun x hx =>
    congrArg (fun f : C(closure U, ℝ) => f ⟨x, hx⟩) hH
  obtain ⟨M, hM⟩ := hUb.isCompact_closure.exists_bound_of_continuousOn H.continuous.continuousOn
  -- Integrals against exit-point laws, rewritten on path space.
  have hend : ∀ V : Set (Euc d), IsOpen V →
      Measurable fun ω => CurveSpace.endPoint (stoppedBrownianCurve V z ω) := fun V hV =>
    CurveSpace.continuous_endPoint.measurable.comp (measurable_stoppedBrownianCurve hV z)
  have hrepr : ∀ V : Set (Euc d), IsOpen V → Bornology.IsBounded V → z ∈ V → V ⊆ closure U →
      (∫ x, h x ∂((stoppedBrownianLaw V z μ).map CurveSpace.endPoint)) =
        ∫ ω, H (z + ω (continuousExitTime V z ω).toNNReal) ∂μ := by
    intro V hV hVb hzV hVU
    have hae : h =ᵐ[(stoppedBrownianLaw V z μ).map CurveSpace.endPoint] H := by
      filter_upwards [standardBrownianLaw_stopped_endPoint_ae_mem_frontier hd hμ hV hVb hzV]
        with x hx
      have hxU : x ∈ closure U := by
        simpa only [closure_closure] using closure_mono hVU (frontier_subset_closure hx)
      exact (hHeq x hxU).symm
    rw [integral_congr_ae hae, stoppedBrownianLaw,
      Measure.map_map CurveSpace.continuous_endPoint.measurable
        (measurable_stoppedBrownianCurve hV z),
      integral_map (CurveSpace.continuous_endPoint.measurable.comp
        (measurable_stoppedBrownianCurve hV z)).aemeasurable H.continuous.aestronglyMeasurable]
    simp only [Function.comp_def, stoppedBrownianCurve_endPoint]
  -- The inner approximations.
  have hinner : ∀ᶠ k in atTop,
      ∫ ω, H (z + ω (continuousExitTime (innerApprox U k) z ω).toNNReal) ∂μ = h z := by
    filter_upwards [eventually_mem_innerApprox hU hUc hz] with k hk
    rw [← hrepr (innerApprox U k) (isOpen_innerApprox U k)
      (hUb.subset (innerApprox_subset k)) hk ((innerApprox_subset k).trans subset_closure)]
    exact standardBrownianLaw_integral_stopped_endPoint_harmonicNearClosure hd hμ
      (isOpen_innerApprox U k) (hUb.subset (innerApprox_subset k))
      ⟨U, hU, closure_innerApprox_subset k, hh⟩ hk
  -- Dominated convergence.
  have hbound : ∀ k, ∀ᵐ ω ∂μ,
      ‖H (z + ω (continuousExitTime (innerApprox U k) z ω).toNNReal)‖ ≤ M := by
    intro k
    filter_upwards [standardBrownianLaw_eval_zero_ae hμ,
      standardBrownianLaw_ae_finiteExit hd hμ hUb z] with ω h0 hfin
    apply hM
    have hfin_k : continuousExitTime (innerApprox U k) z ω ≠ ∞ :=
      ne_top_of_le_ne_top hfin (continuousExitTime_mono_set (innerApprox_subset k) z ω)
    by_cases hzk : z ∈ innerApprox U k
    · have hstart : z + ω 0 ∈ innerApprox U k := by simpa only [h0, add_zero] using hzk
      exact subset_closure (closure_innerApprox_subset k
        (frontier_subset_closure
          (continuousExitTime_mem_frontier (isOpen_innerApprox U k) hstart hfin_k)))
    · have hstart : z + ω 0 ∉ innerApprox U k := by simpa only [h0, add_zero] using hzk
      rw [continuousExitTime_eq_zero_of_not_mem hstart]
      simpa only [ENNReal.toNNReal_zero, h0, add_zero] using subset_closure hz
  have hmeas : ∀ k, AEStronglyMeasurable
      (fun ω => H (z + ω (continuousExitTime (innerApprox U k) z ω).toNNReal)) μ := by
    intro k
    have := (H.continuous.measurable.comp (hend (innerApprox U k) (isOpen_innerApprox U k)))
    simpa only [Function.comp_def, stoppedBrownianCurve_endPoint] using this.aestronglyMeasurable
  have hlim : ∀ᵐ ω ∂μ, Tendsto
      (fun k => H (z + ω (continuousExitTime (innerApprox U k) z ω).toNNReal)) atTop
      (𝓝 (H (z + ω (continuousExitTime U z ω).toNNReal))) := by
    filter_upwards [standardBrownianLaw_eval_zero_ae hμ,
      standardBrownianLaw_ae_finiteExit hd hμ hUb z] with ω h0 hfin
    exact (H.continuous.tendsto _).comp (tendsto_exitPoint_innerApprox hU hUc hz h0 hfin)
  have hDCT := tendsto_integral_of_dominated_convergence (fun _ => M) hmeas
    (integrable_const M) hbound hlim
  rw [hrepr U hU hUb hz subset_closure]
  exact tendsto_nhds_unique hDCT (tendsto_const_nhds.congr' (hinner.mono fun _ hk => hk.symm))

end SpherePackings
