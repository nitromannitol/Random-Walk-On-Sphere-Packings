-- Built on Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne (commit cf73d6e).
import SpherePackings.Support.Section4General.BallExitInputs
import SpherePackings.General.Walk.StoppedCurveMeasurable

/-!
# The stopped walk law of Theorem 4.1

For a nearest-neighbour walk on a graph in `ℝ^d` and a set `U`, the law of the walk started at a
vertex `a`, linearly interpolated and stopped at its first exit from `V[U]`, as a law on curves
modulo time parametrization (`rw-spheres.tex:1481-1488`).  On paths that never exit, the stopped
curve is the constant curve at the start (a convention; under Assumption D, for bounded `U` in the
`δ`-neighbourhood of `D`, the walk eventually exits `V[U]` almost surely, `eventually_ae_exit`).
-/

open MeasureTheory Metric Filter Set
open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork

namespace SpherePackings

variable {d : ℕ}

namespace NearestNeighbourWalk

variable (W : NearestNeighbourWalk d)

/-- The law of the walk from `a`, interpolated and stopped at its first exit from `V[U]`. -/
noncomputable def stoppedWalkLaw (U : Set (Euc d)) (a : W.V) : Measure (CurveSpace d) :=
  (MarkovChain.law W.kernel a).map (stoppedPolygonalCurve (Subtype.val : W.V → Euc d) (W.inner U))

instance stoppedWalkLaw_isProbabilityMeasure (U : Set (Euc d)) (a : W.V) :
    IsProbabilityMeasure (W.stoppedWalkLaw U a) :=
  MarkovChain.stoppedPolygonalCurve_map_isProbabilityMeasure measurable_subtype_coe
    (W.measurableSet_inner U) _

end NearestNeighbourWalk

/-- Under Assumption D, eventually the walk started at any vertex of a bounded `U` inside the
closed `δ`-neighbourhood of `D` exits `V[U]` almost surely. -/
theorem eventually_ae_exit (W : ℕ → NearestNeighbourWalk d) (near : ∀ n, Euc d → (W n).V)
    {D : Set (Euc d)} {δ : ℝ} (hAD : AssumptionD W near D δ) {U : Set (Euc d)}
    (hUb : Bornology.IsBounded U) (hUD : U ⊆ cthickening δ D) :
    ∀ᶠ n in atTop, ∀ a : (W n).V, ∀ᵐ ω ∂MarkovChain.law (W n).kernel a,
      exitTime ((W n).inner U) ω ≠ ⊤ := by
  rcases U.eq_empty_or_nonempty with rfl | ⟨c, hc⟩
  · refine Filter.Eventually.of_forall fun n a => Filter.Eventually.of_forall fun ω => ?_
    rw [exitTime_eq_zero_of_not_mem (by simp [NearestNeighbourWalk.inner])]
    exact WithTop.zero_ne_top
  obtain ⟨r, hr, hUr⟩ := hUb.subset_ball_lt 0 c
  have hcD : c ∈ cthickening δ D := hUD hc
  obtain ⟨-, -, hAD'⟩ := hAD
  obtain ⟨-, hdir⟩ := hAD' r hr c hcD
  have hconv := hdir (fun _ => 0)
    ⟨univ, isOpen_univ, subset_univ _, ⟨contDiffOn_const, fun x _ => by simp⟩⟩ 1 one_pos
  filter_upwards [hconv] with n hn a
  set B := closedBall c r ∩ cthickening δ D
  have hsub : (W n).inner U ⊆ (W n).inner B := by
    intro v hv
    have hv' : (v : Euc d) ∈ interior U := hv
    simp only [NearestNeighbourWalk.inner, mem_ofPred_eq, B, interior_inter]
    exact ⟨interior_mono (hUr.trans ball_subset_closedBall) hv',
      interior_mono hUD hv'⟩
  by_cases ha : a ∈ (W n).inner U
  · have h0 := MarkovChain.survival_eq_zero_of_forall_solution_bounded (W n).kernel
      ((W n).measurableSet_inner B) ((W n).disjoint_inner_boundary B) measurable_const le_rfl
      (fun _ => by simp) hn (hsub ha)
    rw [MarkovChain.survival, measureReal_eq_zero_iff] at h0
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) h0
    simp only [not_not, mem_ofPred_eq] at hω ⊢
    rw [exitTime_eq_top_iff] at hω ⊢
    exact fun k => hsub (hω k)
  · filter_upwards [MarkovChain.law_ae_start_not_mem (W n).kernel ((W n).measurableSet_inner U) ha]
      with ω hω
    rw [exitTime_eq_zero_of_not_mem hω]
    exact WithTop.zero_ne_top

end SpherePackings
