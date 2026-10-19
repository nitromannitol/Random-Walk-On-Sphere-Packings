-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/StoppedCurveMeasurable.lean` at commit cf73d6e): its declarations that assume a
-- finite state space or a finite conductance network, for the chain of an arbitrary Markov
-- kernel on a measurable space.
import BouRabeeGwynne.StoppedCurveMeasurable
import SpherePackings.General.MarkovChain.Absorbed
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-! General-state-space version of `BouRabeeGwynne.StoppedCurveMeasurable`: the declarations of that file
that assume a finite state space or a finite conductance network. -/

open scoped BigOperators unitInterval
open MeasureTheory
namespace SpherePackings.MarkovChain

open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork BouRabeeGwynne.TrajectoryCoupling
variable {d : ℕ} {V : Type*} [MeasurableSpace V]

/-- A fixed-duration curve class is a measurable function of the path, for a measurable position
map. -/
lemma measurable_curveProjection_polygonalCurve {pos : V → Euc d} (hpos : Measurable pos)
    (m : ℕ) : Measurable (fun ω : ℕ → V => CurveSpace.project (polygonalCurve pos ω m)) := by
  have h : Measurable (fun ω : ℕ → V => polygonalCurve pos ω m) := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    change Measurable (fun ω : ℕ → V => pos (ω 0) + ∑ k ∈ Finset.range m,
      max (0 : ℝ) (min 1 ((m : ℝ) * (t : ℝ) - (k : ℝ))) • (pos (ω (k + 1)) - pos (ω k)))
    have hk : ∀ k, Measurable (fun ω : ℕ → V => pos (ω k)) := fun k =>
      hpos.comp (measurable_pi_apply k)
    fun_prop
  exact CurveSpace.continuous_project.measurable.comp h

/-- The first exit from a measurable set is measurable, also on never-exiting paths. -/
lemma measurable_discreteExitTime {A : Set V} (hA : MeasurableSet A) :
    Measurable (FiniteConductanceNetwork.exitTime A) :=
  measurable_exitTime hA

/-- The duration used by the total stopped interpolation is measurable. -/
lemma measurable_stoppedPolygonalDuration {A : Set V} (hA : MeasurableSet A) :
    Measurable (fun ω : ℕ → V => (FiniteConductanceNetwork.exitTime A ω).untopD 0) :=
  (measurable_of_countable (fun n : WithTop ℕ => n.untopD 0)).comp
    (measurable_discreteExitTime hA)

/-- The stopped polygonal interpolation into the curve space is measurable.  No almost-sure
finite-exit hypothesis is required. -/
lemma measurable_stoppedPolygonalCurve {pos : V → Euc d} (hpos : Measurable pos) {A : Set V}
    (hA : MeasurableSet A) : Measurable (stoppedPolygonalCurve pos A) := by
  have hf : Measurable (fun p : (ℕ → V) × ℕ =>
      CurveSpace.project (polygonalCurve pos p.1 p.2)) :=
    measurable_from_prod_countable_left (measurable_curveProjection_polygonalCurve hpos)
  exact hf.comp (measurable_id.prodMk (measurable_stoppedPolygonalDuration hA))

lemma aemeasurable_stoppedPolygonalCurve {pos : V → Euc d} (hpos : Measurable pos) {A : Set V}
    (hA : MeasurableSet A) (μ : Measure (ℕ → V)) : AEMeasurable (stoppedPolygonalCurve pos A) μ :=
  (measurable_stoppedPolygonalCurve hpos hA).aemeasurable

/-- The stopped-curve pushforward of a probability law is a probability law. -/
lemma stoppedPolygonalCurve_map_isProbabilityMeasure {pos : V → Euc d} (hpos : Measurable pos)
    {A : Set V} (hA : MeasurableSet A) (μ : Measure (ℕ → V)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (μ.map (stoppedPolygonalCurve pos A)) :=
  (Measure.isProbabilityMeasure_map_iff
    (aemeasurable_stoppedPolygonalCurve hpos hA μ)).mpr inferInstance

end SpherePackings.MarkovChain
