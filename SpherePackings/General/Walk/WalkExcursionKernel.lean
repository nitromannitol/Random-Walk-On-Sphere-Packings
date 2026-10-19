-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/WalkExcursionKernel.lean` at commit cf73d6e): its declarations that assume a
-- finite state space or a finite conductance network, for the chain of an arbitrary Markov
-- kernel on a measurable space.
import BouRabeeGwynne.WalkExcursionKernel
import SpherePackings.General.MarkovChain.Absorbed
import SpherePackings.General.Walk.DiscreteHarmonicMeasure
import SpherePackings.General.Walk.HarmonicMeasureBridge
import SpherePackings.General.Walk.StoppedCurveMeasurable

/-! General-state-space version of `BouRabeeGwynne.WalkExcursionKernel`: the declarations of that file
that assume a finite state space or a finite conductance network. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators unitInterval
namespace SpherePackings.MarkovChain

open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork BouRabeeGwynne.TrajectoryCoupling
variable {d : ℕ} {V : Type*} [MeasurableSpace V] [MeasurableEq V]

omit [MeasurableEq V] in
/-- Fixed-duration interpolation is measurable into the space of full
continuous paths, before passing to the Fréchet quotient. -/
lemma measurable_polygonalCurve (pos : V → Euc d) (hpos : Measurable pos) (m : ℕ) :
    Measurable (fun ω : ℕ → V => polygonalCurve pos ω m) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  have hk : ∀ k, Measurable (fun ω : ℕ → V => pos (ω k)) := fun k =>
    hpos.comp (measurable_pi_apply k)
  change Measurable (fun ω : ℕ → V => pos (ω 0) + ∑ k ∈ Finset.range m,
    max (0 : ℝ) (min 1 ((m : ℝ) * (t : ℝ) - (k : ℝ))) •
      (pos (ω (k + 1)) - pos (ω k)))
  fun_prop

omit [MeasurableEq V] in
lemma measurable_stoppedPolygonalRepresentative (pos : V → Euc d) (A : Set V)
    (hA : MeasurableSet A) (hpos : Measurable pos) :
    Measurable (stoppedPolygonalRepresentative pos A) := by
  have hf : Measurable (fun p : (ℕ → V) × ℕ => polygonalCurve pos p.1 p.2) :=
    measurable_from_prod_countable_left (measurable_polygonalCurve pos hpos)
  exact hf.comp (measurable_id.prodMk (measurable_stoppedPolygonalDuration hA))

variable (κ : Kernel V V) [IsMarkovKernel κ]
/-- The actual stopped walk excursion kernel, constructed from the genuine
trajectory law; no lifting or disintegration of endpoint measures is used. -/
noncomputable def walkExcursionKernel (pos : V → Euc d) (A : Set V)
    (hA : MeasurableSet A) (hpos : Measurable pos) : Kernel V C(unitInterval, Euc d) where
  toFun v := (law (absorbedKernel κ hA) v).map (stoppedPolygonalRepresentative pos A)
  measurable' := by
    have hlaw : Measurable fun v => law (absorbedKernel κ hA) v := by
      simp only [← pathKernel_apply]
      exact (pathKernel (absorbedKernel κ hA)).measurable
    exact (Measure.measurable_map _
      (measurable_stoppedPolygonalRepresentative pos A hA hpos)).comp hlaw

omit [MeasurableEq V] in
lemma walkExcursionKernel_apply (pos : V → Euc d) (A : Set V)
    (hA : MeasurableSet A) (hpos : Measurable pos) (v : V) :
    walkExcursionKernel κ pos A hA hpos v =
      (law (absorbedKernel κ hA) v).map (stoppedPolygonalRepresentative pos A) := rfl

instance walkExcursionKernel_isMarkov (pos : V → Euc d) (A : Set V)
    (hA : MeasurableSet A) (hpos : Measurable pos) :
    IsMarkovKernel (walkExcursionKernel κ pos A hA hpos) where
  isProbabilityMeasure _ :=
    (Measure.isProbabilityMeasure_map_iff
      (measurable_stoppedPolygonalRepresentative pos A hA hpos).aemeasurable).mpr inferInstance

lemma walkExcursionKernel_ae_start (pos : V → Euc d) (A : Set V)
    (hA : MeasurableSet A) (hpos : Measurable pos) (v : V) :
    ∀ᵐ c ∂walkExcursionKernel κ pos A hA hpos v, c 0 = pos v := by
  rw [walkExcursionKernel_apply κ]
  apply (ae_map_iff (measurable_stoppedPolygonalRepresentative pos A hA hpos).aemeasurable
    (measurableSet_eq_fun (ContinuousMap.measurable_eval 0) measurable_const)).mpr
  filter_upwards [law_ae_start (absorbedKernel κ hA) v] with ω hω
  simp only [stoppedPolygonalRepresentative_start, hω]

/-- The whole sampled excursion stays in a closed convex set containing all the
embedded states `pos w`, including the exit vertices. -/
lemma walkExcursionKernel_ae_mem_convex (pos : V → Euc d) (A : Set V)
    (hA : MeasurableSet A) (hpos : Measurable pos) (v : V)
    {S : Set (Euc d)} (hS : Convex ℝ S) (hclosed : IsClosed S)
    (hvertices : ∀ w, pos w ∈ S) :
    ∀ᵐ c ∂walkExcursionKernel κ pos A hA hpos v, ∀ t, c t ∈ S := by
  have hset : MeasurableSet {c : C(unitInterval, Euc d) | ∀ t, c t ∈ S} := by
    simp only [Set.ofPred_forall]
    exact (isClosed_iInter fun t => hclosed.preimage (continuous_eval_const t)).measurableSet
  rw [walkExcursionKernel_apply κ]
  apply (ae_map_iff (measurable_stoppedPolygonalRepresentative pos A hA hpos).aemeasurable hset).mpr
  exact Filter.Eventually.of_forall fun ω t =>
    polygonalCurve_mem_of_convex pos ω hS hvertices _ t

omit [MeasurableEq V] in
/-- Projecting the full excursion gives exactly the original stopped curve law. -/
lemma walkExcursionKernel_project (pos : V → Euc d) (A : Set V)
    (hA : MeasurableSet A) (hpos : Measurable pos) (v : V) :
    (walkExcursionKernel κ pos A hA hpos v).map CurveSpace.project =
      (law (absorbedKernel κ hA) v).map (stoppedPolygonalCurve pos A) := by
  rw [walkExcursionKernel_apply κ,
    Measure.map_map CurveSpace.continuous_project.measurable
      (measurable_stoppedPolygonalRepresentative pos A hA hpos)]
  rfl

omit [MeasurableEq V] in
/-- Its full-path endpoint law is the actual spatial harmonic measure. -/
lemma walkExcursionKernel_endPoint (pos : V → Euc d) (A : Set V)
    (hA : MeasurableSet A) (hpos : Measurable pos) (v : V) :
    (walkExcursionKernel κ pos A hA hpos v).map (fun c => c 1) =
      (discreteHarmonicMeasure κ A hA v).map pos := by
  have h := stoppedPolygonalCurve_map_endPoint κ pos A hA hpos v
  rw [← walkExcursionKernel_project κ pos A hA hpos v,
    Measure.map_map CurveSpace.continuous_endPoint.measurable
      CurveSpace.continuous_project.measurable] at h
  exact h

end SpherePackings.MarkovChain
