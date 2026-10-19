-- Built on Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne (commit cf73d6e).
import SpherePackings.General.Walk.WalkAbsorption
import SpherePackings.General.Walk.DiscreteHarmonicMeasure

/-!
# The free chain and the absorbed chains

Up to its exit from `B`, the chain absorbed outside a set `A ⊇ B` moves as the free chain.  So the
two have the same law for every functional of the path stopped at the exit from `B`: the stopped
path, the exit vertex, and the stopped polygonal curve.
-/

open MeasureTheory ProbabilityTheory Set

namespace SpherePackings.MarkovChain

open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork

variable {V : Type*} [MeasurableSpace V] [MeasurableEq V]
variable (κ : Kernel V V) [IsMarkovKernel κ]

omit [MeasurableEq V] [IsMarkovKernel κ] in
/-- Absorbing outside the whole space does nothing. -/
lemma absorbedKernel_univ : absorbedKernel κ MeasurableSet.univ = κ := by
  ext1 a
  exact absorbedKernel_of_mem κ MeasurableSet.univ (mem_univ a)

/-- The free chain stopped at its exit from `B` is the chain absorbed outside `B`. -/
theorem law_map_stoppedWalkPath {B : Set V} (hB : MeasurableSet B) (v : V) :
    (law κ v).map (stoppedWalkPath B) = law (absorbedKernel κ hB) v := by
  have key : ∀ (κ' : Kernel V V) [IsMarkovKernel κ'], κ' = κ → law κ' v = law κ v := by
    intro κ' _ h
    subst h
    rfl
  rw [← key _ (absorbedKernel_univ κ)]
  exact trajectoryLaw_map_stoppedWalkPath κ (subset_univ B) MeasurableSet.univ hB v

/-- A functional of the path stopped at the exit from `B ⊆ A` has the same law under the free
chain and under the chain absorbed outside `A`. -/
theorem law_absorbed_map_eq_law_map {A B : Set V} (hBA : B ⊆ A) (hA : MeasurableSet A)
    (hB : MeasurableSet B) {X : Type*} [MeasurableSpace X] {F : (ℕ → V) → X}
    (hF : Measurable F) (hstop : ∀ ω, F (stoppedWalkPath B ω) = F ω) (v : V) :
    (law (absorbedKernel κ hA) v).map F = (law κ v).map F := by
  have hFs : F ∘ stoppedWalkPath B = F := funext hstop
  rw [← hFs, ← Measure.map_map hF (measurable_stoppedWalkPath B hB),
    ← Measure.map_map hF (measurable_stoppedWalkPath B hB),
    trajectoryLaw_map_stoppedWalkPath κ hBA hA hB v, law_map_stoppedWalkPath κ hB v]

lemma exitVertex_stoppedWalkPath (B : Set V) (ω : ℕ → V) :
    exitVertex B (stoppedWalkPath B ω) = exitVertex B ω := by
  unfold exitVertex
  rw [exitTime_stoppedWalkPath]
  exact stoppedWalkPath_eq_of_le_exitTime B ω _ (WithTop.coe_untopD_le _ _)

lemma stoppedPolygonalCurve_stoppedWalkPath {d : ℕ} (pos : V → Euc d) (B : Set V)
    (ω : ℕ → V) :
    stoppedPolygonalCurve pos B (stoppedWalkPath B ω) = stoppedPolygonalCurve pos B ω := by
  unfold stoppedPolygonalCurve
  rw [exitTime_stoppedWalkPath, polygonalCurve_congr_prefix pos (fun k hk =>
    stoppedWalkPath_eq_of_le_exitTime B ω k
      ((WithTop.coe_le_coe.mpr hk).trans (WithTop.coe_untopD_le _ _)))]

/-- The discrete harmonic measure is the law of the exit vertex of the free chain. -/
theorem discreteHarmonicMeasure_eq_law_map {B : Set V} (hB : MeasurableSet B) (v : V) :
    discreteHarmonicMeasure κ B hB v = (law κ v).map (exitVertex B) := by
  rw [discreteHarmonicMeasure, ← law_map_stoppedWalkPath κ hB v,
    Measure.map_map (measurable_exitVertex B hB) (measurable_stoppedWalkPath B hB)]
  congr 1
  exact funext (exitVertex_stoppedWalkPath B)

/-- Exit from `B` is almost sure for the chain absorbed outside `A ⊇ B` as soon as it is for the
free chain. -/
theorem ae_exit_absorbed_of_free {A B : Set V} (hBA : B ⊆ A) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (v : V) (h : ∀ᵐ ω ∂law κ v, exitTime B ω ≠ ⊤) :
    ∀ᵐ ω ∂law (absorbedKernel κ hA) v, exitTime B ω ≠ ⊤ := by
  have hm : MeasurableSet {t : WithTop ℕ | t ≠ ⊤} := (measurableSet_singleton ⊤).compl
  have hτ : Measurable (exitTime (V := V) B) := measurable_discreteExitTime hB
  have hlaw := law_absorbed_map_eq_law_map κ hBA hA hB hτ (exitTime_stoppedWalkPath B) v
  have h' : ∀ᵐ t ∂(law κ v).map (exitTime B), t ≠ ⊤ := (ae_map_iff hτ.aemeasurable hm).mpr h
  rw [← hlaw] at h'
  exact (ae_map_iff hτ.aemeasurable hm).mp h'

end SpherePackings.MarkovChain
