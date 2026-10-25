module

-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/HarmonicMeasureBridge.lean` at commit cf73d6e): its declarations that assume a
-- finite state space or a finite conductance network, for the chain of an arbitrary Markov
-- kernel on a measurable space.
public import BouRabeeGwynne.HarmonicMeasureBridge
public import SpherePackings.General.MarkovChain.Absorbed
public import SpherePackings.General.Walk.DiscreteHarmonicMeasure
public import SpherePackings.General.Walk.StoppedCurveMeasurable

@[expose] public section

/-! General-state-space version of `BouRabeeGwynne.HarmonicMeasureBridge`: the declarations of that file
that assume a finite state space or a finite conductance network. -/

open MeasureTheory ProbabilityTheory
namespace SpherePackings.MarkovChain

open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork BouRabeeGwynne.TrajectoryCoupling
variable {V : Type*}  [MeasurableSpace V] [MeasurableEq V]
variable (κ : Kernel V V) [IsMarkovKernel κ]
omit [MeasurableEq V] in
/-- The endpoint distribution of the actual stopped polygonal walk is its
first-exit harmonic measure, mapped to the spatial embedding. -/
theorem stoppedPolygonalCurve_map_endPoint {d : ℕ} (pos : V → Euc d)
    (A : Set V) (hA : MeasurableSet A) (hpos : Measurable pos) (v : V) :
    ((law (absorbedKernel κ hA) v).map (stoppedPolygonalCurve pos A)).map
        CurveSpace.endPoint =
      (discreteHarmonicMeasure κ A hA v).map pos := by
  rw [Measure.map_map CurveSpace.continuous_endPoint.measurable
    (measurable_stoppedPolygonalCurve hpos hA)]
  rw [discreteHarmonicMeasure,
    Measure.map_map hpos (measurable_exitVertex A hA)]
  congr 1
  funext ω
  exact stoppedPolygonalCurve_endPoint pos A ω

/-- Replacing the boundary data changes its actual exit expectation by at most
the uniform boundary error. This also allows a separate approximation error at
the starting point. The data `g` and the solution `f` are measurable, and the solution is bounded,
which the finite state space used to provide. -/
theorem abs_integral_discreteHarmonicMeasure_sub_le (A : Set V)
    (hA : MeasurableSet A) (hexit : ∀ v, ∀ᵐ ω ∂law (absorbedKernel κ hA) v, exitTime A ω ≠ ⊤)
    {g h f : V → ℝ} (hg : Measurable g) (hfm : Measurable f) (hfb : ∃ C, ∀ w, |f w| ≤ C)
    (hf : SolvesDirichlet κ A Aᶜ h f) {η : ℝ}
    (hboundary : ∀ w, w ∉ A → |g w - h w| ≤ η) (v : V) (target : ℝ) :
    |(∫ w, g w ∂discreteHarmonicMeasure κ A hA v) - target| ≤ η + |f v - target| := by
  obtain ⟨C, hC⟩ := hfb
  have hsol : SolvesDirichlet κ A Aᶜ f f := ⟨hf.1, fun _ _ => rfl⟩
  have hmean : ∫ w, f w ∂discreteHarmonicMeasure κ A hA v = f v :=
    integral_discreteHarmonicMeasure_of_solvesDirichlet κ A hA hexit hfm hfm ⟨C, hC⟩ hsol v
  have hae : ∀ᵐ w ∂discreteHarmonicMeasure κ A hA v, w ∉ A := by
    rw [discreteHarmonicMeasure, ae_map_iff (p := fun w => w ∉ A)
      (measurable_exitVertex A hA).aemeasurable hA.compl]
    filter_upwards [hexit v] with ω hω
    exact exitVertex_not_mem' hω
  have hdiff : ∀ᵐ w ∂discreteHarmonicMeasure κ A hA v, ‖g w - f w‖ ≤ η := by
    filter_upwards [hae] with w hw
    rw [Real.norm_eq_abs, hf.2 w hw]
    exact hboundary w hw
  have hfint : Integrable f (discreteHarmonicMeasure κ A hA v) :=
    (integrable_const C).mono' hfm.aestronglyMeasurable
      (ae_of_all _ fun w => by rw [Real.norm_eq_abs]; exact hC w)
  have hgb : ∀ᵐ w ∂discreteHarmonicMeasure κ A hA v, ‖g w‖ ≤ C + η := by
    filter_upwards [hdiff] with w hw
    rw [Real.norm_eq_abs] at hw ⊢
    calc |g w| = |(g w - f w) + f w| := by rw [sub_add_cancel]
      _ ≤ |g w - f w| + |f w| := abs_add_le _ _
      _ ≤ η + C := add_le_add hw (hC w)
      _ = C + η := add_comm _ _
  have hgint : Integrable g (discreteHarmonicMeasure κ A hA v) :=
    (integrable_const (C + η)).mono' hg.aestronglyMeasurable hgb
  have hsplit : ∫ w, (g w - f w) ∂discreteHarmonicMeasure κ A hA v =
      (∫ w, g w ∂discreteHarmonicMeasure κ A hA v) -
        ∫ w, f w ∂discreteHarmonicMeasure κ A hA v :=
    integral_sub hgint hfint
  have hD : |∫ w, (g w - f w) ∂discreteHarmonicMeasure κ A hA v| ≤ η := by
    have h := norm_integral_le_of_norm_le_const hdiff
    rw [probReal_univ, mul_one, Real.norm_eq_abs] at h
    exact h
  have key : (∫ w, g w ∂discreteHarmonicMeasure κ A hA v) - target =
      (∫ w, (g w - f w) ∂discreteHarmonicMeasure κ A hA v) + (f v - target) := by
    rw [hsplit, hmean]
    ring
  rw [key]
  linarith [abs_add_le (∫ w, (g w - f w) ∂discreteHarmonicMeasure κ A hA v) (f v - target)]

/-- A strict interior Dirichlet approximation bound combines with the boundary
test error without changing either quantifier or normalization. -/
theorem abs_integral_discreteHarmonicMeasure_sub_lt (A : Set V)
    (hA : MeasurableSet A) (hexit : ∀ v, ∀ᵐ ω ∂law (absorbedKernel κ hA) v, exitTime A ω ≠ ⊤)
    {g h f : V → ℝ} (hg : Measurable g) (hfm : Measurable f) (hfb : ∃ C, ∀ w, |f w| ≤ C)
    (hf : SolvesDirichlet κ A Aᶜ h f) {η ρ : ℝ}
    (hboundary : ∀ w, w ∉ A → |g w - h w| ≤ η) (v : V) (target : ℝ)
    (herror : |f v - target| < ρ) :
    |(∫ w, g w ∂discreteHarmonicMeasure κ A hA v) - target| < η + ρ :=
  (abs_integral_discreteHarmonicMeasure_sub_le κ A hA hexit hg hfm hfb hf hboundary
    v target).trans_lt (add_lt_add_of_le_of_lt le_rfl herror)

end SpherePackings.MarkovChain
