module

/- Nonvacuity examples written by the independent reviewer (Claude Haiku 5.5) of audit batch 06;
   see `AUDIT.md`. They show that the hypothesis bundles named below can hold together. -/
public import BouRabeeGwynne.WalkBrownianFailure
public import BouRabeeGwynne.EuclideanWienerLaw
public import BouRabeeGwynne.BrownianExcursionKernel
public import BouRabeeGwynne.ContinuousExitProperties

@[expose] public section

-- The reviewer's examples, kept as written.
set_option linter.unusedVariables false
set_option linter.deprecated false

/-! Nonvacuity witness for the hypothesis bundle of
`walkBrownianJointLaw_firstFailure_le` in the one-stage case `k = 0`:
one walk vertex with no edges, one Brownian domain `ball 0 1`, one cell
`closedBall 0 1` that contains the whole closure of the domain, and the
standard Brownian law `euclideanWienerLaw 1`. The stage-`0` approximation
hypothesis holds with both masses equal to `1`. The `herror` bundle (`k ≥ 1`)
is not witnessed here. -/

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace SpherePackings.Audit.Nonvacuity06
open BouRabeeGwynne
open BouRabeeGwynne.FiniteConductanceNetwork

def N1 : FiniteConductanceNetwork (Fin 1) where
  a := fun _ _ => 0
  symm := fun _ _ => rfl
  nonneg := fun _ _ => le_rfl
  loop_zero := fun _ => rfl

def posOne : Fin 1 → Euc 1 := fun _ => 0
def BOne : Unit → Set (Fin 1) := fun _ => ∅
abbrev UOne : Unit → Set (Euc 1) := fun _ => Metric.ball 0 1
instance : MeasurableSpace (Option Unit) := ⊤

instance : MeasurableSingletonClass (Option Unit) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

def selOne : ℕ → Euc 1 → Option Unit := fun _ _ => none
abbrev mOne : ℕ → ℕ := fun _ => 1
def EOne : ∀ n, Fin (mOne n) → Set (Euc 1) := fun _ _ => Metric.closedBall 0 1
def choiceOne : ∀ n, Fin (mOne n) → Option Unit := fun _ _ => none

theorem hinj_one : Function.Injective posOne := fun a b _ => Subsingleton.elim a b

theorem hB_one : ∀ j v, v ∈ BOne j → 0 < N1.totalConductance v := by
  intro j v hv
  simp [BOne] at hv

theorem hU_one : ∀ j, IsOpen (UOne j) := fun _ => Metric.isOpen_ball

theorem hUb_one : ∀ j, Bornology.IsBounded (UOne j) := fun _ => Metric.isBounded_ball

theorem hs_one : ∀ n, Measurable (selOne n) := fun _ => measurable_const

theorem hE_one : ∀ n i, MeasurableSet (EOne n i) := fun _ _ => measurableSet_closedBall

theorem hdE_one : ∀ n, Pairwise (fun i j => Disjoint (EOne n i) (EOne n j)) := by
  intro n i j hij
  exact absurd (Subsingleton.elim i j) hij

theorem hselect_one : ∀ n, selOne n = cellSelector (EOne n) (choiceOne n) := by
  intro n
  funext x
  unfold cellSelector
  cases cellLabel (EOne n) x <;> rfl

theorem hdiam_one : ∀ n ≤ 0, ∀ i, ∀ x ∈ EOne n i, ∀ y ∈ EOne n i, dist x y ≤ 2 := by
  intro n _ i x hx y hy
  have hx' : dist x 0 ≤ 1 := mem_closedBall.mp hx
  have hy' : dist y 0 ≤ 1 := mem_closedBall.mp hy
  linarith [dist_triangle_right x y 0]

theorem hcover_one : ∀ n ≤ 0, ∀ j, closure (UOne j) ⊆ ⋃ i, EOne n i := by
  intro n _ j
  rw [show UOne j = Metric.ball 0 1 from rfl, closure_ball (0 : Euc 1) one_ne_zero]
  intro x hx
  exact Set.mem_iUnion.mpr ⟨0, hx⟩

theorem hinit_one :
    ∀ i : Fin (mOne 0),
      |((Measure.map posOne (N1.discreteHarmonicMeasure (BOne ()) (hB_one ()) 0)) (EOne 0 i)).toReal
        - ((Measure.map CurveSpace.endPoint
            (stoppedBrownianLaw (UOne ()) 0 (euclideanWienerLaw 1))) (EOne 0 i)).toReal|
        ≤ (1 / 2 : ℝ) / ((mOne 0 : ℝ) + 1) := by
  have : IsProbabilityMeasure (euclideanWienerLaw 1) :=
    (isStandardBrownianLaw_euclideanWienerLaw 1).1
  intro i
  have hwalk : (Measure.map posOne (N1.discreteHarmonicMeasure (BOne ()) (hB_one ()) 0))
      (EOne 0 i) = 1 := by
    rw [Measure.map_apply (measurable_of_finite posOne) (hE_one 0 i)]
    have hpre : posOne ⁻¹' (EOne 0 i) = univ := by
      apply eq_univ_of_forall
      intro v
      simp [posOne, EOne]
    rw [hpre, measure_univ]
  have hae : ∀ᵐ ω ∂(euclideanWienerLaw 1),
      CurveSpace.endPoint (stoppedBrownianCurve (UOne ()) 0 ω) ∈ EOne 0 i := by
    have key : ∀ᵐ ω ∂(euclideanWienerLaw 1),
        ∀ t, stoppedBrownianRepresentative (UOne ()) 0 ω t ∈ closure (UOne ()) :=
      ae_of_ae_map (measurable_stoppedBrownianRepresentative (Metric.isOpen_ball : IsOpen (Metric.ball (0 : Euc 1) 1)) 0).aemeasurable
        (brownianExcursionKernel_ae_mem_closure le_rfl Metric.isOpen_ball Metric.isBounded_ball
          (euclideanWienerLaw 1) (isStandardBrownianLaw_euclideanWienerLaw 1)
          (mem_ball_self one_pos))
    filter_upwards [key] with ω hω
    have h1 : stoppedBrownianRepresentative (UOne ()) 0 ω 1 ∈ Metric.closedBall (0 : Euc 1) 1 := by
      have h2 := hω 1
      rwa [show UOne () = Metric.ball 0 1 from rfl, closure_ball (0 : Euc 1) one_ne_zero] at h2
    exact h1
  have hbrown : (Measure.map CurveSpace.endPoint
      (stoppedBrownianLaw (UOne ()) 0 (euclideanWienerLaw 1))) (EOne 0 i) = 1 := by
    rw [stoppedBrownianLaw, Measure.map_map CurveSpace.continuous_endPoint.measurable
      (measurable_stoppedBrownianCurve (Metric.isOpen_ball : IsOpen (Metric.ball (0 : Euc 1) 1)) 0),
      Measure.map_apply (CurveSpace.continuous_endPoint.measurable.comp
        (measurable_stoppedBrownianCurve (Metric.isOpen_ball : IsOpen (Metric.ball (0 : Euc 1) 1)) 0)) (hE_one 0 i)]
    have hset : (CurveSpace.endPoint ∘ stoppedBrownianCurve (UOne ()) 0) ⁻¹' EOne 0 i
        =ᵐ[euclideanWienerLaw 1] (univ : Set (BrownianPath 1)) := by
      refine Filter.eventuallyEqSet_iff.2 ?_
      filter_upwards [hae] with ω hω
      simp only [Function.comp_apply, Set.mem_preimage, Set.mem_univ, iff_true]
      exact hω
    rw [measure_congr hset, measure_univ]
  rw [hwalk, hbrown]
  norm_num

theorem firstFailure_bundle_witness : True := by
  have : IsProbabilityMeasure (euclideanWienerLaw 1) :=
    (isStandardBrownianLaw_euclideanWienerLaw 1).1
  have h := FiniteConductanceNetwork.walkBrownianJointLaw_firstFailure_le N1 (le_refl (1 : ℕ))
    posOne hinj_one BOne hB_one UOne hU_one hUb_one (euclideanWienerLaw 1)
    (isStandardBrownianLaw_euclideanWienerLaw 1) selOne hs_one mOne EOne hE_one hdE_one
    choiceOne hselect_one 0 (b := 1 / 2) (by norm_num) hdiam_one
    (fun n hn => absurd hn (Nat.not_lt_zero n)) hcover_one
    (fun n hn => absurd hn (Nat.not_lt_zero n)) () 0 0 (mem_ball_self one_pos) hinit_one
  trivial

end SpherePackings.Audit.Nonvacuity06
