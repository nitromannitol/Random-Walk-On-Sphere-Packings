module

-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/JointExcursionPasting.lean` at commit cf73d6e): its theorem for the chain
-- of an arbitrary Markov kernel on a measurable space, with the deterministic bound on the
-- excursion ranges replaced by their shape (a bound that holds on the good event only).
public import BouRabeeGwynne.JointExcursionPasting
public import SpherePackings.General.MarkovChain.Absorbed
public import SpherePackings.General.Walk.ActualWalkSkeleton
public import SpherePackings.General.Walk.GoodRange
public import SpherePackings.General.Walk.WalkBrownianCoupling
public import SpherePackings.General.Walk.WalkSkeletonLaw
public import SpherePackings.General.Walk.WalkSkeletonPrefix

@[expose] public section

/-! General-state-space version of `BouRabeeGwynne.JointExcursionPasting`.  leobon12's theorem
assumes that every walk excursion stays within a fixed distance `R` of its start, which holds for
walks with bounded steps.  Here the excursions are only assumed to stay within
`max R₀ |end - start|` of their start (true for excursions from balls of radius `R₀ / 2`); on the
good event, where walk and Brownian endpoints are close, this bounds their ranges by
`max R₀ (2 a + S)` (`walk_range_of_goodExcursionPairs`). -/

set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Metric
open scoped unitInterval ENNReal
namespace SpherePackings.MarkovChain

open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork BouRabeeGwynne.TrajectoryCoupling
variable {d : ℕ} {V J : Type*} [MeasurableSpace V] [MeasurableEq V] [Countable J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

/-- The almost sure structure of the joint excursion law: compatible walk and Brownian
excursions, with the given starts, the walk excursions with the shape bound and the Brownian
excursions within `S` of their starts. -/
theorem walkBrownianJointLaw_ae_structure (κ : Kernel V V) [IsMarkovKernel κ]
    (hd : 1 ≤ d) (pos : V → Euc d) (hpos : MeasurableEmbedding pos)
    (B : J → Set V) (hB : ∀ j, MeasurableSet (B j))
    (U : J → Set (Euc d)) (hU : ∀ j, IsOpen (U j))
    (hUb : ∀ j, Bornology.IsBounded (U j))
    (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ] (hμ : IsStandardBrownianLaw μ)
    (select : ℕ → Euc d → Option J) (hs : ∀ n, Measurable (select n))
    (m : ℕ → ℕ) (E : ∀ n, Fin (m n) → Set (Euc d))
    (hE : ∀ n k, MeasurableSet (E n k))
    (hdE : ∀ n, Pairwise (fun i j => Disjoint (E n i) (E n j)))
    {A : Set V} (hBA : ∀ j, B j ⊆ A)
    (hA : MeasurableSet A) (hexit : ∀ v, ∀ᵐ ω ∂law (absorbedKernel κ hA) v, exitTime A ω ≠ ⊤)
    (initial : J) (v : V) (z : Euc d) (K : ℕ) {R₀ S : ℝ}
    (hwshape : ∀ᵐ ω ∂law (absorbedKernel κ hA) v, ∀ n, ∀ t,
      dist (ClockedWalkExcursion.curve (actualWalkExcursionSequence pos B initial select ω n).2 t)
        (ClockedWalkExcursion.curve (actualWalkExcursionSequence pos B initial select ω n).2 0) ≤
      max R₀ (dist
        (ClockedWalkExcursion.curve (actualWalkExcursionSequence pos B initial select ω n).2 1)
        (ClockedWalkExcursion.curve (actualWalkExcursionSequence pos B initial select ω n).2 0)))
    (hbrange : ∀ᵐ ω ∂μ, ∀ n,
      (brownianSkeletonExcursion U z initial (brownianSelectorForWalk select) n ω).2 ∈
        curveOscillationLe S) :
    ∀ᵐ p ∂walkBrownianJointLaw κ pos hpos B hB U hU μ select hs m E hE hdE initial v z,
      ((fun i => ClockedWalkExcursion.curve (p.1 i).2) ∈ ExcursionTrajectory.compatiblePaths K d ∧
        ClockedWalkExcursion.start (p.1 0).2 = pos v ∧
        ∀ n, ∀ t, dist (ClockedWalkExcursion.curve (p.1 n).2 t)
            (ClockedWalkExcursion.curve (p.1 n).2 0) ≤
          max R₀ (dist (ClockedWalkExcursion.curve (p.1 n).2 1)
            (ClockedWalkExcursion.curve (p.1 n).2 0))) ∧
      ((fun i => (p.2 i).2) ∈ ExcursionTrajectory.compatiblePaths K d ∧
        (p.2 0).2 0 = z ∧ ∀ n, (p.2 n).2 ∈ curveOscillationLe S) := by
  let WS : Set (ℕ → Bool × ClockedWalkExcursion d) := {w |
    (fun i => ClockedWalkExcursion.curve (w i).2) ∈ ExcursionTrajectory.compatiblePaths K d ∧
      ClockedWalkExcursion.start (w 0).2 = pos v ∧
        ∀ n, ∀ t, dist (ClockedWalkExcursion.curve (w n).2 t)
            (ClockedWalkExcursion.curve (w n).2 0) ≤
          max R₀ (dist (ClockedWalkExcursion.curve (w n).2 1)
            (ClockedWalkExcursion.curve (w n).2 0))}
  let BS : Set (ℕ → Bool × C(unitInterval, Euc d)) := {b |
    (fun i => (b i).2) ∈ ExcursionTrajectory.compatiblePaths K d ∧
      (b 0).2 0 = z ∧ ∀ n, (b n).2 ∈ curveOscillationLe S}
  have hWS : MeasurableSet WS := by
    have hr : MeasurableSet {w : ℕ → Bool × ClockedWalkExcursion d |
        ∀ n, ∀ t, dist (ClockedWalkExcursion.curve (w n).2 t)
            (ClockedWalkExcursion.curve (w n).2 0) ≤
          max R₀ (dist (ClockedWalkExcursion.curve (w n).2 1)
            (ClockedWalkExcursion.curve (w n).2 0))} := by
      have hshape : MeasurableSet {c : C(unitInterval, Euc d) |
          ∀ t, dist (c t) (c 0) ≤ max R₀ (dist (c 1) (c 0))} := by
        simp only [Set.ofPred_forall]
        exact (isClosed_iInter fun t => isClosed_le
          ((continuous_eval_const t).dist (continuous_eval_const 0))
          (continuous_const.max ((continuous_eval_const 1).dist
            (continuous_eval_const 0)))).measurableSet
      have hset : {w : ℕ → Bool × ClockedWalkExcursion d |
          ∀ n, ∀ t, dist (ClockedWalkExcursion.curve (w n).2 t)
              (ClockedWalkExcursion.curve (w n).2 0) ≤
            max R₀ (dist (ClockedWalkExcursion.curve (w n).2 1)
              (ClockedWalkExcursion.curve (w n).2 0))} =
          ⋂ n, (fun w : ℕ → Bool × ClockedWalkExcursion d =>
            ClockedWalkExcursion.curve (w n).2) ⁻¹'
            {c : C(unitInterval, Euc d) | ∀ t, dist (c t) (c 0) ≤ max R₀ (dist (c 1) (c 0))} := by
        ext w
        simp [Set.mem_iInter]
      rw [hset]
      exact MeasurableSet.iInter fun n =>
        (ClockedWalkExcursion.measurable_curve.comp (measurable_pi_apply n).snd) hshape
    exact ((ExcursionTrajectory.measurableSet_compatiblePaths K d).preimage
      (Measurable.of_eval fun n => ClockedWalkExcursion.measurable_curve.comp
        (measurable_pi_apply n).snd)).inter
      ((measurableSet_eq_fun (ClockedWalkExcursion.measurable_start.comp
        (measurable_pi_apply 0).snd) measurable_const).inter hr)
  have hBS : MeasurableSet BS := by
    have hr : MeasurableSet {b : ℕ → Bool × C(unitInterval, Euc d) |
        ∀ n, (b n).2 ∈ curveOscillationLe S} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun n =>
        (measurable_pi_apply n).snd (measurableSet_curveOscillationLe S)
    exact ((ExcursionTrajectory.measurableSet_compatiblePaths K d).preimage
      (Measurable.of_eval fun n => (measurable_pi_apply n).snd)).inter
      ((measurableSet_eq_fun ((ContinuousMap.measurable_eval 0).comp
        (measurable_pi_apply 0).snd) measurable_const).inter hr)
  have hwactual : ∀ᵐ ω ∂law (absorbedKernel κ hA) v,
      actualWalkExcursionSequence pos B initial select ω ∈ WS := by
    filter_upwards [actualWalkStage_ae_all_clocks_finite κ pos B hBA hA hexit initial
      (fun n v => select n (pos v)) v, law_ae_start (absorbedKernel κ hA) v, hwshape]
      with ω hf hstart hr
    refine ⟨actualWalkStage_compatiblePaths pos B initial (fun n v => select n (pos v))
      K ω (hf K), ?_, hr⟩
    simpa only [actualWalkExcursionSequence, actualWalkStage, ClockedWalkExcursion.start_ofWalk]
      using congrArg pos hstart
  have hbstart : ∀ᵐ ω ∂μ,
      (brownianSkeletonExcursion U z initial (brownianSelectorForWalk select) 0 ω).2 0 = z := by
    exact ae_of_ae_map (measurable_stoppedBrownianRepresentative (hU initial) z).aemeasurable
      (brownianExcursionKernel_ae_start (hU initial) μ hμ z)
  have hbactual : ∀ᵐ ω ∂μ,
      (fun n => brownianSkeletonExcursion U z initial (brownianSelectorForWalk select) n ω) ∈ BS := by
    filter_upwards [standardBrownianLaw_ae_finiteSkeletonClock hd hμ U hU hUb z initial
      (fun n => hs (n - 1)) K, hbstart, hbrange] with ω hf hstart hr
    refine ⟨?_, hstart, hr⟩
    have hchain := brownianSkeletonPhysicalKnots_chain_apply U z initial
      (brownianSelectorForWalk select) K ω hf
    intro i j hij
    change (brownianSkeletonExcursion U z initial (brownianSelectorForWalk select) i.val ω).2 1 =
      (brownianSkeletonExcursion U z initial (brownianSelectorForWalk select) j.val ω).2 0
    rw [← hchain i, ← hchain j]
    exact ((brownianSkeletonPhysicalKnots U z initial (brownianSelectorForWalk select) K ω hf).chain
      z ω).property i j hij
  have hm := walkBrownianJointLaw_marginals κ pos hpos B hB U hU μ select hs m E hE hdE
    hd hμ hUb hBA hA hexit initial v z
  have hwlaw : ∀ᵐ w ∂(walkBrownianJointLaw κ pos hpos B hB U hU μ select hs m E hE hdE
      initial v z).fst, w ∈ WS := by
    rw [hm.1]
    exact (ae_map_iff (measurable_actualWalkExcursionSequence pos B initial select
      hpos.measurable hB hs).aemeasurable hWS).mpr hwactual
  have hblaw : ∀ᵐ b ∂(walkBrownianJointLaw κ pos hpos B hB U hU μ select hs m E hE hdE
      initial v z).snd, b ∈ BS := by
    rw [hm.2]
    exact (ae_map_iff (Measurable.of_eval fun n => measurable_brownianSkeletonExcursion U hU z
      initial (fun n => hs (n - 1)) n).aemeasurable hBS).mpr hbactual
  filter_upwards [ae_of_ae_map measurable_fst.aemeasurable hwlaw,
    ae_of_ae_map measurable_snd.aemeasurable hblaw] with p hw hb
  exact ⟨hw, hb⟩

/-- **Walk ranges on the good event**: the walk excursions `0, …, K` of a good pair stay within
`max R₀ (2 a + S)` of their starts. -/
theorem walkBrownianJointLaw_ae_walk_range (κ : Kernel V V) [IsMarkovKernel κ]
    (hd : 1 ≤ d) (pos : V → Euc d) (hpos : MeasurableEmbedding pos)
    (B : J → Set V) (hB : ∀ j, MeasurableSet (B j))
    (U : J → Set (Euc d)) (hU : ∀ j, IsOpen (U j))
    (hUb : ∀ j, Bornology.IsBounded (U j))
    (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ] (hμ : IsStandardBrownianLaw μ)
    (select : ℕ → Euc d → Option J) (hs : ∀ n, Measurable (select n))
    (m : ℕ → ℕ) (E : ∀ n, Fin (m n) → Set (Euc d))
    (hE : ∀ n k, MeasurableSet (E n k))
    (hdE : ∀ n, Pairwise (fun i j => Disjoint (E n i) (E n j)))
    {A : Set V} (hBA : ∀ j, B j ⊆ A)
    (hA : MeasurableSet A) (hexit : ∀ v, ∀ᵐ ω ∂law (absorbedKernel κ hA) v, exitTime A ω ≠ ⊤)
    (initial : J) (v : V) (z : Euc d) (K : ℕ) {R₀ a S : ℝ}
    (hdiam : ∀ i ≤ K, ∀ k, ∀ x ∈ E i k, ∀ y ∈ E i k, dist x y ≤ a)
    (hnear : dist (pos v) z ≤ a)
    (hwshape : ∀ᵐ ω ∂law (absorbedKernel κ hA) v, ∀ n, ∀ t,
      dist (ClockedWalkExcursion.curve (actualWalkExcursionSequence pos B initial select ω n).2 t)
        (ClockedWalkExcursion.curve (actualWalkExcursionSequence pos B initial select ω n).2 0) ≤
      max R₀ (dist
        (ClockedWalkExcursion.curve (actualWalkExcursionSequence pos B initial select ω n).2 1)
        (ClockedWalkExcursion.curve (actualWalkExcursionSequence pos B initial select ω n).2 0)))
    (hbrange : ∀ᵐ ω ∂μ, ∀ n,
      (brownianSkeletonExcursion U z initial (brownianSelectorForWalk select) n ω).2 ∈
        curveOscillationLe S) :
    ∀ᵐ p ∂walkBrownianJointLaw κ pos hpos B hB U hU μ select hs m E hE hdE initial v z,
      (∀ i ≤ K, (p.1 i, p.2 i) ∈ goodExcursionPair pos (E i) a) →
        ∀ i ≤ K, ClockedWalkExcursion.curve (p.1 i).2 ∈
          curveOscillationLe (max R₀ (2 * a + S)) := by
  filter_upwards [walkBrownianJointLaw_ae_structure κ hd pos hpos B hB U hU hUb μ hμ select hs
    m E hE hdE hBA hA hexit initial v z K hwshape hbrange] with p hp
  obtain ⟨⟨hwc, hws, hwsh⟩, ⟨hbc, hbs, hbr⟩⟩ := hp
  intro hgood
  exact walk_range_of_goodExcursionPairs pos m E hdiam p.1 p.2 hwc hbc hgood
    (by rw [hws, hbs]; exact hnear) (fun i _ => hbr i) (fun i _ => hwsh i)

/-- **Pasting on good pairs**, for walks without a deterministic step bound: on the good event
the pasted walk and Brownian curves stay within `max R₀ (2 a + S) + a + S`. -/
theorem walkBrownianJointLaw_ae_pasted_dist_le (κ : Kernel V V) [IsMarkovKernel κ]
    (hd : 1 ≤ d) (pos : V → Euc d) (hpos : MeasurableEmbedding pos)
    (B : J → Set V) (hB : ∀ j, MeasurableSet (B j))
    (U : J → Set (Euc d)) (hU : ∀ j, IsOpen (U j))
    (hUb : ∀ j, Bornology.IsBounded (U j))
    (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ] (hμ : IsStandardBrownianLaw μ)
    (select : ℕ → Euc d → Option J) (hs : ∀ n, Measurable (select n))
    (m : ℕ → ℕ) (E : ∀ n, Fin (m n) → Set (Euc d))
    (hE : ∀ n k, MeasurableSet (E n k))
    (hdE : ∀ n, Pairwise (fun i j => Disjoint (E n i) (E n j)))
    {A : Set V} (hBA : ∀ j, B j ⊆ A)
    (hA : MeasurableSet A) (hexit : ∀ v, ∀ᵐ ω ∂law (absorbedKernel κ hA) v, exitTime A ω ≠ ⊤)
    (initial : J) (v : V) (z : Euc d) {K : ℕ} (P : TimePartition K) {R₀ a S : ℝ}
    (hdiam : ∀ i ≤ K, ∀ k, ∀ x ∈ E i k, ∀ y ∈ E i k, dist x y ≤ a)
    (hnear : dist (pos v) z ≤ a)
    (hwshape : ∀ᵐ ω ∂law (absorbedKernel κ hA) v, ∀ n, ∀ t,
      dist (ClockedWalkExcursion.curve (actualWalkExcursionSequence pos B initial select ω n).2 t)
        (ClockedWalkExcursion.curve (actualWalkExcursionSequence pos B initial select ω n).2 0) ≤
      max R₀ (dist
        (ClockedWalkExcursion.curve (actualWalkExcursionSequence pos B initial select ω n).2 1)
        (ClockedWalkExcursion.curve (actualWalkExcursionSequence pos B initial select ω n).2 0)))
    (hbrange : ∀ᵐ ω ∂μ, ∀ n,
      (brownianSkeletonExcursion U z initial (brownianSelectorForWalk select) n ω).2 ∈
        curveOscillationLe S) :
    ∀ᵐ p ∂walkBrownianJointLaw κ pos hpos B hB U hU μ select hs m E hE hdE initial v z,
      (∀ i ≤ K, (p.1 i, p.2 i) ∈ goodExcursionPair pos (E i) a) → ∀ t,
        dist (P.concatenate (ExcursionTrajectory.prefixChain K d
          (fun i => ClockedWalkExcursion.curve (p.1 i).2)) t)
          (P.concatenate (ExcursionTrajectory.prefixChain K d (fun i => (p.2 i).2)) t) ≤
            max R₀ (2 * a + S) + a + S := by
  filter_upwards [walkBrownianJointLaw_ae_structure κ hd pos hpos B hB U hU hUb μ hμ select hs
      m E hE hdE hBA hA hexit initial v z K hwshape hbrange,
    walkBrownianJointLaw_ae_walk_range κ hd pos hpos B hB U hU hUb μ hμ select hs
      m E hE hdE hBA hA hexit initial v z K hdiam hnear hwshape hbrange] with p hp hrange
  obtain ⟨⟨hwc, hws, -⟩, ⟨hbc, hbs, hbr⟩⟩ := hp
  intro hgood t
  exact goodExcursionPair_pasted_pointwise_dist_le pos P m E hdiam p.1 p.2 hwc hbc hgood
    (by rw [hws, hbs]; exact hnear) (hrange hgood) (fun i _ => hbr i) t

end SpherePackings.MarkovChain
