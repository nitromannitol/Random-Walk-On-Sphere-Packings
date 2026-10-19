-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/ActualStoppedLawComparison.lean` at commit cf73d6e): its theorem for the
-- chain of an arbitrary Markov kernel on a measurable space, with the deterministic step and range
-- bounds of the walk replaced by the shape of its excursions.
import BouRabeeGwynne.ActualStoppedLawComparison
import SpherePackings.General.Walk.CanonicalStoppingRange
import SpherePackings.General.Walk.FiniteStoppedLawComparisonGood
import SpherePackings.General.Walk.JointExcursionPasting
import SpherePackings.General.Walk.WalkBrownianActiveTransfer
import SpherePackings.General.Walk.WalkReconstructionLaw

/-! General-state-space version of `BouRabeeGwynne.ActualStoppedLawComparison`.  leobon12's
theorem assumes a deterministic bound on the steps of the walk and on the ranges of its
excursions.  Here the excursions are only assumed to satisfy the shape bound
`max R₀ |end - start|`; on the good event their ranges are at most `R' := max R₀ (2 a + S)`
(`walkBrownianJointLaw_ae_walk_range`), and the steps before the exit at most `2 R'`
(`trajectoryLaw_map_ae_canonicalWalkStoppingSupport_of_range`), which is all the comparison
uses. -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval ENNReal NNReal
namespace SpherePackings.MarkovChain

open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork BouRabeeGwynne.TrajectoryCoupling
variable {d : ℕ} {V J : Type*} [MeasurableSpace V] [MeasurableEq V] [Countable J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

theorem levyProkhorov_actual_stopped_laws_le_of_shape (κ : Kernel V V) [IsMarkovKernel κ]
    (hd : 1 ≤ d) (pos : V → Euc d) (hpos : MeasurableEmbedding pos)
    (B : J → Set V) (hB : ∀ j, MeasurableSet (B j))
    (W : J → Set (Euc d)) (hW : ∀ j, IsOpen (W j))
    (hWb : ∀ j, Bornology.IsBounded (W j))
    (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ] (hμ : IsStandardBrownianLaw μ)
    (select : ℕ → Euc d → Option J) (hs : ∀ i, Measurable (select i))
    (m : ℕ → ℕ) (E : ∀ i, Fin (m i) → Set (Euc d))
    (hE : ∀ i k, MeasurableSet (E i k))
    (hdE : ∀ i, Pairwise (fun j k => Disjoint (E i j) (E i k)))
    {A : Set V} (hBA : ∀ j, B j ⊆ A)
    (hA : MeasurableSet A) (hexit : ∀ v, ∀ᵐ ω ∂law (absorbedKernel κ hA) v, exitTime A ω ≠ ⊤)
    (initial : J) (v : V) (z : Euc d) (n : ℕ) (P : TimePartition n)
    {U : Set (Euc d)} (hU : IsOpen U) {a R₀ S ε δ η : ℝ}
    (hε : 0 < ε) (hR₀ : 0 ≤ R₀) (hbuffer : ε + 2 * max R₀ (2 * a + S) < δ)
    (hnone : ∀ i x, select i x = none → x ∉ Metric.thickening δ U)
    (hdiam : ∀ i ≤ n, ∀ k, ∀ x ∈ E i k, ∀ y ∈ E i k, dist x y ≤ a)
    (hnear : dist (pos v) z ≤ a) (hpoint : max R₀ (2 * a + S) + a + S ≤ ε)
    (hwshape : ∀ᵐ ω ∂law (absorbedKernel κ hA) v, ∀ i, ∀ t,
      dist (ClockedWalkExcursion.curve (actualWalkExcursionSequence pos B initial select ω i).2 t)
        (ClockedWalkExcursion.curve (actualWalkExcursionSequence pos B initial select ω i).2 0) ≤
      max R₀ (dist
        (ClockedWalkExcursion.curve (actualWalkExcursionSequence pos B initial select ω i).2 1)
        (ClockedWalkExcursion.curve (actualWalkExcursionSequence pos B initial select ω i).2 0)))
    (hbrange : ∀ᵐ ω ∂μ, ∀ i,
      (brownianSkeletonExcursion W z initial (brownianSelectorForWalk select) i ω).2 ∈
        curveOscillationLe S)
    {b c o : ℝ≥0∞}
    (hfailure : walkBrownianJointLaw κ pos hpos B hB W hW μ select hs m E hE hdE initial v z
      {p | ∃ i ≤ n, (p.1 i, p.2 i) ∉ goodExcursionPair pos (E i) a} ≤ b)
    (htail : μ {ω | (brownianSkeletonExcursion W z initial
      (brownianSelectorForWalk select) n ω).1 = false} ≤ c)
    (hosc : μ {ω | P.concatenate (ExcursionTrajectory.prefixChain n d
      (fun k => (brownianSkeletonExcursion W z initial
        (brownianSelectorForWalk select) k ω).2)) ∈
      unitCurveExitOscillationBad (innerDomain U ε) (Metric.thickening δ U) η} ≤ o)
    (rWalk rMiddle rBrownian : ℝ≥0) (hrWalk : 0 < rWalk) (hrBrownian : 0 < rBrownian)
    (hwalkBudget : b + c ≤ (rWalk : ℝ≥0∞))
    (hbrownianBudget : c ≤ (rBrownian : ℝ≥0∞))
    (hmiddleBudget : b + c + o ≤ (rMiddle : ℝ≥0∞))
    (hsmall : ENNReal.ofReal (ε + η) < (rMiddle : ℝ≥0∞)) :
    levyProkhorovEDist
      ((law (absorbedKernel κ hA) v).map (stoppedPolygonalCurve pos (pos ⁻¹' U)))
      (stoppedBrownianLaw U z μ) ≤ (rWalk + rMiddle + rBrownian : ℝ≥0) := by
  set R' := max R₀ (2 * a + S) with hR'
  let ρ := walkBrownianJointLaw κ pos hpos B hB W hW μ select hs m E hE hdE initial v z
  let Γ := fun ω k => brownianSkeletonExcursion W z initial
    (brownianSelectorForWalk select) k ω
  have hΓ : Measurable Γ := Measurable.of_eval fun k =>
    measurable_brownianSkeletonExcursion W hW z initial (fun i => hs (i - 1)) k
  have hmarg := walkBrownianJointLaw_marginals κ pos hpos B hB W hW μ select hs m E hE hdE
    hd hμ hWb hBA hA hexit initial v z
  have hwlaw : ρ.fst = (law (absorbedKernel κ hA) v).map
      (actualWalkExcursionSequence pos B initial select) := hmarg.1
  have hblaw : ρ.snd = μ.map Γ := hmarg.2
  have hmesh : 0 ≤ 2 * R' := mul_nonneg zero_le_two (le_max_of_le_left hR₀)
  have hδ : 0 < δ := lt_of_lt_of_le hε (le_trans (le_add_of_nonneg_right hmesh) hbuffer.le)
  have hnoneU : ∀ i x, select i x = none → x ∉ U := by
    intro i x hx hxin
    exact hnone i x hx (Metric.self_subset_thickening hδ U hxin)
  have hnoneBrownian : ∀ i x, brownianSelectorForWalk select i x = none →
      x ∉ Metric.thickening δ U := fun i x hx => hnone (i - 1) x hx
  -- the walk support, on the good event
  have hsupp : ∀ᵐ e ∂ρ.fst, (∀ i ≤ n, ClockedWalkExcursion.curve (e i).2 ∈
      curveOscillationLe R') → (e n).1 = false ∨ e ∈ canonicalWalkStoppingSupport U (2 * R') P := by
    rw [hwlaw]
    exact trajectoryLaw_map_ae_canonicalWalkStoppingSupport_of_range κ pos hpos.measurable B hB
      hBA hA hexit initial select hs U hU.measurableSet hnoneU v n R' P
  have hrange := walkBrownianJointLaw_ae_walk_range κ hd pos hpos B hB W hW hWb μ hμ select hs
    m E hE hdE hBA hA hexit initial v z n hdiam hnear hwshape hbrange
  have hwalk : ∀ᵐ p ∂ρ, (∀ i ≤ n, (p.1 i, p.2 i) ∈ goodExcursionPair pos (E i) a) →
      (p.1 n).1 = false ∨ p.1 ∈ canonicalWalkStoppingSupport U (2 * R') P := by
    filter_upwards [ae_of_ae_map measurable_fst.aemeasurable hsupp, hrange] with p h1 h2
    exact fun hgood => h1 (h2 hgood)
  have hendpoint : ∀ᵐ γ ∂ρ.snd, (γ n).1 = true →
      P.concatenate (ExcursionTrajectory.prefixChain n d (fun k => (γ k).2)) 1 ∉
        Metric.thickening δ U := by
    rw [hblaw]
    exact standardBrownianLaw_skeleton_ae_stopped_endPoint_outside hd hμ W hW hWb z initial
      (brownianSelectorForWalk select) (fun i => hs (i - 1))
      Metric.isOpen_thickening.measurableSet hnoneBrownian n P
  have hclose : ∀ᵐ p ∂ρ,
      (∀ i ≤ n, (p.1 i, p.2 i) ∈ goodExcursionPair pos (E i) a) → ∀ t,
      dist (pastedWalkCurve P p.1 t)
        (P.concatenate (ExcursionTrajectory.prefixChain n d (fun k => (p.2 k).2)) t) ≤ ε := by
    filter_upwards [walkBrownianJointLaw_ae_pasted_dist_le κ hd pos hpos B hB W hW hWb μ hμ
      select hs m E hE hdE hBA hA hexit initial v z P hdiam hnear hwshape hbrange]
      with p hp
    intro hgood t
    exact (hp hgood t).trans hpoint
  have htailρ : ρ.snd (sequenceActive n) ≤ c := by
    rw [hblaw, Measure.map_apply hΓ (measurableSet_sequenceActive n)]
    exact htail
  let G := fun γ : ℕ → Bool × C(unitInterval, Euc d) =>
    P.concatenate (ExcursionTrajectory.prefixChain n d (fun k => (γ k).2))
  have hG : Measurable G := P.measurable_concatenate.comp
    ((ExcursionTrajectory.measurable_prefixChain n d).comp
      (Measurable.of_eval fun k => (measurable_pi_apply k).snd))
  have hObad : MeasurableSet {γ | G γ ∈
      unitCurveExitOscillationBad (innerDomain U ε) (Metric.thickening δ U) η} :=
    (measurableSet_unitCurveExitOscillationBad (isOpen_innerDomain U ε)
      Metric.isOpen_thickening η).preimage hG
  have hoscρ : ρ.snd {γ | G γ ∈
      unitCurveExitOscillationBad (innerDomain U ε) (Metric.thickening δ U) η} ≤ o := by
    rw [hblaw, Measure.map_apply hΓ hObad]
    exact hosc
  have hmiddle : levyProkhorovEDist
      (ρ.fst.map (reconstructedVertexStoppedCurve U n))
      (ρ.snd.map (reconstructedBrownianStoppedCurve U P)) ≤ (rMiddle : ℝ≥0∞) :=
    levyProkhorov_reconstructed_stopped_laws_le_of_good pos m E a P hU ρ hε hmesh hbuffer
      rMiddle hsmall hwalk hendpoint hclose hfailure htailρ hoscρ hmiddleBudget
  have hwalkTail : law (absorbedKernel κ hA) v
      {ω | (actualWalkExcursionSequence pos B initial select ω n).1 = false} ≤
        (rWalk : ℝ≥0∞) := by
    apply (trajectoryLaw_walkActive_le_brownianActive_add_failure κ hd pos hpos B hB W hW hWb
      μ hμ select hs m E hE hdE hBA hA hexit initial v z a n).trans
    exact (add_le_add htail hfailure).trans (by simpa only [add_comm] using hwalkBudget)
  have hleft : levyProkhorovEDist
      ((law (absorbedKernel κ hA) v).map (stoppedPolygonalCurve pos (pos ⁻¹' U)))
      (ρ.fst.map (reconstructedVertexStoppedCurve U n)) ≤ (rWalk : ℝ≥0∞) := by
    rw [hwlaw]
    exact trajectoryLaw_reconstructedStopped_le κ pos hpos.measurable B hBA hB hA hexit initial
      select hs U hU.measurableSet hnoneU v n rWalk hrWalk hwalkTail
  have hrightReverse : levyProkhorovEDist (stoppedBrownianLaw U z μ)
      (ρ.snd.map (reconstructedBrownianStoppedCurve U P)) ≤ (rBrownian : ℝ≥0∞) := by
    rw [hblaw]
    apply levyProkhorov_stoppedBrownian_reconstruction_le hd hμ W hW hWb z initial
      (brownianSelectorForWalk select) (fun i => hs (i - 1)) hU
      (fun i x hx => hnoneU (i - 1) x hx) n P rBrownian hrBrownian
    simpa only [brownianSkeletonExcursion_flag] using htail.trans hbrownianBudget
  have hright : levyProkhorovEDist
      (ρ.snd.map (reconstructedBrownianStoppedCurve U P)) (stoppedBrownianLaw U z μ) ≤
      (rBrownian : ℝ≥0∞) := by
    rw [levyProkhorovEDist_comm]
    exact hrightReverse
  have htriangle := (levyProkhorovEDist_triangle
    ((law (absorbedKernel κ hA) v).map (stoppedPolygonalCurve pos (pos ⁻¹' U)))
    (ρ.fst.map (reconstructedVertexStoppedCurve U n)) (stoppedBrownianLaw U z μ)).trans
      (add_le_add hleft ((levyProkhorovEDist_triangle
        (ρ.fst.map (reconstructedVertexStoppedCurve U n))
        (ρ.snd.map (reconstructedBrownianStoppedCurve U P)) (stoppedBrownianLaw U z μ)).trans
          (add_le_add hmiddle hright)))
  simpa only [ENNReal.coe_add, add_assoc] using htriangle

end SpherePackings.MarkovChain
