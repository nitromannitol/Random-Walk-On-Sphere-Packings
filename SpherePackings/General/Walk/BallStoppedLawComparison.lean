module

-- Built on Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne (commit cf73d6e).
public import SpherePackings.General.Walk.ActualStoppedLawComparison
public import SpherePackings.General.Walk.ExcursionSteps
public import BouRabeeGwynne.SelectedExcursionOscillation

@[expose] public section

/-!
# The stopped-law comparison for excursions from balls

The general comparison `levyProkhorov_actual_stopped_laws_le_of_shape` for the walk and Brownian
motion restarted in balls `B_r(c_j)` selected with an inner margin `r / 2`: the walk excursions
have the shape bound `max (2 r) |end - start|` (`actualWalkStage_shape`), the Brownian excursions
stay within `2 r` of their starts.  This is the counterpart of leobon12's
`levyProkhorov_actual_tiling_stopped_laws_le`, with no bound on the steps of the walk.
-/

open MeasureTheory ProbabilityTheory Set Metric
open scoped unitInterval ENNReal NNReal

namespace SpherePackings.MarkovChain

open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork

variable {d : ℕ} {V J : Type*} [MeasurableSpace V] [MeasurableEq V] [Countable J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

/-- The excursions of the walk from selected balls have the shape bound almost surely. -/
theorem law_ae_actualWalkExcursion_shape (κ : Kernel V V) [IsMarkovKernel κ]
    (pos : V → Euc d) (centers : J → Euc d) {r : ℝ} {A : Set V}
    (hBA : ∀ j, {w | pos w ∈ ball (centers j) r} ⊆ A) (hA : MeasurableSet A)
    (hexit : ∀ v, ∀ᵐ ω ∂law (absorbedKernel κ hA) v, exitTime A ω ≠ ⊤)
    (select : ℕ → Euc d → Option J)
    (hselect : ∀ i x j, select i x = some j → x ∈ ball (centers j) r)
    (initial : J) (v : V) (hv : pos v ∈ ball (centers initial) r) :
    ∀ᵐ ω ∂law (absorbedKernel κ hA) v, ∀ i, ∀ t,
      dist (ClockedWalkExcursion.curve (actualWalkExcursionSequence pos
          (fun j => {w | pos w ∈ ball (centers j) r}) initial select ω i).2 t)
        (ClockedWalkExcursion.curve (actualWalkExcursionSequence pos
          (fun j => {w | pos w ∈ ball (centers j) r}) initial select ω i).2 0) ≤
      max (2 * r) (dist
        (ClockedWalkExcursion.curve (actualWalkExcursionSequence pos
          (fun j => {w | pos w ∈ ball (centers j) r}) initial select ω i).2 1)
        (ClockedWalkExcursion.curve (actualWalkExcursionSequence pos
          (fun j => {w | pos w ∈ ball (centers j) r}) initial select ω i).2 0)) := by
  filter_upwards [actualWalkStage_ae_all_clocks_finite κ pos _ hBA hA hexit initial
    (fun i v => select i (pos v)) v, law_ae_start (absorbedKernel κ hA) v] with ω hf h0 i t
  exact actualWalkStage_shape pos (fun j => {w | pos w ∈ ball (centers j) r}) initial
    (fun i v => select i (pos v)) centers (fun j w hw => hw) (fun i w j h => hselect i (pos w) j h)
    ω (by rw [h0]; exact hv) i (hf i) t

/-- **The stopped-law comparison for ball excursions.** -/
theorem levyProkhorov_ball_stopped_laws_le (κ : Kernel V V) [IsMarkovKernel κ] (hd : 1 ≤ d)
    (pos : V → Euc d) (hpos : MeasurableEmbedding pos) (centers : J → Euc d) {r : ℝ} (hr : 0 < r)
    {A : Set V} (hBA : ∀ j, {w | pos w ∈ ball (centers j) r} ⊆ A) (hA : MeasurableSet A)
    (hexit : ∀ v, ∀ᵐ ω ∂law (absorbedKernel κ hA) v, exitTime A ω ≠ ⊤)
    (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ] (hμ : IsStandardBrownianLaw μ)
    (select : ℕ → Euc d → Option J) (hs : ∀ i, Measurable (select i))
    (hselect : ∀ i x j, select i x = some j → ball x (r / 2) ⊆ ball (centers j) r)
    (m : ℕ → ℕ) (E : ∀ i, Fin (m i) → Set (Euc d))
    (hE : ∀ i k, MeasurableSet (E i k))
    (hdE : ∀ i, Pairwise (fun j k => Disjoint (E i j) (E i k)))
    (initial : J) (v : V) (z : Euc d)
    (hv : pos v ∈ ball (centers initial) r) (hz : z ∈ ball (centers initial) r)
    (n : ℕ) (P : TimePartition n) {U : Set (Euc d)} (hU : IsOpen U)
    {a ε δ η : ℝ} (hε : 0 < ε) (hbuffer : ε + 2 * max (2 * r) (2 * a + 2 * r) < δ)
    (hnone : ∀ i x, select i x = none → x ∉ thickening δ U)
    (hdiam : ∀ i ≤ n, ∀ k, ∀ x ∈ E i k, ∀ y ∈ E i k, dist x y ≤ a)
    (hnear : dist (pos v) z ≤ a)
    (hpoint : max (2 * r) (2 * a + 2 * r) + a + 2 * r ≤ ε)
    {b c o : ℝ≥0∞}
    (hfailure : walkBrownianJointLaw κ pos hpos (fun j => {w | pos w ∈ ball (centers j) r})
      (fun _ => hpos.measurable measurableSet_ball)
      (fun j => ball (centers j) r) (fun _ => isOpen_ball) μ select hs m E hE hdE initial v z
      {p | ∃ i ≤ n, (p.1 i, p.2 i) ∉ goodExcursionPair pos (E i) a} ≤ b)
    (htail : μ {ω | (brownianSkeletonExcursion (fun j => ball (centers j) r) z initial
      (brownianSelectorForWalk select) n ω).1 = false} ≤ c)
    (hosc : μ {ω | P.concatenate (ExcursionTrajectory.prefixChain n d
      (fun k => (brownianSkeletonExcursion (fun j => ball (centers j) r) z initial
        (brownianSelectorForWalk select) k ω).2)) ∈
      unitCurveExitOscillationBad (innerDomain U ε) (thickening δ U) η} ≤ o)
    (rWalk rMiddle rBrownian : ℝ≥0) (hrWalk : 0 < rWalk) (hrBrownian : 0 < rBrownian)
    (hwalkBudget : b + c ≤ (rWalk : ℝ≥0∞))
    (hbrownianBudget : c ≤ (rBrownian : ℝ≥0∞))
    (hmiddleBudget : b + c + o ≤ (rMiddle : ℝ≥0∞))
    (hsmall : ENNReal.ofReal (ε + η) < (rMiddle : ℝ≥0∞)) :
    levyProkhorovEDist
      ((law (absorbedKernel κ hA) v).map (stoppedPolygonalCurve pos (pos ⁻¹' U)))
      (stoppedBrownianLaw U z μ) ≤ (rWalk + rMiddle + rBrownian : ℝ≥0) := by
  have hinside : ∀ i x j, select i x = some j → x ∈ ball (centers j) r :=
    fun i x j hj => hselect i x j hj (mem_ball_self (half_pos hr))
  exact levyProkhorov_actual_stopped_laws_le_of_shape κ hd pos hpos
    (fun j => {w | pos w ∈ ball (centers j) r}) (fun _ => hpos.measurable measurableSet_ball)
    (fun j => ball (centers j) r) (fun _ => isOpen_ball) (fun _ => isBounded_ball) μ hμ
    select hs m E hE hdE hBA hA hexit initial v z n P hU hε (by positivity) hbuffer hnone
    hdiam hnear hpoint
    (law_ae_actualWalkExcursion_shape κ pos centers hBA hA hexit select hinside initial v hv)
    (standardBrownianLaw_skeleton_ae_oscillation hd hμ centers hr select hs hinside initial z hz)
    hfailure htail hosc rWalk rMiddle rBrownian hrWalk hrBrownian hwalkBudget hbrownianBudget
    hmiddleBudget hsmall

end SpherePackings.MarkovChain
