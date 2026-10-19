-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/BrownianExitRangeComparison.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.BrownianExcursionRange
import BouRabeeGwynne.BrownianExcursionKernel
import Mathlib.Topology.MetricSpace.Thickening

/-! Exit-time comparisons control every point of the original stopped curve.
The collar inclusion uses the closure of the open outer thickening. -/

open Set Metric
open scoped NNReal ENNReal

namespace BouRabeeGwynne

lemma mem_closure_of_le_continuousExitTime {d : ℕ} {V : Set (Euc d)}
    (hV : IsOpen V) {z : Euc d} {ω : BrownianPath d} (hstart : z + ω 0 ∈ V)
    (hfinite : continuousExitTime V z ω ≠ ∞) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) ≤ continuousExitTime V z ω) : z + ω t ∈ closure V := by
  have ht' : t ≤ (continuousExitTime V z ω).toNNReal := by
    apply ENNReal.coe_le_coe.mp
    simpa only [ENNReal.coe_toNNReal hfinite] using ht
  obtain ⟨u, hu⟩ := mem_range_stoppedBrownianRepresentative V z ω ht'
  exact hu ▸ stoppedBrownianRepresentative_mem_closure hV hstart hfinite u

lemma mem_cthickening_of_le_outerExit {d : ℕ} (U : Set (Euc d)) (δ : ℝ)
    {z : Euc d} {ω : BrownianPath d} (hstart : z + ω 0 ∈ thickening δ U)
    (hfinite : continuousExitTime (thickening δ U) z ω ≠ ∞) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) ≤ continuousExitTime (thickening δ U) z ω) :
    z + ω t ∈ cthickening δ U :=
  closure_thickening_subset_cthickening δ U
    (mem_closure_of_le_continuousExitTime isOpen_thickening hstart hfinite ht)

theorem stoppedBrownianRepresentative_dist_le_of_exit_le {d : ℕ}
    (U : Set (Euc d)) (p z : Euc d) (R : ℝ) (ω : BrownianPath d)
    (hstart : z + ω 0 ∈ ball p R)
    (hfinite : continuousExitTime (ball p R) z ω ≠ ∞)
    (hle : continuousExitTime U z ω ≤ continuousExitTime (ball p R) z ω)
    (u : unitInterval) :
    dist (stoppedBrownianRepresentative U z ω u) z ≤ R + dist z p := by
  let t : ℝ≥0 := ⟨(u : ℝ) * ((continuousExitTime U z ω).toNNReal : ℝ),
    mul_nonneg u.property.1 (NNReal.coe_nonneg _)⟩
  have hfi := ne_top_of_le_ne_top hfinite hle
  have ht : t ≤ (continuousExitTime U z ω).toNNReal :=
    mul_le_of_le_one_left (NNReal.coe_nonneg _) u.property.2
  have ht' : (t : ℝ≥0∞) ≤ continuousExitTime (ball p R) z ω := by
    apply le_trans _ hle
    simpa only [ENNReal.coe_toNNReal hfi] using ENNReal.coe_le_coe.mpr ht
  have hmem : z + ω t ∈ closedBall p R :=
    (closure_minimal ball_subset_closedBall isClosed_closedBall)
      (mem_closure_of_le_continuousExitTime isOpen_ball hstart hfinite ht')
  change dist (z + ω t) z ≤ R + dist z p
  calc
    dist (z + ω t) z ≤ dist (z + ω t) p + dist p z := dist_triangle _ _ _
    _ ≤ R + dist z p := add_le_add (mem_closedBall.mp hmem)
      (le_of_eq (dist_comm p z))

end BouRabeeGwynne
