module

-- Built on Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne (commit cf73d6e).
public import BouRabeeGwynne.Section3TheoremBPartA

@[expose] public section

/-!
# Assumption D for orthogonal tilings

Assumption D of rw-spheres.tex (lines 1438–1462), localized to balls inside the domain, for the
conductance-weighted walk on an orthogonal tiling sequence: on every ball whose closure lies in the
interior of the domain, the discrete Dirichlet problem with boundary data a function harmonic near
the closed ball eventually has a unique solution, and the solutions converge uniformly to that
function at the interior vertices.  The space-approximation part (4.1) of Assumption D is the
condition (1.3) `NearestVertexData.ApproximationCondition`, kept as a separate hypothesis.

By Theorem B(a), the assumption holds under (1.3) and one of the hypotheses (I), (II), (III).
-/

open BouRabeeGwynne

namespace SpherePackings

/-- Assumption D, localized to balls with the ambient collar. -/
def TilingAssumptionD {d : ℕ} (G : TilingSequence d) : Prop :=
  ∀ (c : Euc d) (r : ℝ) (h : Euc d → ℝ), 0 < r →
    HasAmbientCollar (Metric.ball c r) G.domain → HarmonicNearClosure h (Metric.ball c r) →
      DirichletApproximationTarget G (Metric.ball c r) h (fun n v => h ((G.tiling n).pos v))

/-- Theorem B(a) gives Assumption D for the tilings of Theorems A and B (the paper's proof of
Theorem A from Theorem 4.1, lines 1490–1493). -/
theorem tilingAssumptionD_of_paperRegularity {d : ℕ} (hd : 1 ≤ d) (G : TilingSequence d)
    (N : NearestVertexData G) (happrox : N.ApproximationCondition)
    (hreg : PaperRegularity G) : TilingAssumptionD G := by
  intro c r h hr hUD hh
  exact theoremB_part_a d G N (Metric.ball c r) h hd
    ⟨Metric.isOpen_ball, ⟨c, Metric.mem_ball_self hr⟩, (convex_ball c r).isPreconnected⟩
    Metric.isBounded_ball hUD happrox hreg hh

end SpherePackings
