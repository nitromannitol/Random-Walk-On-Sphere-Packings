/- Nonvacuity examples written by the independent reviewer (Claude Haiku 5.5) of audit batch 09;
   see `AUDIT.md`. They show that the hypothesis bundles named below can hold together. -/
import BouRabeeGwynne.Section3CaseIITarget
import SpherePackings.Support.Guards.LatticeTilings

-- The reviewer's examples, kept as written.
set_option linter.unusedVariables false
set_option linter.deprecated false

/-!
Nonvacuity of the hypothesis bundle of `BouRabeeGwynne.theoremB_part_a_caseII` (Hypothesis II,
Theorem B(a)): the lattice tiling sequence of `exists_lattice_tilingSequence` supplies the
tilings, collar, nearest vertices, approximation condition (1.3) and Hypothesis II, and
the zero function is harmonic on `ball 0 2`, a neighbourhood of `closure (ball 0 1)`.
-/

open Metric

namespace SpherePackings.Audit.Nonvacuity09
open BouRabeeGwynne
/-- The non-dimensional hypotheses of `theoremB_part_a_caseII` (with `1 ≤ d` assumed) are
simultaneously satisfied by a concrete instance. -/
theorem nonvacuity_caseII_hypotheses {d : ℕ} (hd : 1 ≤ d) :
    ∃ (G : TilingSequence d) (N : NearestVertexData G) (U : Set (Euc d)) (hC : Euc d → ℝ),
      Bornology.IsBounded U ∧ HasAmbientCollar U G.domain ∧ N.ApproximationCondition ∧
        RegularityII G ∧ HarmonicNearClosure hC U := by
  obtain ⟨G, hcol, ⟨N⟩, hall, hII⟩ := SpherePackings.exists_lattice_tilingSequence hd
  refine ⟨G, N, ball (0 : Euc d) 1, fun _ => 0, isBounded_ball, hcol, hall N, hII,
    ball (0 : Euc d) 2, isOpen_ball, ?_, contDiffOn_const, fun x _ => by simp⟩
  exact (closure_ball_subset_closedBall).trans (closedBall_subset_ball (by norm_num))

/-- The conclusion of Theorem B(a) under Hypothesis II is attained on the same instance:
the hypotheses of `theoremB_part_a_caseII` can all be met at once. -/
theorem nonvacuity_caseII_conclusion {d : ℕ} (hd : 1 ≤ d) :
    ∃ (G : TilingSequence d) (N : NearestVertexData G),
      DirichletApproximationTarget G (ball (0 : Euc d) 1) (fun _ => 0)
        (fun _n _v => (0 : ℝ)) := by
  obtain ⟨G, hcol, ⟨N⟩, hall, hII⟩ := SpherePackings.exists_lattice_tilingSequence hd
  have hh : HarmonicNearClosure (fun _ : Euc d => (0 : ℝ)) (ball (0 : Euc d) 1) :=
    ⟨ball (0 : Euc d) 2, isOpen_ball,
      (closure_ball_subset_closedBall).trans (closedBall_subset_ball (by norm_num)),
      contDiffOn_const, fun x _ => by simp⟩
  exact ⟨G, N, theoremB_part_a_caseII hd G N (ball (0 : Euc d) 1) (fun _ => 0)
    isBounded_ball hcol (hall N) hII hh⟩

end SpherePackings.Audit.Nonvacuity09
