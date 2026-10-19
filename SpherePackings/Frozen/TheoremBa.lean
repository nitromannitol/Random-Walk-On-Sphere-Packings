/-
Theorem B, alternative (a), of rw-spheres.tex, frozen.

Paper statement, `rw-spheres.tex:297-321` (label `theorem:convergence-of-the-dirichlet-problem`),
alternative (a): for a bounded domain `U` and `h_C` harmonic in a neighbourhood of `closure U`, the
discrete harmonic extensions converge uniformly on `V_n[U]`.

Statement of leobon12 (`BouRabeeGwynne.TheoremBPartAStatement`) with the ambient collar
`closure U ⊆ interior D`; it also asserts eventual existence and uniqueness of the discrete
solution.
-/
import BouRabeeGwynne.Section3TheoremBPartA

open scoped Topology ENNReal
open BouRabeeGwynne

-- FROZEN-STATEMENT-BEGIN
theorem SpherePackings.Frozen.theoremB_a :
  ∀ (d : ℕ) (G : TilingSequence d) (N : NearestVertexData G)
    (U : Set (Euc d)) (hC : Euc d → ℝ),
    1 ≤ d → IsDomain U → Bornology.IsBounded U →
    HasAmbientCollar U G.domain → N.ApproximationCondition → PaperRegularity G →
    HarmonicNearClosure hC U →
      DirichletApproximationTarget G U hC (fun n v => hC ((G.tiling n).pos v))
-- FROZEN-STATEMENT-END
:= BouRabeeGwynne.theoremB_part_a
