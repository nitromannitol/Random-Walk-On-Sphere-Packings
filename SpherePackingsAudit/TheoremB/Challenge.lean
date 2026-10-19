import SpherePackingsAudit.Vocabulary.BouRabeeGwynne.TheoremBStatement

/-!
# Comparator challenge: Theorem B (`theorem:convergence-of-the-dirichlet-problem`), both alternatives

This file imports only Mathlib and the vocabulary modules of `SpherePackingsAudit/Vocabulary/`,
which copy verbatim, under their repository names, the repository declarations needed to read the
statement (`python3 tools/check_vocabulary.py`).  It ends with one `sorry`, the proof being checked.
-/

namespace SpherePackingsAudit

open scoped Topology ENNReal
open BouRabeeGwynne

/-- Theorem B (`theorem:convergence-of-the-dirichlet-problem`), both alternatives. -/
theorem theoremB :
  (∀ (d : ℕ) (G : TilingSequence d) (N : NearestVertexData G)
    (U : Set (Euc d)) (hC : Euc d → ℝ),
    1 ≤ d → IsDomain U → Bornology.IsBounded U →
    HasAmbientCollar U G.domain → N.ApproximationCondition → PaperRegularity G →
    HarmonicNearClosure hC U →
      DirichletApproximationTarget G U hC (fun n v => hC ((G.tiling n).pos v))) ∧
  (∀ (d : ℕ) (G : TilingSequence d) (N : NearestVertexData G)
    (U : Set (Euc d)) (hC : Euc d → ℝ),
    1 ≤ d → IsLipschitzDomain U → Bornology.IsBounded U →
    HasAmbientCollar U G.domain → N.ApproximationCondition → PaperRegularity G →
    IsHarmonicOn hC U → ContinuousOnClosure hC U →
      Nonempty (NearestClosureBoundaryChoices G U) ∧
      ∀ S : NearestClosureBoundaryChoices G U,
        (∀ n v, S.point n v ∈ frontier U) ∧
        (∀ᶠ n in Filter.atTop, ∀ v : (G.tiling n).boundaryVertices U,
          dist ((G.tiling n).pos v) (S.point n v) ≤ 2 * (G.tiling n).mesh.toReal) ∧
        DirichletApproximationTarget G U hC (S.boundaryData hC)) := by
  sorry

end SpherePackingsAudit
