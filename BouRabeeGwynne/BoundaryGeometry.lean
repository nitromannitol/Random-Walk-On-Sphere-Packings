-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/BoundaryGeometry.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.LocalRegion
import BouRabeeGwynne.BoundarySampling

open scoped ENNReal

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

/-- Every minimizing boundary sample is at most two meshes from the external
vertex. The comparison uses its adjacent interior vertex, not its own cell. -/
lemma boundary_minimizer_dist_le {U : Set (Euc d)} {w : T.V}
    (hw : w ∈ T.boundaryVertices U) (hmesh : T.mesh ≠ ∞) {q : Euc d}
    (hmin : ∀ z ∈ U, dist (T.pos w) q ≤ dist (T.pos w) z) :
    dist (T.pos w) q ≤ 2 * T.mesh.toReal := by
  obtain ⟨v, hv, hdist⟩ := T.boundaryVertices_near_interior hw hmesh
  exact (hmin (T.pos v) hv).trans hdist

/-- The approved nearest-closure sample is on the continuum boundary. -/
lemma boundary_projection_mem_frontier {U : Set (Euc d)} (hne : U.Nonempty)
    {w : T.V} (hw : w ∈ T.boundaryVertices U) :
    nearestClosurePoint U hne (T.pos w) ∈ frontier U :=
  nearestClosurePoint_mem_frontier_of_notMem U hne hw.1

/-- The approved boundary sampling has the required vanishing mesh-scale error. -/
lemma boundary_projection_dist_le {U : Set (Euc d)} (hne : U.Nonempty)
    {w : T.V} (hw : w ∈ T.boundaryVertices U) (hmesh : T.mesh ≠ ∞) :
    dist (T.pos w) (nearestClosurePoint U hne (T.pos w)) ≤ 2 * T.mesh.toReal :=
  T.boundary_minimizer_dist_le hw hmesh
    (fun _ hz => nearestClosurePoint_dist_le_of_mem U hne (T.pos w) hz)

end BouRabeeGwynne.OrthogonalTiling
