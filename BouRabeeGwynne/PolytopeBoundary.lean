-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/PolytopeBoundary.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.PaperObjects
import Mathlib.Analysis.Convex.Topology

namespace BouRabeeGwynne

/-- Full-dimensional convex cells are the closures of their interiors. -/
lemma ConvexPolytope.closure_interior {d : ℕ} (P : ConvexPolytope d) :
    closure (interior P.carrier) = P.carrier := by
  rw [P.convex.closure_interior_eq_closure_of_nonempty_interior P.interior_nonempty,
    P.compact.isClosed.closure_eq]

namespace TilingData

variable {d : ℕ} (T : TilingData d)

/-- No point of one closed cell is in the interior of a different cell. -/
lemma cell_disjoint_interior {v w : T.V} (hvw : v ≠ w) :
    Disjoint (T.cell v).carrier (interior (T.cell w).carrier) := by
  have h := (T.interiors_pairwise_disjoint hvw).closure_left isOpen_interior
  rwa [(T.cell v).closure_interior] at h

/-- Every cell contact is contained in the boundary of the first cell. -/
lemma facet_subset_frontier_left {v w : T.V} (hvw : v ≠ w) :
    T.facet v w ⊆ frontier (T.cell v).carrier := by
  intro x hx
  refine (mem_frontier_iff_notMem_interior hx.1).mpr ?_
  intro hxi
  exact Set.disjoint_left.mp (T.cell_disjoint_interior hvw.symm) hx.2 hxi

/-- Cell contacts are boundary pieces for both of their cells. -/
lemma facet_subset_frontiers {v w : T.V} (hvw : v ≠ w) :
    T.facet v w ⊆ frontier (T.cell v).carrier ∩ frontier (T.cell w).carrier := by
  intro x hx
  exact ⟨T.facet_subset_frontier_left hvw hx,
    T.facet_subset_frontier_left hvw.symm ⟨hx.2, hx.1⟩⟩

end TilingData
end BouRabeeGwynne
