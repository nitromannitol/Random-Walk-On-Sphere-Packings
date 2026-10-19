import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Set.Finite.Basic
import SpherePackings.Support.Definitions.IncidentDirectedEdges
import SpherePackings.Support.Membership.MemClosedNeighborhood

open Finset
open scoped Classical

namespace SphereSBPALocal

variable {V : Type*} (G : SimpleGraph V) (A : Finset V)
  (hA : ∀ v ∈ A, (G.neighborSet v).Finite)

theorem mem_incidentDirectedEdges {x y : V} :
    (x, y) ∈ incidentDirectedEdges G A hA ↔ G.Adj x y ∧ (x ∈ A ∨ y ∈ A) := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · rintro ⟨hxy, hEndpoints⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hxy, hEndpoints⟩
    · rcases hEndpoints with hx | hy
      · exact (mem_closedNeighborhood G A hA).mpr (Or.inl hx)
      · exact (mem_closedNeighborhood G A hA).mpr (Or.inr ⟨y, hy, hxy.symm⟩)
    · rcases hEndpoints with hx | hy
      · exact (mem_closedNeighborhood G A hA).mpr (Or.inr ⟨x, hx, hxy⟩)
      · exact (mem_closedNeighborhood G A hA).mpr (Or.inl hy)

end SphereSBPALocal
