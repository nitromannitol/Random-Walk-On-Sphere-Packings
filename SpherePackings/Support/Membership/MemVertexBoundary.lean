import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Set.Finite.Basic
import SpherePackings.Support.Definitions.VertexBoundary
import SpherePackings.Support.Membership.MemClosedNeighborhood

open Finset
open scoped Classical

namespace SphereSBPALocal

variable {V : Type*} (G : SimpleGraph V) (A : Finset V)
  (hA : ∀ v ∈ A, (G.neighborSet v).Finite)

theorem mem_vertexBoundary {x : V} :
    x ∈ vertexBoundary G A hA ↔ x ∉ A ∧ ∃ a ∈ A, G.Adj a x := by
  simp only [vertexBoundary, Finset.mem_sdiff, mem_closedNeighborhood]
  tauto

end SphereSBPALocal
