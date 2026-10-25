module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Finite.Basic
public import SpherePackings.Support.Definitions.VertexBoundary
public import SpherePackings.Support.Membership.MemClosedNeighborhood

@[expose] public section

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
