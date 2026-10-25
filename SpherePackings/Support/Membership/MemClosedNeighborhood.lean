module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Finite.Basic
public import SpherePackings.Support.Definitions.ClosedNeighborhood

@[expose] public section

open Finset
open scoped Classical

namespace SphereSBPALocal

variable {V : Type*} (G : SimpleGraph V) (A : Finset V)
  (hA : ∀ v ∈ A, (G.neighborSet v).Finite)

theorem mem_closedNeighborhood {x : V} :
    x ∈ closedNeighborhood G A hA ↔ x ∈ A ∨ ∃ a ∈ A, G.Adj a x := by
  simp only [closedNeighborhood, Finset.mem_union, Finset.mem_biUnion,
    Set.Finite.mem_toFinset, Finset.mem_attach, true_and, Subtype.exists,
    SimpleGraph.mem_neighborSet, exists_prop]

end SphereSBPALocal
