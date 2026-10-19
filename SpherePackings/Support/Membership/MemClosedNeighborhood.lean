import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Set.Finite.Basic
import SpherePackings.Support.Definitions.ClosedNeighborhood

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
