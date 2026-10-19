import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Set.Finite.Basic
import SpherePackings.Support.Definitions.InteriorVertex
import SpherePackings.Support.Definitions.ClosureVertex
import SpherePackings.Support.Membership.MemClosedNeighborhood

open Finset
open scoped Classical

namespace SphereSBPALocal

variable {V : Type*} (G : SimpleGraph V) (A : Finset V)
  (hA : ∀ v ∈ A, (G.neighborSet v).Finite)

noncomputable def ofInterior (v : InteriorVertex A) : ClosureVertex G A hA :=
  ⟨v.1, (mem_closedNeighborhood G A hA).mpr (Or.inl v.2)⟩

end SphereSBPALocal
