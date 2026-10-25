module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Finite.Basic
public import SpherePackings.Support.Definitions.InteriorVertex
public import SpherePackings.Support.Definitions.ClosureVertex
public import SpherePackings.Support.Membership.MemClosedNeighborhood

@[expose] public section

open Finset
open scoped Classical

namespace SphereSBPALocal

variable {V : Type*} (G : SimpleGraph V) (A : Finset V)
  (hA : ∀ v ∈ A, (G.neighborSet v).Finite)

noncomputable def ofInterior (v : InteriorVertex A) : ClosureVertex G A hA :=
  ⟨v.1, (mem_closedNeighborhood G A hA).mpr (Or.inl v.2)⟩

end SphereSBPALocal
