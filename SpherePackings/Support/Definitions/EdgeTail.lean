module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Finite.Basic
public import SpherePackings.Support.Definitions.IncidentEdge
public import SpherePackings.Support.Definitions.ClosureVertex

@[expose] public section

open Finset
open scoped Classical

namespace SphereSBPALocal

variable {V : Type*} (G : SimpleGraph V) (A : Finset V)
  (hA : ∀ v ∈ A, (G.neighborSet v).Finite)

noncomputable def edgeTail (e : IncidentEdge G A hA) : ClosureVertex G A hA :=
  ⟨e.1.1, (Finset.mem_product.mp (Finset.mem_filter.mp e.2).1).1⟩

end SphereSBPALocal
