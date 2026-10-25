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

noncomputable def incidentDirectedEdges : Finset (V × V) :=
  ((closedNeighborhood G A hA).product (closedNeighborhood G A hA)).filter
    (fun e => G.Adj e.1 e.2 ∧ (e.1 ∈ A ∨ e.2 ∈ A))

end SphereSBPALocal
