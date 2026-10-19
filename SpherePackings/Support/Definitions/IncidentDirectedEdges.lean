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

noncomputable def incidentDirectedEdges : Finset (V × V) :=
  ((closedNeighborhood G A hA).product (closedNeighborhood G A hA)).filter
    (fun e => G.Adj e.1 e.2 ∧ (e.1 ∈ A ∨ e.2 ∈ A))

end SphereSBPALocal
