import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Set.Finite.Basic
import SpherePackings.Support.Definitions.IncidentEdge
import SpherePackings.Support.Definitions.ClosureVertex

open Finset
open scoped Classical

namespace SphereSBPALocal

variable {V : Type*} (G : SimpleGraph V) (A : Finset V)
  (hA : ∀ v ∈ A, (G.neighborSet v).Finite)

noncomputable def edgeTail (e : IncidentEdge G A hA) : ClosureVertex G A hA :=
  ⟨e.1.1, (Finset.mem_product.mp (Finset.mem_filter.mp e.2).1).1⟩

end SphereSBPALocal
