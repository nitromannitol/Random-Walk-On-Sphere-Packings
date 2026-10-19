import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Set.Finite.Basic
import SpherePackings.Support.Definitions.InteriorVertex
import SpherePackings.Support.Definitions.IncidentEdge
import SpherePackings.Support.Membership.MemIncidentDirectedEdges

open Finset
open scoped Classical

namespace SphereSBPALocal

variable {V : Type*} (G : SimpleGraph V) (A : Finset V)
  (hA : ∀ v ∈ A, (G.neighborSet v).Finite)

noncomputable def incomingEdge (v : InteriorVertex A)
    (w : {x : V // x ∈ (hA v.1 v.2).toFinset}) : IncidentEdge G A hA :=
  ⟨(w.1, v.1), (mem_incidentDirectedEdges G A hA).mpr
    ⟨((hA v.1 v.2).mem_toFinset.mp w.2).symm, Or.inr v.2⟩⟩

end SphereSBPALocal
