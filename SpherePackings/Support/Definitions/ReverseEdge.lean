import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Set.Finite.Basic
import SpherePackings.Support.Definitions.IncidentEdge
import SpherePackings.Support.Membership.MemIncidentDirectedEdges

open Finset
open scoped Classical

namespace SphereSBPALocal

variable {V : Type*} (G : SimpleGraph V) (A : Finset V)
  (hA : ∀ v ∈ A, (G.neighborSet v).Finite)

noncomputable def reverseEdge (e : IncidentEdge G A hA) : IncidentEdge G A hA :=
  ⟨(e.1.2, e.1.1), by
    obtain ⟨h, ha⟩ := (mem_incidentDirectedEdges G A hA).mp e.2
    exact (mem_incidentDirectedEdges G A hA).mpr ⟨h.symm, ha.elim Or.inr Or.inl⟩⟩

end SphereSBPALocal
