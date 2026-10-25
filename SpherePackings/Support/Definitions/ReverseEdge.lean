module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Finite.Basic
public import SpherePackings.Support.Definitions.IncidentEdge
public import SpherePackings.Support.Membership.MemIncidentDirectedEdges

@[expose] public section

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
