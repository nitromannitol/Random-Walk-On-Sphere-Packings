module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Finite.Basic
public import SpherePackings.Support.Definitions.InteriorVertex
public import SpherePackings.Support.Definitions.IncidentEdge
public import SpherePackings.Support.Membership.MemIncidentDirectedEdges

@[expose] public section

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
