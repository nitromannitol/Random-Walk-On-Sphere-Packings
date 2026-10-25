module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Finite.Basic
public import SpherePackings.Support.Definitions.IncomingEdge

@[expose] public section

open Finset
open scoped Classical

namespace SphereSBPALocal

variable {V : Type*} (G : SimpleGraph V) (A : Finset V)
  (hA : ∀ v ∈ A, (G.neighborSet v).Finite)

noncomputable def incomingDivergence (θ : IncidentEdge G A hA → ℝ)
    (v : InteriorVertex A) : ℝ :=
  ∑ w : {x : V // x ∈ (hA v.1 v.2).toFinset}, θ (incomingEdge G A hA v w)

end SphereSBPALocal
