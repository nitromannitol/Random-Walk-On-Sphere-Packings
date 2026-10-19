import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Set.Finite.Basic
import SpherePackings.Support.Definitions.IncomingEdge

open Finset
open scoped Classical

namespace SphereSBPALocal

variable {V : Type*} (G : SimpleGraph V) (A : Finset V)
  (hA : ∀ v ∈ A, (G.neighborSet v).Finite)

noncomputable def incomingDivergence (θ : IncidentEdge G A hA → ℝ)
    (v : InteriorVertex A) : ℝ :=
  ∑ w : {x : V // x ∈ (hA v.1 v.2).toFinset}, θ (incomingEdge G A hA v w)

end SphereSBPALocal
