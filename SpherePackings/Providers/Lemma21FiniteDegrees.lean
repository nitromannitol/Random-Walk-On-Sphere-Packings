import SpherePackings.Support.ALocalProof

open Finset
open scoped Classical
open SphereSBPALocal

namespace SpherePackings.Providers

variable {V : Type*} (G : SimpleGraph V) (A : Finset V)
  (hA : ∀ v ∈ A, (G.neighborSet v).Finite)

theorem lemma21FiniteDegrees
    (f : ClosureVertex G A hA → ℝ)
    (hf : ∀ v : ClosureVertex G A hA, v.1 ∈ vertexBoundary G A hA → f v = 0)
    (θ : IncidentEdge G A hA → ℝ)
    (hθ : ∀ e : IncidentEdge G A hA, θ (reverseEdge G A hA e) = -θ e) :
    (∑ v : InteriorVertex A, incomingDivergence G A hA θ v * f (ofInterior G A hA v))
      = -(1 / 2 : ℝ) *
        ∑ e : IncidentEdge G A hA,
          θ e * (f (edgeTail G A hA e) - f (edgeHead G A hA e)) := by
  exact SphereSBPALocal.discrete_summation_by_parts G A hA f hf θ hθ

end SpherePackings.Providers
