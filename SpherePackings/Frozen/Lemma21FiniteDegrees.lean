/-
Lemma 2.1 of rw-spheres.tex, frozen.

Paper statement, `rw-spheres.tex:633-640` (label `lemma:discrete-divergence-theorem`): for a finite
set `A` of vertices, `f : Ā → ℝ` zero on `∂A` and a vector field `θ` on `E[Ā]`,
`∑_{v ∈ A} (div θ)(v) f(v) = -1/2 ∑_{e ∈ E[Ā]} θ(e) ∇f(e)`.

Added hypothesis, for well-posedness: every vertex of `A` has finite degree, so that the divergence
and the edge sum are finite sums.  The paper states the lemma "for general graphs"; at the centre of
an infinite star the divergence is an infinite sum.  Boundary vertices may have infinite degree.
Stated for an arbitrary simple graph.
-/
import SpherePackings.Providers.Lemma21FiniteDegrees

open Finset
open scoped Classical
open SphereSBPALocal

-- FROZEN-STATEMENT-BEGIN
theorem SpherePackings.Frozen.lemma21FiniteDegrees {V : Type*} (G : SimpleGraph V) (A : Finset V)
    (hA : ∀ v ∈ A, (G.neighborSet v).Finite)
    (f : ClosureVertex G A hA → ℝ)
    (hf : ∀ v : ClosureVertex G A hA, v.1 ∈ vertexBoundary G A hA → f v = 0)
    (θ : IncidentEdge G A hA → ℝ)
    (hθ : ∀ e : IncidentEdge G A hA, θ (reverseEdge G A hA e) = -θ e) :
    (∑ v : InteriorVertex A, incomingDivergence G A hA θ v * f (ofInterior G A hA v))
      = -(1 / 2 : ℝ) *
        ∑ e : IncidentEdge G A hA,
          θ e * (f (edgeTail G A hA e) - f (edgeHead G A hA e))
-- FROZEN-STATEMENT-END
:= by
  exact SpherePackings.Providers.lemma21FiniteDegrees G A hA f hf θ hθ

