module

/-
Lemma 2.3 of rw-spheres.tex, frozen.

Paper statement, `rw-spheres.tex:684-690` (label `lemma:dual-variational-principle`): for a finite
set `A`, `f` zero on `∂A` and a vector field `θ` on `E[Ā]` with `div θ = div(∇_a f)` on `A`,
`∑_{e ∈ E[Ā]} a(e)⁻¹ |∇_a f(e)|² ≤ ∑_{e ∈ E[Ā]} a(e)⁻¹ θ(e)²`.

Stated for a finite network with arbitrary symmetric nonnegative conductances (the tiling
conductances on a finite set of vertices are one); `E[Ā]` is the set of directed edges of positive
conductance with an endpoint in `A`, and `θ` vanishes off it.  Proved from leobon12's dual
variational lemmas.
-/
public import SpherePackings.Support.Section2.DualVariational

@[expose] public section

open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork SpherePackings
open scoped BigOperators

open Classical in
-- FROZEN-STATEMENT-BEGIN
theorem SpherePackings.Frozen.lemma23_dual_variational {V : Type*} [Fintype V] [DecidableEq V]
    (N : FiniteConductanceNetwork V) (A : Set V) [DecidablePred (· ∈ A)]
    (f : V → ℝ) (hf : ∀ v, v ∉ A → f v = 0)
    (θ : V → V → ℝ) (hθ : IsDiscreteVectorField θ)
    (hsupp : ∀ w v, ¬ IsIncidentEdge N A w v → θ w v = 0)
    (hdiv : ∀ v ∈ A, discreteDiv θ v = discreteDiv (N.weightedGradient f) v) :
    (∑ v, ∑ w, if IsIncidentEdge N A w v then (N.weightedGradient f w v) ^ 2 / N.a w v else 0) ≤
      ∑ v, ∑ w, if IsIncidentEdge N A w v then (θ w v) ^ 2 / N.a w v else 0
-- FROZEN-STATEMENT-END
:= SpherePackings.dual_variational_principle_incident N A f hf θ hθ hsupp hdiv
