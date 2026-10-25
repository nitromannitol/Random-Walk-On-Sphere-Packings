module

-- Built on Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne (commit cf73d6e).
public import BouRabeeGwynne.DualDirichlet

@[expose] public section

/-!
# Lemma 2.3: the dual variational principle

`rw-spheres.tex:684-707` (label `lemma:dual-variational-principle`).  The sums run over the directed
edges `E[Ā]` with at least one endpoint in `A`; the vector field `θ` is defined on those edges, i.e.
vanishes elsewhere.
-/

open scoped BigOperators

namespace SpherePackings

open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork

/-- Directed edges with at least one endpoint in `A`: the set `E[Ā]` of the paper. -/
def IsIncidentEdge {V : Type*} [Fintype V] (N : FiniteConductanceNetwork V) (A : Set V)
    (w v : V) : Prop :=
  0 < N.a w v ∧ (w ∈ A ∨ v ∈ A)

open Classical in
/-- A sum over `E[Ā]` equals the full sum when the summand vanishes off `E[Ā]`. -/
private lemma sum_incident_eq {V : Type*} [Fintype V] (N : FiniteConductanceNetwork V) (A : Set V)
    (F : V → V → ℝ) (hF : ∀ w v, ¬ IsIncidentEdge N A w v → F w v = 0) :
    (∑ v, ∑ w, if IsIncidentEdge N A w v then F w v else 0) = ∑ v, ∑ w, F w v := by
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => ?_
  by_cases h : IsIncidentEdge N A w v
  · simp [h]
  · simp [h, hF w v h]

/-- The weighted gradient vanishes on directed edges outside `E[Ā]`, since `f` vanishes off `A`. -/
private lemma weightedGradient_eq_zero_of_not_incident {V : Type*} [Fintype V]
    (N : FiniteConductanceNetwork V) (A : Set V) (f : V → ℝ) (hf : ∀ v, v ∉ A → f v = 0)
    (w v : V) (h : ¬ IsIncidentEdge N A w v) : N.weightedGradient f w v = 0 := by
  unfold IsIncidentEdge at h
  rcases (N.nonneg w v).eq_or_lt with ha | ha
  · simp [weightedGradient, ← ha]
  · have hw : w ∉ A := fun hw => h ⟨ha, Or.inl hw⟩
    have hv : v ∉ A := fun hv => h ⟨ha, Or.inr hv⟩
    simp [weightedGradient, discreteGrad, hf w hw, hf v hv]

open Classical in
/-- **Lemma 2.3** (`lemma:dual-variational-principle`).  If `f` vanishes off `A` and the vector field
`θ` on `E[Ā]` has the divergence of `∇_a f` on `A`, then
`∑_{e ∈ E[Ā]} a(e)⁻¹ |∇_a f(e)|² ≤ ∑_{e ∈ E[Ā]} a(e)⁻¹ θ(e)²`. -/
theorem dual_variational_principle_incident {V : Type*} [Fintype V] [DecidableEq V]
    (N : FiniteConductanceNetwork V) (A : Set V) [DecidablePred (· ∈ A)]
    (f : V → ℝ) (hf : ∀ v, v ∉ A → f v = 0)
    (θ : V → V → ℝ) (hθ : IsDiscreteVectorField θ)
    (hsupp : ∀ w v, ¬ IsIncidentEdge N A w v → θ w v = 0)
    (hdiv : ∀ v ∈ A, discreteDiv θ v = discreteDiv (N.weightedGradient f) v) :
    (∑ v, ∑ w, if IsIncidentEdge N A w v then (N.weightedGradient f w v) ^ 2 / N.a w v else 0) ≤
      ∑ v, ∑ w, if IsIncidentEdge N A w v then (θ w v) ^ 2 / N.a w v else 0 := by
  have hL := sum_incident_eq N A (fun w v => N.weightedGradient f w v ^ 2 / N.a w v)
    (fun w v h => by simp [weightedGradient_eq_zero_of_not_incident N A f hf w v h])
  have hR := sum_incident_eq N A (fun w v => θ w v ^ 2 / N.a w v)
    (fun w v h => by simp [hsupp w v h])
  have hsupport : ∀ w v, N.a w v = 0 → θ w v = 0 := fun w v ha =>
    hsupp w v fun h => h.1.ne' ha
  rw [hL, hR]
  exact dual_variational_principle N A f θ hθ hsupport hf hdiv

end SpherePackings
