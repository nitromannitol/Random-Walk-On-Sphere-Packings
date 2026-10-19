import SpherePackings.Support.Definitions.VertexBoundary
import SpherePackings.Support.Membership.MemVertexBoundary
import SpherePackings.Support.Definitions.OfInterior
import SpherePackings.Support.Definitions.EdgeTail
import SpherePackings.Support.Definitions.EdgeHead
import SpherePackings.Support.Definitions.ReverseEdge
import SpherePackings.Support.Definitions.IncomingDivergence
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

open Finset
open scoped Classical

namespace SphereSBPALocal

variable {V : Type*} (G : SimpleGraph V) (A : Finset V)
  (hA : ∀ v ∈ A, (G.neighborSet v).Finite)

private noncomputable def extendFunction (f : ClosureVertex G A hA → ℝ) (x : V) : ℝ :=
  if h : x ∈ closedNeighborhood G A hA then f ⟨x, h⟩ else 0

private noncomputable def extendField (θ : IncidentEdge G A hA → ℝ) (x y : V) : ℝ :=
  if h : (x, y) ∈ incidentDirectedEdges G A hA then θ ⟨(x, y), h⟩ else 0

private theorem extended_antisymm
    (θ : IncidentEdge G A hA → ℝ)
    (hθ : ∀ e : IncidentEdge G A hA, θ (reverseEdge G A hA e) = -θ e) :
    ∀ x y, extendField G A hA θ y x = -extendField G A hA θ x y := by
  classical
  let T := extendField G A hA θ
  have hT : ∀ e : IncidentEdge G A hA, T e.1.1 e.1.2 = θ e := by
    intro e
    exact dite_eq_left e.2
  have hTzero : ∀ x y, (x, y) ∉ incidentDirectedEdges G A hA → T x y = 0 := by
    intro x y h
    exact dite_eq_right h
  have hanti : ∀ x y, T y x = -T x y := by
    intro x y
    by_cases hxy : (x, y) ∈ incidentDirectedEdges G A hA
    · calc
        T y x = θ (reverseEdge G A hA ⟨(x, y), hxy⟩) :=
          hT (reverseEdge G A hA ⟨(x, y), hxy⟩)
        _ = -θ ⟨(x, y), hxy⟩ := hθ ⟨(x, y), hxy⟩
        _ = -T x y := congrArg Neg.neg (hT ⟨(x, y), hxy⟩).symm
    · have hyx : (y, x) ∉ incidentDirectedEdges G A hA := by
        intro h
        obtain ⟨ha, hb⟩ := (mem_incidentDirectedEdges G A hA).mp h
        exact hxy ((mem_incidentDirectedEdges G A hA).mpr
          ⟨ha.symm, hb.elim Or.inr Or.inl⟩)
      rw [hTzero x y hxy, hTzero y x hyx, neg_zero]
  exact hanti

private theorem incoming_eq_closure_sum (θ : IncidentEdge G A hA → ℝ)
    (v : InteriorVertex A) :
    incomingDivergence G A hA θ v =
      ∑ w ∈ closedNeighborhood G A hA, extendField G A hA θ w v.1 := by
  classical
  let S := closedNeighborhood G A hA
  let T := extendField G A hA θ
  have hT : ∀ e : IncidentEdge G A hA, T e.1.1 e.1.2 = θ e := by
    intro e
    exact dite_eq_left e.2
  have hTzero : ∀ x y, (x, y) ∉ incidentDirectedEdges G A hA → T x y = 0 := by
    intro x y h
    exact dite_eq_right h
  have hin : ∀ v : InteriorVertex A,
      incomingDivergence G A hA θ v = ∑ w ∈ S, T w v.1 := by
    intro v
    calc
      _ = ∑ w : {x : V // x ∈ (hA v.1 v.2).toFinset}, T w.1 v.1 := by
        exact Finset.sum_congr rfl fun w _ => (hT (incomingEdge G A hA v w)).symm
      _ = ∑ w ∈ (hA v.1 v.2).toFinset, T w v.1 :=
        Finset.sum_coe_sort _ (fun w => T w v.1)
      _ = ∑ w ∈ S, T w v.1 := by
        refine Finset.sum_subset ?_ ?_
        · intro w hw
          exact (mem_closedNeighborhood G A hA).mpr
            (Or.inr ⟨v.1, v.2, (hA v.1 v.2).mem_toFinset.mp hw⟩)
        · intro w _ hw
          apply hTzero
          intro he
          exact hw ((hA v.1 v.2).mem_toFinset.mpr
            ((mem_incidentDirectedEdges G A hA).mp he).1.symm)
  exact hin v

private theorem lhs_eq_finite_sum
    (f : ClosureVertex G A hA → ℝ) (θ : IncidentEdge G A hA → ℝ) :
    (∑ v : InteriorVertex A, incomingDivergence G A hA θ v * f (ofInterior G A hA v)) =
      ∑ v ∈ A, extendFunction G A hA f v *
        ∑ w ∈ closedNeighborhood G A hA, extendField G A hA θ w v := by
  classical
  let S := closedNeighborhood G A hA
  let F := extendFunction G A hA f
  let T := extendField G A hA θ
  have hF : ∀ v : ClosureVertex G A hA, F v.1 = f v := by
    intro v
    exact dite_eq_left v.2
  have hin := incoming_eq_closure_sum G A hA θ
  have hleft :
      (∑ v : InteriorVertex A, incomingDivergence G A hA θ v * f (ofInterior G A hA v))
        = ∑ v ∈ A, F v * ∑ w ∈ S, T w v := by
    calc
      _ = ∑ v : InteriorVertex A, F v.1 * ∑ w ∈ S, T w v.1 := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [hin v, ← hF (ofInterior G A hA v)]
        exact mul_comm _ _
      _ = _ := Finset.sum_coe_sort A (fun v => F v * ∑ w ∈ S, T w v)
  exact hleft

private theorem rhs_eq_double_sum
    (f : ClosureVertex G A hA → ℝ) (θ : IncidentEdge G A hA → ℝ) :
    (∑ e : IncidentEdge G A hA,
      θ e * (f (edgeTail G A hA e) - f (edgeHead G A hA e))) =
      ∑ x ∈ closedNeighborhood G A hA, ∑ y ∈ closedNeighborhood G A hA,
        extendField G A hA θ x y *
          (extendFunction G A hA f x - extendFunction G A hA f y) := by
  classical
  let S := closedNeighborhood G A hA
  let F := extendFunction G A hA f
  let T := extendField G A hA θ
  have hF : ∀ v : ClosureVertex G A hA, F v.1 = f v := by
    intro v
    exact dite_eq_left v.2
  have hT : ∀ e : IncidentEdge G A hA, T e.1.1 e.1.2 = θ e := by
    intro e
    exact dite_eq_left e.2
  have hTzero : ∀ x y, (x, y) ∉ incidentDirectedEdges G A hA → T x y = 0 := by
    intro x y h
    exact dite_eq_right h
  have hES : incidentDirectedEdges G A hA ⊆ S.product S :=
    Finset.filter_subset _ _
  change (∑ e : IncidentEdge G A hA,
    θ e * (f (edgeTail G A hA e) - f (edgeHead G A hA e))) =
      ∑ x ∈ S, ∑ y ∈ S, T x y * (F x - F y)
  clear_value S F T
  have hright :
      (∑ e : IncidentEdge G A hA, θ e * (f (edgeTail G A hA e) - f (edgeHead G A hA e)))
        = ∑ x ∈ S, ∑ y ∈ S, T x y * (F x - F y) := by
    calc
      _ = ∑ e : IncidentEdge G A hA, T e.1.1 e.1.2 * (F e.1.1 - F e.1.2) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [hT e, ← hF (edgeTail G A hA e), ← hF (edgeHead G A hA e)]
        rfl
      _ = ∑ e ∈ incidentDirectedEdges G A hA, T e.1 e.2 * (F e.1 - F e.2) :=
        Finset.sum_coe_sort _ (fun e : V × V => T e.1 e.2 * (F e.1 - F e.2))
      _ = ∑ e ∈ S.product S, T e.1 e.2 * (F e.1 - F e.2) := by
        refine Finset.sum_subset hES ?_
        intro e _ he
        rw [hTzero e.1 e.2 he, zero_mul]
      _ = _ := Finset.sum_product _ _ _
  exact hright

private theorem finite_matrix_sbp (S B : Finset V) (F : V → ℝ) (T : V → V → ℝ)
    (hAS : B ⊆ S) (hFzero : ∀ x, x ∉ B → F x = 0)
    (hanti : ∀ x y, T y x = -T x y) :
    (∑ v ∈ B, F v * ∑ w ∈ S, T w v) =
      -(1 / 2 : ℝ) * ∑ x ∈ S, ∑ y ∈ S, T x y * (F x - F y) := by
  classical
  have hrestrict : (∑ v ∈ S, F v * ∑ w ∈ S, T w v) =
      ∑ v ∈ B, F v * ∑ w ∈ S, T w v := by
    refine (Finset.sum_subset hAS ?_).symm
    intro v _ hv
    rw [hFzero v hv, zero_mul]
  have hswap : (∑ x ∈ S, ∑ y ∈ S, T x y * F x) =
      -(∑ y ∈ S, F y * ∑ x ∈ S, T x y) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun y _ => by rw [hanti x y]; ring
  have hhead : (∑ x ∈ S, ∑ y ∈ S, T x y * F y) =
      ∑ y ∈ S, F y * ∑ x ∈ S, T x y := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => mul_comm _ _
  have hsplit : (∑ x ∈ S, ∑ y ∈ S, T x y * (F x - F y)) =
      (∑ x ∈ S, ∑ y ∈ S, T x y * F x) -
      (∑ x ∈ S, ∑ y ∈ S, T x y * F y) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hsplit, hswap, hhead, hrestrict]
  ring

/-- Incoming-divergence SBP with finite degrees required only on A. -/
theorem discrete_summation_by_parts
    (f : ClosureVertex G A hA → ℝ)
    (hf : ∀ v : ClosureVertex G A hA, v.1 ∈ vertexBoundary G A hA → f v = 0)
    (θ : IncidentEdge G A hA → ℝ)
    (hθ : ∀ e : IncidentEdge G A hA, θ (reverseEdge G A hA e) = -θ e) :
    (∑ v : InteriorVertex A, incomingDivergence G A hA θ v * f (ofInterior G A hA v))
      = -(1 / 2 : ℝ) *
        ∑ e : IncidentEdge G A hA,
          θ e * (f (edgeTail G A hA e) - f (edgeHead G A hA e)) := by
  classical
  let S := closedNeighborhood G A hA
  let F := extendFunction G A hA f
  let T := extendField G A hA θ
  have hAS : A ⊆ S := fun x hx => (mem_closedNeighborhood G A hA).mpr (Or.inl hx)
  have hFzero : ∀ x, x ∉ A → F x = 0 := by
    intro x hx
    by_cases hc : x ∈ closedNeighborhood G A hA
    · exact (dite_eq_left hc).trans (hf ⟨x, hc⟩ (Finset.mem_sdiff.mpr ⟨hc, hx⟩))
    · exact dite_eq_right hc
  rw [lhs_eq_finite_sum, rhs_eq_double_sum]
  exact finite_matrix_sbp S A F T hAS hFzero (extended_antisymm G A hA θ hθ)

end SphereSBPALocal
