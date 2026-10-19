import SpherePackings.Frozen.Lemma21FiniteDegrees

open Finset
open scoped Classical

namespace SphereSBPALocal.InfiniteStarCheck

def graph : SimpleGraph ℕ where
  Adj x y := (x = 0 ∧ y ≠ 0) ∨ (y = 0 ∧ x ≠ 0)
  symm := ⟨by
    intro x y h
    exact h.elim Or.inr Or.inl⟩
  loopless := ⟨by
    intro x h
    rcases h with h | h
    · exact h.2 h.1
    · exact h.2 h.1⟩

noncomputable def region : Finset ℕ := {1}

theorem neighbors_leaf : graph.neighborSet 1 = {0} := by
  ext n
  simp [SimpleGraph.mem_neighborSet, graph]

theorem finiteDegrees : ∀ v ∈ region, (graph.neighborSet v).Finite := by
  intro v hv
  have hv1 : v = 1 := by simpa only [region, Finset.mem_singleton] using hv
  subst v
  rw [neighbors_leaf]
  exact Set.finite_singleton 0

theorem center_infinite_degree : ¬ (graph.neighborSet 0).Finite := by
  intro h
  apply Set.infinite_range_of_injective Nat.succ_injective
  apply h.subset
  rintro n ⟨k, rfl⟩
  simp [SimpleGraph.mem_neighborSet, graph]

noncomputable def potential (v : ClosureVertex graph region finiteDegrees) : ℝ :=
  if v.1 = 1 then 2 else 0

noncomputable def field (e : IncidentEdge graph region finiteDegrees) : ℝ :=
  3 * ((if e.1.1 = 1 then 1 else 0) - (if e.1.2 = 1 then 1 else 0))

theorem potential_boundary_zero :
    ∀ v : ClosureVertex graph region finiteDegrees,
      v.1 ∈ vertexBoundary graph region finiteDegrees → potential v = 0 := by
  intro v hv
  have hn : v.1 ≠ 1 := by
    have := ((mem_vertexBoundary graph region finiteDegrees).mp hv).1
    simpa only [region, Finset.mem_singleton] using this
  exact ite_eq_right hn

theorem field_antisymmetric :
    ∀ e : IncidentEdge graph region finiteDegrees,
      field (reverseEdge graph region finiteDegrees e) = -field e := by
  intro e
  dsimp only [field, reverseEdge]
  ring

theorem center_boundary : 0 ∈ vertexBoundary graph region finiteDegrees := by
  rw [mem_vertexBoundary]
  refine ⟨by simp [region], 1, by simp [region], ?_⟩
  simp [graph]

theorem closure_pair : closedNeighborhood graph region finiteDegrees = {0, 1} := by
  ext n
  simp [mem_closedNeighborhood, region, graph]
  tauto

theorem edges_pair : incidentDirectedEdges graph region finiteDegrees = {(0, 1), (1, 0)} := by
  ext e
  rcases e with ⟨x, y⟩
  simp only [mem_incidentDirectedEdges, region, Finset.mem_singleton,
    Finset.mem_insert, Prod.mk.injEq]
  change ((x = 0 ∧ y ≠ 0) ∨ (y = 0 ∧ x ≠ 0)) ∧ (x = 1 ∨ y = 1) ↔
    (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0)
  constructor
  · rintro ⟨(⟨rfl, hy⟩ | ⟨rfl, hx⟩), h⟩ <;> simp_all
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

noncomputable def interior : InteriorVertex region := ⟨1, by simp [region]⟩

theorem interior_unique (v : InteriorVertex region) : v = interior := by
  apply Subtype.ext
  change v.1 = 1
  simpa only [region, Finset.mem_singleton] using v.2

theorem incoming_value : incomingDivergence graph region finiteDegrees field interior = -3 := by
  have hn : (finiteDegrees interior.1 interior.2).toFinset = {0} := by
    ext n
    simp only [Set.Finite.mem_toFinset, interior, neighbors_leaf, Set.mem_singleton_iff,
      Finset.mem_singleton]
  calc
    _ = ∑ w ∈ (finiteDegrees interior.1 interior.2).toFinset,
        (3 : ℝ) * ((if w = 1 then 1 else 0) - (if interior.1 = 1 then 1 else 0)) :=
      Finset.sum_coe_sort _ (fun w =>
        (3 : ℝ) * ((if w = 1 then 1 else 0) - (if interior.1 = 1 then 1 else 0)))
    _ = -3 := by rw [hn]; norm_num [interior]

theorem lhs_value :
    (∑ v : InteriorVertex region,
      incomingDivergence graph region finiteDegrees field v *
        potential (ofInterior graph region finiteDegrees v)) = -6 := by
  have hs : (∑ v : InteriorVertex region,
      incomingDivergence graph region finiteDegrees field v *
        potential (ofInterior graph region finiteDegrees v)) =
      incomingDivergence graph region finiteDegrees field interior *
        potential (ofInterior graph region finiteDegrees interior) := by
    apply Finset.sum_eq_single interior
    · intro v _ hv
      exact (hv (interior_unique v)).elim
    · intro hv
      exact (hv (Finset.mem_univ interior)).elim
  rw [hs, incoming_value]
  norm_num [potential, ofInterior, interior]

-- Independent raw-sum computation: does not consume the SBP theorem.
theorem raw_edge_sum :
    (∑ e : IncidentEdge graph region finiteDegrees,
      field e * (potential (edgeTail graph region finiteDegrees e) -
        potential (edgeHead graph region finiteDegrees e))) = 12 := by
  calc
    _ = ∑ e ∈ incidentDirectedEdges graph region finiteDegrees,
        (3 : ℝ) * ((if e.1 = 1 then 1 else 0) - (if e.2 = 1 then 1 else 0)) *
          ((if e.1 = 1 then 2 else 0) - (if e.2 = 1 then 2 else 0)) :=
      Finset.sum_coe_sort _ (fun e : ℕ × ℕ =>
        (3 : ℝ) * ((if e.1 = 1 then 1 else 0) - (if e.2 = 1 then 1 else 0)) *
          ((if e.1 = 1 then 2 else 0) - (if e.2 = 1 then 2 else 0)))
    _ = 12 := by rw [edges_pair]; norm_num

theorem rhs_value :
    -(1 / 2 : ℝ) * (∑ e : IncidentEdge graph region finiteDegrees,
      field e * (potential (edgeTail graph region finiteDegrees e) -
        potential (edgeHead graph region finiteDegrees e))) = -6 := by
  rw [raw_edge_sum]
  norm_num

theorem checked_identity :
    (∑ v : InteriorVertex region,
      incomingDivergence graph region finiteDegrees field v *
        potential (ofInterior graph region finiteDegrees v)) =
    -(1 / 2 : ℝ) * ∑ e : IncidentEdge graph region finiteDegrees,
      field e * (potential (edgeTail graph region finiteDegrees e) -
        potential (edgeHead graph region finiteDegrees e)) :=
  SpherePackings.Frozen.lemma21FiniteDegrees graph region finiteDegrees potential potential_boundary_zero
    field field_antisymmetric

end SphereSBPALocal.InfiniteStarCheck
