-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/Section3GraphPaths.lean` at commit cf73d6e); unchanged apart from this header.
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic

/-!
# Section 3: telescoping along boundary-reaching column paths

The pointwise part of Lemma 3.1 uses a path to the graph boundary, rather than
connectedness of an entire column. Loop erasure gives a path with no repeated
edges, so its total variation is bounded by the variation over all graph edges.
A strictly increasing score at each interior vertex supplies such a path in
any finite graph; column geometry will supply the score from fiber endpoints.
-/

open scoped BigOperators Classical

namespace BouRabeeGwynne

/-- Absolute variation on an unordered edge. -/
def unorderedEdgeVariation {V : Type*} (f : V → ℝ) (e : Sym2 V) : ℝ :=
  Sym2.lift ⟨fun v w => |f v - f w|, fun _ _ => abs_sub_comm _ _⟩ e

@[simp] lemma unorderedEdgeVariation_mk {V : Type*} (f : V → ℝ) (v w : V) :
    unorderedEdgeVariation f s(v, w) = |f v - f w| := rfl

lemma unorderedEdgeVariation_nonneg {V : Type*} (f : V → ℝ) (e : Sym2 V) :
    0 ≤ unorderedEdgeVariation f e := by
  induction e using Sym2.inductionOn with
  | hf v w => exact abs_nonneg _

/-- Telescoping and the triangle inequality along an actual graph walk. -/
lemma abs_sub_le_walk_variation {V : Type*} {G : SimpleGraph V} (f : V → ℝ)
    {v w : V} (p : G.Walk v w) :
    |f v - f w| ≤ (p.edges.map (unorderedEdgeVariation f)).sum := by
  induction p with
  | nil => simp
  | @cons v u w h p ih =>
    simp only [SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons,
      unorderedEdgeVariation_mk]
    exact (abs_sub_le (f v) (f u) (f w)).trans (add_le_add_right ih _)

/-- A reachable vertex pair is controlled by the variation on all unordered
edges, with each edge counted once. -/
theorem abs_sub_le_graph_variation {V : Type*} [Fintype V] (G : SimpleGraph V)
    (f : V → ℝ) {v w : V} (hvw : G.Reachable v w) :
    |f v - f w| ≤ ∑ e ∈ G.edgeFinset, unorderedEdgeVariation f e := by
  apply hvw.elim_path
  intro p
  have hp := abs_sub_le_walk_variation f p.val
  rw [← List.sum_toFinset _ p.isTrail.edges_nodup] at hp
  apply hp.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    exact SimpleGraph.mem_edgeFinset.mpr
      (p.val.edges_subset_edgeSet (List.mem_toFinset.mp he))
  · intro e _ _
    exact unorderedEdgeVariation_nonneg f e

/-- The deterministic boundary-reaching ingredient of the column inequality. -/
theorem abs_le_graph_variation_of_boundary_path {V : Type*} [Fintype V]
    (G : SimpleGraph V) (A : Set V) (f : V → ℝ)
    (hzero : ∀ w, w ∉ A → f w = 0) {v : V}
    (hpath : ∃ w, w ∉ A ∧ G.Reachable v w) :
    |f v| ≤ ∑ e ∈ G.edgeFinset, unorderedEdgeVariation f e := by
  obtain ⟨w, hw, hvw⟩ := hpath
  simpa only [hzero w hw, sub_zero] using abs_sub_le_graph_variation G f hvw

/-- Strictly increasing neighbors cannot remain forever inside a finite graph.
This is a structural way to obtain the boundary paths needed for columns. -/
theorem boundary_path_of_increasing_neighbor {V : Type*} [Fintype V]
    (G : SimpleGraph V) (A : Set V) (score : V → ℝ)
    (hup : ∀ v ∈ A, ∃ w, G.Adj v w ∧ score v < score w) :
    ∀ v ∈ A, ∃ w, w ∉ A ∧ G.Reachable v w := by
  intro v _
  by_contra hno
  have hinside : ∀ w, G.Reachable v w → w ∈ A := by
    intro w hw
    by_contra hwA
    exact hno ⟨w, hwA, hw⟩
  let R : Finset V := Finset.univ.filter (G.Reachable v)
  have hvR : v ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ v, .rfl⟩
  obtain ⟨m, hmR, hmax⟩ := Finset.exists_max_image R score ⟨v, hvR⟩
  have hmreach : G.Reachable v m := (Finset.mem_filter.mp hmR).2
  obtain ⟨w, hmw, hscore⟩ := hup m (hinside m hmreach)
  have hwR : w ∈ R := Finset.mem_filter.mpr
    ⟨Finset.mem_univ w, hmreach.trans hmw.reachable⟩
  exact (not_lt_of_ge (hmax w hwR)) hscore

end BouRabeeGwynne
