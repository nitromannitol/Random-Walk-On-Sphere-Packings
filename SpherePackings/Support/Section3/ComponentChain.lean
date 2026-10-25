module

-- Built on Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne (commit cf73d6e).
public import BouRabeeGwynne.PaperObjects
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

/-!
# Chains of adjacent cells

Along a walk of adjacent cells, a function that is `L`-Lipschitz inside every cell of the walk
changes by at most `L` times the sum of the diameters of the cells (the printed "mean value
theorem" over a component in the proof of Theorem 3.6, `rw-spheres.tex:1236-1240`).
-/

namespace SpherePackings

open BouRabeeGwynne BouRabeeGwynne.OrthogonalTiling

open scoped BigOperators Classical

variable {d : ℕ}

/-- Facet adjacency within a set of vertices. -/
def adjGraphIn (T : OrthogonalTiling d) (S : Set T.V) : SimpleGraph T.V where
  Adj a b := a ∈ S ∧ b ∈ S ∧ T.adj a b
  symm := ⟨fun _ _ h => ⟨h.2.1, h.1, T.toTilingData.adj_symm h.2.2⟩⟩
  loopless := ⟨fun a h => T.toTilingData.adj_irrefl a h.2.2⟩

/-- **Chain bound.**  Along a walk of adjacent cells, a function that is `L`-Lipschitz inside every
cell of the walk changes by at most `L` times the sum of the diameters of the cells of the walk. -/
theorem chain_dist_le (T : OrthogonalTiling d) {S : Set T.V} {E : Type*} [PseudoMetricSpace E]
    (φ : Euc d → E) {L : ℝ} (hL : 0 ≤ L) {a b : T.V} (p : (adjGraphIn T S).Walk a b)
    (hφ : ∀ u ∈ p.support, ∀ x ∈ (T.cell u).carrier, ∀ y ∈ (T.cell u).carrier,
      dist (φ x) (φ y) ≤ L * dist x y) :
    ∀ x ∈ (T.cell a).carrier, ∀ y ∈ (T.cell b).carrier,
      dist (φ x) (φ y) ≤ L * (p.support.map fun u => Metric.diam (T.cell u).carrier).sum := by
  induction p with
  | @nil u =>
    intro x hx y hy
    simp only [SimpleGraph.Walk.support_nil, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
    exact (hφ u (by simp) x hx y hy).trans
      (mul_le_mul_of_nonneg_left (Metric.dist_le_diam_of_mem (T.cell u).compact.isBounded hx hy) hL)
  | @cons a c b hadj p ih =>
    intro x hx y hy
    have hne : ((T.cell a).carrier ∩ (T.cell c).carrier).Nonempty := hadj.2.2.2.1
    obtain ⟨z, hzA, hzC⟩ := hne
    have h1 := (hφ a (by simp [SimpleGraph.Walk.support_cons]) x hx z hzA).trans
      (mul_le_mul_of_nonneg_left (Metric.dist_le_diam_of_mem (T.cell a).compact.isBounded hx hzA) hL)
    have h2 := ih (fun u hu => hφ u (by simp [SimpleGraph.Walk.support_cons, hu])) z hzC y hy
    have htri := dist_triangle (φ x) (φ z) (φ y)
    simp only [SimpleGraph.Walk.support_cons, List.map_cons, List.sum_cons, mul_add]
    linarith

end SpherePackings
