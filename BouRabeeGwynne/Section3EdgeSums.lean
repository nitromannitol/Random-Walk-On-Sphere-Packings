-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/Section3EdgeSums.lean` at commit cf73d6e); unchanged apart from this header.
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Section 3: exact weighted handshaking

The unordered-edge energy equals one half of the ordered adjacent-pair sum.
-/

open scoped Classical BigOperators

namespace BouRabeeGwynne

variable {V : Type*} [Fintype V]

/-- An arbitrary edge weight is counted twice by the ordered adjacent-pair sum. -/
theorem sum_adjacent_pairs_eq_twice_edge_sum (G : SimpleGraph V) (F : Sym2 V → ℝ) :
    (∑ v, ∑ w, if G.Adj v w then F s(v, w) else 0) =
      2 * ∑ a ∈ G.edgeFinset, F a := by
  classical
  have hpairs : (∑ v, ∑ w, if G.Adj v w then F s(v, w) else 0) =
      ∑ p ∈ (Finset.univ : Finset (V × V)).filter (fun p => G.Adj p.1 p.2),
        F s(p.1, p.2) := by
    rw [Finset.sum_filter]
    exact (Fintype.sum_prod_type (fun p : V × V =>
      if G.Adj p.1 p.2 then F s(p.1, p.2) else (0 : ℝ))).symm
  have hdarts : (∑ p ∈ (Finset.univ : Finset (V × V)).filter
      (fun p => G.Adj p.1 p.2), F s(p.1, p.2)) =
        ∑ q : G.Dart, F q.edge := by
    exact Finset.sum_bij'
      (s := (Finset.univ : Finset (V × V)).filter (fun p => G.Adj p.1 p.2))
      (t := (Finset.univ : Finset G.Dart))
      (f := fun p => F s(p.1, p.2)) (g := fun q : G.Dart => F q.edge)
      (fun p hp => (⟨p, (Finset.mem_filter.mp hp).2⟩ : G.Dart))
      (fun q _ => q.toProd)
      (fun _ _ => Finset.mem_univ _)
      (fun q _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, q.adj⟩)
      (fun _ _ => rfl)
      (fun q _ => SimpleGraph.Dart.ext _ q rfl)
      (fun _ _ => rfl)
  have hmap : ∀ q ∈ (Finset.univ : Finset G.Dart), q.edge ∈ G.edgeFinset := by
    intro q _
    exact SimpleGraph.mem_edgeFinset.mpr q.edge_mem
  rw [hpairs, hdarts, ← Finset.sum_fiberwise_of_maps_to' hmap F, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_const, G.dart_edge_fiber_card a (SimpleGraph.mem_edgeFinset.mp ha)]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]

/-- The once-per-edge sum equals one half of the ordered adjacent-pair sum. -/
theorem edge_sum_eq_half_sum_adjacent_pairs (G : SimpleGraph V) (F : Sym2 V → ℝ) :
    (∑ a ∈ G.edgeFinset, F a) =
      (1 / 2 : ℝ) * ∑ v, ∑ w, if G.Adj v w then F s(v, w) else 0 := by
  rw [sum_adjacent_pairs_eq_twice_edge_sum]
  ring

end BouRabeeGwynne
