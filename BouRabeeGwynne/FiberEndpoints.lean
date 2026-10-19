-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/FiberEndpoints.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.HalfspaceFibers
import Mathlib.Topology.Order.Lattice

namespace BouRabeeGwynne.ConvexPolytope

variable {d : ℕ} (P : ConvexPolytope d)

lemma continuous_planeParameter (e : Euc d) (p : Euc d × ℝ) :
    Continuous (fun y => planeParameter e y p) := by
  unfold planeParameter
  exact (continuous_const.sub (continuous_const.inner continuous_id)).div_const _

lemma continuous_lowerFiber {e : Euc d} (he : e ≠ 0) :
    Continuous (P.lowerFiber e he) := by
  apply Continuous.finset_sup'_apply (P.lowerConstraints_nonempty he)
  intro p _
  exact continuous_planeParameter e p

lemma continuous_upperFiber {e : Euc d} (he : e ≠ 0) :
    Continuous (P.upperFiber e he) := by
  apply Continuous.finset_sup'_apply (L := OrderDual ℝ) (P.upperConstraints_nonempty he)
  intro p _
  exact continuous_planeParameter e p

/-- A finite upper envelope always attains one of its actual plane bounds. -/
theorem exists_upperFiber_active {e : Euc d} (he : e ≠ 0) (y : Euc d) :
    ∃ p ∈ P.halfspaces, 0 < inner ℝ p.1 e ∧
      inner ℝ p.1 (y + P.upperFiber e he y • e) = p.2 := by
  classical
  obtain ⟨p, hp, heq⟩ := Finset.exists_mem_eq_inf'
    (P.upperConstraints_nonempty he) (planeParameter e y)
  have hp' := Finset.mem_filter.mp hp
  refine ⟨p, hp'.1, hp'.2, ?_⟩
  change P.upperFiber e he y = (p.2 - inner ℝ p.1 y) / inner ℝ p.1 e at heq
  have hmul := (eq_div_iff hp'.2.ne').mp heq
  rw [inner_add_right, inner_smul_right]
  linarith

theorem exists_lowerFiber_active {e : Euc d} (he : e ≠ 0) (y : Euc d) :
    ∃ p ∈ P.halfspaces, inner ℝ p.1 e < 0 ∧
      inner ℝ p.1 (y + P.lowerFiber e he y • e) = p.2 := by
  classical
  obtain ⟨p, hp, heq⟩ := Finset.exists_mem_eq_sup'
    (P.lowerConstraints_nonempty he) (planeParameter e y)
  have hp' := Finset.mem_filter.mp hp
  refine ⟨p, hp'.1, hp'.2, ?_⟩
  change P.lowerFiber e he y = (p.2 - inner ℝ p.1 y) / inner ℝ p.1 e at heq
  have hmul := (eq_div_iff hp'.2.ne).mp heq
  rw [inner_add_right, inner_smul_right]
  linarith

theorem upperFiber_mem_frontier {e : Euc d} (he : e ≠ 0) (y : Euc d)
    (hy : P.parallelConstraintsHold e y)
    (hlu : P.lowerFiber e he y ≤ P.upperFiber e he y) :
    y + P.upperFiber e he y • e ∈ frontier P.carrier := by
  obtain ⟨p, hp, hn, hactive⟩ := P.exists_upperFiber_active he y
  apply P.mem_frontier_iff.mpr
  refine ⟨(P.mem_line_iff he y _).mpr ⟨hy, hlu, le_rfl⟩, p, hp, ?_, hactive⟩
  intro hpzero
  simpa only [hpzero, inner_zero_left, lt_self_iff_false] using hn

theorem lowerFiber_mem_frontier {e : Euc d} (he : e ≠ 0) (y : Euc d)
    (hy : P.parallelConstraintsHold e y)
    (hlu : P.lowerFiber e he y ≤ P.upperFiber e he y) :
    y + P.lowerFiber e he y • e ∈ frontier P.carrier := by
  obtain ⟨p, hp, hn, hactive⟩ := P.exists_lowerFiber_active he y
  apply P.mem_frontier_iff.mpr
  refine ⟨(P.mem_line_iff he y _).mpr ⟨hy, le_rfl, hlu⟩, p, hp, ?_, hactive⟩
  intro hpzero
  simpa only [hpzero, inner_zero_left, lt_self_iff_false] using hn

/-- The geometric upper boundary map used in coordinate slicing. -/
noncomputable def upperEndpoint (e : Euc d) (he : e ≠ 0) (y : Euc d) : Euc d :=
  y + P.upperFiber e he y • e

noncomputable def lowerEndpoint (e : Euc d) (he : e ≠ 0) (y : Euc d) : Euc d :=
  y + P.lowerFiber e he y • e

lemma continuous_upperEndpoint {e : Euc d} (he : e ≠ 0) :
    Continuous (P.upperEndpoint e he) :=
  continuous_id.add ((P.continuous_upperFiber he).smul continuous_const)

lemma continuous_lowerEndpoint {e : Euc d} (he : e ≠ 0) :
    Continuous (P.lowerEndpoint e he) :=
  continuous_id.add ((P.continuous_lowerFiber he).smul continuous_const)

end BouRabeeGwynne.ConvexPolytope
