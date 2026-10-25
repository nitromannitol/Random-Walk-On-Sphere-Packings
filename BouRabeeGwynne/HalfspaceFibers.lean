module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/HalfspaceFibers.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.HalfspaceBoundary
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace BouRabeeGwynne.ConvexPolytope

variable {d : ℕ} (P : ConvexPolytope d)

/-- Compactness forces a supporting constraint in every nonzero direction. -/
theorem exists_halfspace_inner_pos {e : Euc d} (he : e ≠ 0) :
    ∃ p ∈ P.halfspaces, 0 < inner ℝ p.1 e := by
  obtain ⟨x, hx, hmax⟩ := P.compact.exists_isMaxOn
    (P.interior_nonempty.mono interior_subset)
    (continuous_const.inner continuous_id).continuousOn (f := fun x => inner ℝ e x)
  by_contra hno
  have hy : x + e ∈ P.carrier := by
    apply P.mem_carrier_iff.mpr
    intro p hp
    have hpe : inner ℝ p.1 e ≤ 0 := le_of_not_gt (fun h => hno ⟨p, hp, h⟩)
    have hpx := P.mem_carrier_iff.mp hx p hp
    rw [inner_add_right]
    linarith
  have hle := hmax hy
  change inner ℝ e (x + e) ≤ inner ℝ e x at hle
  have hpos := real_inner_self_pos.mpr he
  simp only [inner_add_right] at hle
  linarith

theorem exists_halfspace_inner_neg {e : Euc d} (he : e ≠ 0) :
    ∃ p ∈ P.halfspaces, inner ℝ p.1 e < 0 := by
  obtain ⟨p, hp, hpe⟩ := P.exists_halfspace_inner_pos (neg_ne_zero.mpr he)
  exact ⟨p, hp, by simpa only [inner_neg_right, neg_pos] using hpe⟩

noncomputable section

open scoped Classical

/-- Constraints bounding a line parameter from above. -/
def upperConstraints (e : Euc d) : Finset (Euc d × ℝ) :=
  P.halfspaces.filter (fun p => 0 < inner ℝ p.1 e)

/-- Constraints bounding a line parameter from below. -/
def lowerConstraints (e : Euc d) : Finset (Euc d × ℝ) :=
  P.halfspaces.filter (fun p => inner ℝ p.1 e < 0)

lemma upperConstraints_nonempty {e : Euc d} (he : e ≠ 0) :
    (P.upperConstraints e).Nonempty := by
  obtain ⟨p, hp, hpe⟩ := P.exists_halfspace_inner_pos he
  exact ⟨p, Finset.mem_filter.mpr ⟨hp, hpe⟩⟩

lemma lowerConstraints_nonempty {e : Euc d} (he : e ≠ 0) :
    (P.lowerConstraints e).Nonempty := by
  obtain ⟨p, hp, hpe⟩ := P.exists_halfspace_inner_neg he
  exact ⟨p, Finset.mem_filter.mpr ⟨hp, hpe⟩⟩

/-- The parameter where the line through `y` in direction `e` meets a plane. -/
def planeParameter (e y : Euc d) (p : Euc d × ℝ) : ℝ :=
  (p.2 - inner ℝ p.1 y) / inner ℝ p.1 e

def upperFiber (e : Euc d) (he : e ≠ 0) (y : Euc d) : ℝ :=
  (P.upperConstraints e).inf' (P.upperConstraints_nonempty he) (planeParameter e y)

def lowerFiber (e : Euc d) (he : e ≠ 0) (y : Euc d) : ℝ :=
  (P.lowerConstraints e).sup' (P.lowerConstraints_nonempty he) (planeParameter e y)

/-- Constraints parallel to the line restrict its base point, not its parameter. -/
def parallelConstraintsHold (e y : Euc d) : Prop :=
  ∀ p ∈ P.halfspaces, inner ℝ p.1 e = 0 → inner ℝ p.1 y ≤ p.2

lemma le_upperFiber_iff {e : Euc d} (he : e ≠ 0) (y : Euc d) (t : ℝ) :
    t ≤ P.upperFiber e he y ↔
      ∀ p ∈ P.halfspaces, 0 < inner ℝ p.1 e → t ≤ planeParameter e y p := by
  simp only [upperFiber, Finset.le_inf'_iff, upperConstraints, Finset.mem_filter,
    and_imp]

lemma lowerFiber_le_iff {e : Euc d} (he : e ≠ 0) (y : Euc d) (t : ℝ) :
    P.lowerFiber e he y ≤ t ↔
      ∀ p ∈ P.halfspaces, inner ℝ p.1 e < 0 → planeParameter e y p ≤ t := by
  simp only [lowerFiber, Finset.sup'_le_iff, lowerConstraints, Finset.mem_filter,
    and_imp]

/-- Exact line fibers of the supplied finite-halfspace polytope. This includes
parallel constraints and allows empty fibers when the lower bound exceeds the upper. -/
theorem mem_line_iff {e : Euc d} (he : e ≠ 0) (y : Euc d) (t : ℝ) :
    y + t • e ∈ P.carrier ↔
      P.parallelConstraintsHold e y ∧
      P.lowerFiber e he y ≤ t ∧ t ≤ P.upperFiber e he y := by
  rw [P.mem_carrier_iff, P.lowerFiber_le_iff, P.le_upperFiber_iff]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro p hp hz
      simpa only [inner_add_right, inner_smul_right, hz, mul_zero, add_zero] using h p hp
    · intro p hp hn
      apply (div_le_iff_of_neg hn).mpr
      have hh := h p hp
      simp only [inner_add_right, inner_smul_right] at hh
      linarith
    · intro p hp hn
      apply (le_div_iff₀ hn).mpr
      have hh := h p hp
      simp only [inner_add_right, inner_smul_right] at hh
      linarith
  · rintro ⟨hz, hlo, hup⟩ p hp
    rw [inner_add_right, inner_smul_right]
    rcases lt_trichotomy (inner ℝ p.1 e) 0 with hn | heq | hn
    · have hh := (div_le_iff_of_neg hn).mp (hlo p hp hn)
      linarith
    · simpa only [heq, mul_zero, add_zero] using hz p hp heq
    · have hh := (le_div_iff₀ hn).mp (hup p hp hn)
      linarith

theorem line_preimage_eq_Icc {e : Euc d} (he : e ≠ 0) (y : Euc d)
    (hy : P.parallelConstraintsHold e y) :
    (fun t : ℝ => y + t • e) ⁻¹' P.carrier =
      Set.Icc (P.lowerFiber e he y) (P.upperFiber e he y) := by
  ext t
  simpa only [Set.mem_preimage, Set.mem_Icc, hy, true_and] using P.mem_line_iff he y t

theorem line_preimage_eq_empty {e : Euc d} (he : e ≠ 0) (y : Euc d)
    (hy : ¬ P.parallelConstraintsHold e y) :
    (fun t : ℝ => y + t • e) ⁻¹' P.carrier = ∅ := by
  ext t
  simp only [Set.mem_preimage, P.mem_line_iff he, hy, false_and, Set.mem_empty_iff_false]

end

end BouRabeeGwynne.ConvexPolytope
