module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/Section3Iteration.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.FiniteDirichlet
public import Mathlib.Algebra.Order.Ring.Abs

@[expose] public section

/-!
# Section 3: a trimmed harmonic-replacement step

The bad set and its trimming are formed from the actual error function and
positive-conductance edges, as in (3.8). The maximum principle then bounds the
cost of replacing the function by its genuine Dirichlet extension on that set.
The volume decay needed for the full iteration is a separate geometric step.
-/

open scoped Classical

namespace BouRabeeGwynne.FiniteConductanceNetwork

variable {V : Type*} [Fintype V] (N : FiniteConductanceNetwork V)

/-- Boundary accessibility is inherited by a smaller interior set in the same network. -/
theorem boundaryAccessible_mono {A B : Set V} (hBA : B ⊆ A)
    (hA : N.BoundaryAccessible A) : N.BoundaryAccessible B := by
  intro v hv
  obtain ⟨w, hw, hpath⟩ := hA v (hBA hv)
  exact ⟨w, fun hwB => hw (hBA hwB), hpath⟩

/-- Vertices of the current interior whose error exceeds the threshold. -/
def errorBadSet (A : Set V) (f : V → ℝ) (κ : ℝ) : Set V :=
  {v | v ∈ A ∧ κ < |f v|}

/-- Remove a bad vertex if an edge to the complement of the bad set has small
error gradient. For a bad vertex, these neighbors are precisely graph-boundary neighbors. -/
def trimmedErrorSet (A : Set V) (f : V → ℝ) (κ δ : ℝ) : Set V :=
  {v | v ∈ errorBadSet A f κ ∧
    ∀ w, 0 < N.a v w → w ∉ errorBadSet A f κ → δ < |f v - f w|}

lemma trimmedErrorSet_subset (A : Set V) (f : V → ℝ) (κ δ : ℝ) :
    N.trimmedErrorSet A f κ δ ⊆ A := fun _ hv => hv.1.1

omit [Fintype V] in
lemma abs_le_of_not_mem_errorBadSet {A : Set V} {f : V → ℝ} {κ : ℝ}
    (hκ : 0 ≤ κ) (hzero : ∀ v, v ∉ A → f v = 0) {v : V}
    (hv : v ∉ errorBadSet A f κ) : |f v| ≤ κ := by
  by_cases hvA : v ∈ A
  · exact le_of_not_gt (fun hlarge => hv ⟨hvA, hlarge⟩)
  · simpa only [hzero v hvA, abs_zero] using hκ

/-- Outside the trimmed set the error is at most threshold plus trimming cutoff. -/
theorem abs_le_outside_trimmedErrorSet {A : Set V} {f : V → ℝ} {κ δ : ℝ}
    (hκ : 0 ≤ κ) (hδ : 0 ≤ δ) (hzero : ∀ v, v ∉ A → f v = 0)
    {v : V} (hv : v ∉ N.trimmedErrorSet A f κ δ) : |f v| ≤ κ + δ := by
  by_cases hbad : v ∈ errorBadSet A f κ
  · have hex := hv
    simp only [trimmedErrorSet, Set.mem_ofPred_eq, hbad, true_and,
      not_forall, not_imp] at hex
    obtain ⟨w, _, hw, hgrad⟩ := hex
    have hwbound := abs_le_of_not_mem_errorBadSet hκ hzero hw
    calc
      |f v| = |(f v - f w) + f w| := by rw [sub_add_cancel]
      _ ≤ |f v - f w| + |f w| := abs_add_le _ _
      _ ≤ δ + κ := add_le_add (le_of_not_gt hgrad) hwbound
      _ = κ + δ := add_comm _ _
  · exact (abs_le_of_not_mem_errorBadSet hκ hzero hbad).trans
      (le_add_of_nonneg_right hδ)

/-- The replacement is the actual finite Dirichlet solver on the trimmed bad set. -/
noncomputable def trimmedHarmonicReplacement (A : Set V) (haccess : N.BoundaryAccessible A)
    (g h : V → ℝ) (κ δ : ℝ) : V → ℝ :=
  N.dirichletSolution (N.trimmedErrorSet A (h - g) κ δ)
    (N.boundaryAccessible_mono (N.trimmedErrorSet_subset A (h - g) κ δ) haccess) g

theorem trimmedHarmonicReplacement_spec (A : Set V) (haccess : N.BoundaryAccessible A)
    (g h : V → ℝ) (κ δ : ℝ) :
    N.SolvesDirichlet (N.trimmedErrorSet A (h - g) κ δ) g
      (N.trimmedHarmonicReplacement A haccess g h κ δ) :=
  N.dirichletSolution_spec _ _ _

/-- The harmonic-replacement cost used in Step 2 of Theorem 3.6, derived from
the trimming rule and the maximum principle rather than assumed as an estimate. -/
theorem trimmedHarmonicReplacement_step_bound (A : Set V)
    (haccess : N.BoundaryAccessible A) (g h : V → ℝ)
    (hh : N.SolvesDirichlet A g h) {κ δ : ℝ} (hκ : 0 ≤ κ) (hδ : 0 ≤ δ) :
    ∀ v, |N.trimmedHarmonicReplacement A haccess g h κ δ v - h v| ≤ κ + δ := by
  let S := N.trimmedErrorSet A (h - g) κ δ
  have hsub : S ⊆ A := N.trimmedErrorSet_subset A (h - g) κ δ
  have hS : N.BoundaryAccessible S := N.boundaryAccessible_mono hsub haccess
  have hold : N.SolvesDirichlet S h h :=
    ⟨fun v hv => hh.1 v (hsub hv), fun _ _ => rfl⟩
  apply N.dirichlet_stability S hS
    (N.trimmedHarmonicReplacement_spec A haccess g h κ δ) hold
  intro v hv
  have hzero : ∀ w, w ∉ A → (h - g) w = 0 := by
    intro w hw
    simp only [Pi.sub_apply, hh.2 w hw, sub_self]
  simpa only [Pi.sub_apply, abs_sub_comm] using
    N.abs_le_outside_trimmedErrorSet hκ hδ hzero hv

end BouRabeeGwynne.FiniteConductanceNetwork
