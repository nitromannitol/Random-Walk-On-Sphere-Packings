-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/Section3HarmonicIteration.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.Section3Iteration

/-!
# Section 3: iteration of genuine harmonic replacements

Every stage contains its actual finite Dirichlet solution and a proved
boundary-accessibility witness. The regions are nested, and the accumulated
change is bounded by the sum of the chosen thresholds and trimming cutoffs.
The geometric decay of the regions is a separate Section 3 obligation.
-/

open scoped BigOperators Classical

namespace BouRabeeGwynne.FiniteConductanceNetwork

variable {V : Type*} [Fintype V] (N : FiniteConductanceNetwork V)

structure HarmonicIterationState (g : V → ℝ) where
  region : Set V
  accessible : N.BoundaryAccessible region
  value : V → ℝ
  solves : N.SolvesDirichlet region g value

namespace HarmonicIterationState

noncomputable def initial (A : Set V) (haccess : N.BoundaryAccessible A)
    (g : V → ℝ) : N.HarmonicIterationState g where
  region := A
  accessible := haccess
  value := N.dirichletSolution A haccess g
  solves := N.dirichletSolution_spec A haccess g

noncomputable def step {g : V → ℝ} (s : N.HarmonicIterationState g)
    (κ δ : ℝ) : N.HarmonicIterationState g where
  region := N.trimmedErrorSet s.region (s.value - g) κ δ
  accessible := N.boundaryAccessible_mono
    (N.trimmedErrorSet_subset s.region (s.value - g) κ δ) s.accessible
  value := N.trimmedHarmonicReplacement s.region s.accessible g s.value κ δ
  solves := N.trimmedHarmonicReplacement_spec s.region s.accessible g s.value κ δ

lemma step_region_subset {g : V → ℝ} (s : N.HarmonicIterationState g) (κ δ : ℝ) :
    (s.step N κ δ).region ⊆ s.region :=
  N.trimmedErrorSet_subset s.region (s.value - g) κ δ

lemma step_value_bound {g : V → ℝ} (s : N.HarmonicIterationState g)
    {κ δ : ℝ} (hκ : 0 ≤ κ) (hδ : 0 ≤ δ) :
    ∀ v, |(s.step N κ δ).value v - s.value v| ≤ κ + δ :=
  N.trimmedHarmonicReplacement_step_bound s.region s.accessible g s.value s.solves hκ hδ

end HarmonicIterationState

noncomputable def harmonicIteration (A : Set V) (haccess : N.BoundaryAccessible A)
    (g : V → ℝ) (κ δ : ℕ → ℝ) : ℕ → N.HarmonicIterationState g :=
  fun n => Nat.rec (HarmonicIterationState.initial N A haccess g)
    (fun j s => HarmonicIterationState.step N s (κ j) (δ j)) n

lemma harmonicIteration_region_antitone (A : Set V) (haccess : N.BoundaryAccessible A)
    (g : V → ℝ) (κ δ : ℕ → ℝ) :
    Antitone (fun n => (N.harmonicIteration A haccess g κ δ n).region) := by
  apply antitone_nat_of_succ_le
  intro n
  exact HarmonicIterationState.step_region_subset N _ _ _

theorem harmonicIteration_cumulative_cost (A : Set V)
    (haccess : N.BoundaryAccessible A) (g : V → ℝ) (κ δ : ℕ → ℝ)
    (hκ : ∀ n, 0 ≤ κ n) (hδ : ∀ n, 0 ≤ δ n) (n : ℕ) :
    ∀ v, |(N.harmonicIteration A haccess g κ δ n).value v -
      N.dirichletSolution A haccess g v| ≤ ∑ j ∈ Finset.range n, (κ j + δ j) := by
  induction n with
  | zero =>
    intro v
    simp [harmonicIteration, HarmonicIterationState.initial]
  | succ n ih =>
    intro v
    have hstep := HarmonicIterationState.step_value_bound N
      (N.harmonicIteration A haccess g κ δ n) (hκ n) (hδ n) v
    calc
      _ ≤ |(N.harmonicIteration A haccess g κ δ (n + 1)).value v -
          (N.harmonicIteration A haccess g κ δ n).value v| +
          |(N.harmonicIteration A haccess g κ δ n).value v -
            N.dirichletSolution A haccess g v| := abs_sub_le _ _ _
      _ ≤ (κ n + δ n) + ∑ j ∈ Finset.range n, (κ j + δ j) :=
        add_le_add hstep (ih v)
      _ = _ := by rw [Finset.sum_range_succ]; ring

theorem harmonicIteration_error_outside (A : Set V)
    (haccess : N.BoundaryAccessible A) (g : V → ℝ) (κ δ : ℕ → ℝ)
    (hκ : ∀ n, 0 ≤ κ n) (hδ : ∀ n, 0 ≤ δ n) (n : ℕ) {v : V}
    (hv : v ∉ (N.harmonicIteration A haccess g κ δ n).region) :
    |N.dirichletSolution A haccess g v - g v| ≤
      ∑ j ∈ Finset.range n, (κ j + δ j) := by
  have heq := (N.harmonicIteration A haccess g κ δ n).solves.2 v hv
  simpa only [heq, abs_sub_comm] using
    N.harmonicIteration_cumulative_cost A haccess g κ δ hκ hδ n v

theorem harmonicIteration_error_outside_of_solves (A : Set V)
    (haccess : N.BoundaryAccessible A) (g h : V → ℝ)
    (hh : N.SolvesDirichlet A g h) (κ δ : ℕ → ℝ)
    (hκ : ∀ n, 0 ≤ κ n) (hδ : ∀ n, 0 ≤ δ n) (n : ℕ) {v : V}
    (hv : v ∉ (N.harmonicIteration A haccess g κ δ n).region) :
    |h v - g v| ≤ ∑ j ∈ Finset.range n, (κ j + δ j) := by
  have heq := N.dirichlet_unique A haccess hh (N.dirichletSolution_spec A haccess g)
  rw [heq]
  exact N.harmonicIteration_error_outside A haccess g κ δ hκ hδ n hv

end BouRabeeGwynne.FiniteConductanceNetwork
