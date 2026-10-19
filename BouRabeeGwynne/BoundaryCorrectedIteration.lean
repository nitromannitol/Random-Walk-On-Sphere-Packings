-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/BoundaryCorrectedIteration.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.BoundaryTaylorCorrection
import BouRabeeGwynne.Section3Iteration

/-!
# Harmonic iteration with boundary Taylor corrections

Only newly exposed boundary edges contribute to the additional cost of a
replacement step. The cost of an old boundary edge is not paid repeatedly.
All functions below are the actual finite Dirichlet and Poisson solutions.
-/

open scoped BigOperators Classical

namespace BouRabeeGwynne.FiniteConductanceNetwork

variable {V : Type*} [Fintype V] (N : FiniteConductanceNetwork V)

noncomputable def boundaryCorrectedError (A : Set V) (hA : N.BoundaryAccessible A)
    (g : V → ℝ) (R : V → V → ℝ) : V → ℝ :=
  N.dirichletSolution A hA g - g - N.boundaryCorrection A hA R

theorem boundaryCorrectedError_boundary (A : Set V) (hA : N.BoundaryAccessible A)
    (g : V → ℝ) (R : V → V → ℝ) {v : V} (hv : v ∉ A) :
    N.boundaryCorrectedError A hA g R v = 0 := by
  simp only [boundaryCorrectedError, Pi.sub_apply,
    (N.dirichletSolution_spec A hA g).2 v hv,
    N.boundaryCorrection_boundary A hA R hv, sub_self, sub_zero]

theorem dirichletSolution_abs_le (A : Set V) (hA : N.BoundaryAccessible A)
    (g : V → ℝ) {C : ℝ} (hg : ∀ v, v ∉ A → |g v| ≤ C) (v : V) :
    |N.dirichletSolution A hA g v| ≤ C := by
  have hzero : N.SolvesDirichlet A (fun _ => 0) (fun _ => 0) :=
    ⟨fun x _ => N.laplacian_const 0 x, fun _ _ => rfl⟩
  simpa only [sub_zero] using N.dirichlet_stability A hA
    (N.dirichletSolution_spec A hA g) hzero (fun x hx => by simpa using hg x hx) v

/-- The corrected errors on two nested interiors differ by a harmonic
extension plus the correction of just the newly exposed edges. -/
theorem boundaryCorrectedError_step_identity {A B : Set V} (hBA : B ⊆ A)
    (hA : N.BoundaryAccessible A) (hB : N.BoundaryAccessible B)
    (g : V → ℝ) (R : V → V → ℝ) :
    N.dirichletSolution B hB (N.boundaryCorrectedError A hA g R) =
      N.boundaryCorrectedError A hA g R - N.boundaryCorrectedError B hB g R -
        N.newBoundaryCorrection A B hB R := by
  apply N.dirichlet_unique B hB (N.dirichletSolution_spec B hB _)
  constructor
  · intro v hv
    have hfunc :
        N.boundaryCorrectedError A hA g R - N.boundaryCorrectedError B hB g R -
          N.newBoundaryCorrection A B hB R =
        (N.dirichletSolution A hA g - N.dirichletSolution B hB g) -
          (N.boundaryCorrection A hA R - N.boundaryCorrection B hB R +
            N.newBoundaryCorrection A B hB R) := by
      funext x
      simp only [boundaryCorrectedError, Pi.sub_apply, Pi.add_apply]
      ring
    rw [hfunc, ← N.dirichletSolution_boundaryCorrection hBA hA hB R,
      N.laplacian_sub, N.laplacian_sub,
      (N.dirichletSolution_spec A hA g).1 v (hBA hv),
      (N.dirichletSolution_spec B hB g).1 v hv,
      (N.dirichletSolution_spec B hB (N.boundaryCorrection A hA R)).1 v hv]
    ring
  · intro v hv
    simp only [Pi.sub_apply, N.boundaryCorrectedError_boundary B hB g R hv,
      newBoundaryCorrection, N.boundaryCorrection_boundary B hB _ hv, sub_zero]

theorem boundaryCorrectedError_step_bound {A B : Set V} (hBA : B ⊆ A)
    (hA : N.BoundaryAccessible A) (hB : N.BoundaryAccessible B)
    (g : V → ℝ) (R : V → V → ℝ) {q C : ℝ} (hC : 0 ≤ C)
    (hq : ∀ v, v ∉ B → |N.boundaryCorrectedError A hA g R v| ≤ q)
    (hR : ∀ u ∈ A, ∀ w ∈ A, 0 < N.a u w → |R u w| ≤ C) (v : V) :
    |N.boundaryCorrectedError A hA g R v -
      N.boundaryCorrectedError B hB g R v| ≤ q + C := by
  have heq := congr_fun (N.boundaryCorrectedError_step_identity hBA hA hB g R) v
  simp only [Pi.sub_apply] at heq
  have hid : N.boundaryCorrectedError A hA g R v -
      N.boundaryCorrectedError B hB g R v =
      N.dirichletSolution B hB (N.boundaryCorrectedError A hA g R) v +
        N.newBoundaryCorrection A B hB R v := by linarith
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add
    (N.dirichletSolution_abs_le B hB _ hq v)
    (N.newBoundaryCorrection_abs_le hBA hB R hC hR v))

/-- Apply the already proved trimming rule to the corrected error, so the
harmonic extension cost is the threshold plus cutoff. -/
theorem boundaryCorrectedError_trimmed_step_bound (A : Set V)
    (hA : N.BoundaryAccessible A) (g : V → ℝ) (R : V → V → ℝ)
    {κ δ C : ℝ} (hκ : 0 ≤ κ) (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hR : ∀ u ∈ A, ∀ w ∈ A, 0 < N.a u w → |R u w| ≤ C) (v : V) :
    let f := N.boundaryCorrectedError A hA g R
    let B := N.trimmedErrorSet A f κ δ
    let hB := N.boundaryAccessible_mono (N.trimmedErrorSet_subset A f κ δ) hA
    |f v - N.boundaryCorrectedError B hB g R v| ≤ κ + δ + C := by
  dsimp only
  apply N.boundaryCorrectedError_step_bound
    (N.trimmedErrorSet_subset A _ κ δ) hA _ g R hC
  · intro x hx
    exact N.abs_le_outside_trimmedErrorSet hκ hδ
      (fun y hy => N.boundaryCorrectedError_boundary A hA g R hy) hx
  · exact hR

/-- A finite nested iteration ending in the empty set bounds the original
Dirichlet error by the initial boundary reward and the genuine step costs. -/
theorem boundaryCorrectedIteration_error_bound (S : ℕ → Set V)
    (hS : ∀ i, N.BoundaryAccessible (S i))
    (hnest : ∀ i, S (i + 1) ⊆ S i) (g : V → ℝ) (R : V → V → ℝ)
    (q C : ℕ → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hq : ∀ i v, v ∉ S (i + 1) →
      |N.boundaryCorrectedError (S i) (hS i) g R v| ≤ q i)
    (hR : ∀ i u, u ∈ S i → ∀ w ∈ S i, 0 < N.a u w → |R u w| ≤ C i)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hR₀ : ∀ u ∈ S 0, ∀ w, w ∉ S 0 → 0 < N.a u w → |R u w| ≤ C₀)
    (n : ℕ) (hempty : S n = ∅) (v : V) :
    |N.dirichletSolution (S 0) (hS 0) g v - g v| ≤
      C₀ + ∑ i ∈ Finset.range n, (q i + C i) := by
  let f : ℕ → V → ℝ := fun i => N.boundaryCorrectedError (S i) (hS i) g R
  have hsteps : ∀ i, |f i v - f (i + 1) v| ≤ q i + C i := fun i =>
    N.boundaryCorrectedError_step_bound (hnest i) (hS i) (hS (i + 1))
      g R (hC i) (hq i) (hR i) v
  have hcum : ∀ k, |f 0 v - f k v| ≤ ∑ i ∈ Finset.range k, (q i + C i) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        _ ≤ |f 0 v - f k v| + |f k v - f (k + 1) v| := abs_sub_le _ _ _
        _ ≤ (∑ i ∈ Finset.range k, (q i + C i)) + (q k + C k) :=
          add_le_add ih (hsteps k)
        _ = _ := (Finset.sum_range_succ _ _).symm
  have hfn : f n v = 0 := N.boundaryCorrectedError_boundary (S n) (hS n) g R
    (by simp [hempty])
  have hf := hcum n
  rw [hfn, sub_zero] at hf
  have hinit : N.dirichletSolution (S 0) (hS 0) g v - g v =
      N.boundaryCorrection (S 0) (hS 0) R v + f 0 v := by
    simp only [f, boundaryCorrectedError, Pi.sub_apply]
    ring
  rw [hinit]
  exact (abs_add_le _ _).trans (add_le_add
    (N.boundaryCorrection_abs_le (S 0) (hS 0) R hC₀ hR₀ v) hf)

end BouRabeeGwynne.FiniteConductanceNetwork
