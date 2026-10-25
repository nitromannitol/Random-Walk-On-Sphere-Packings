module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/BoundaryEdgeResponse.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.FiniteDirichlet

@[expose] public section

/-!
# Boundary-edge Poisson responses

These are solutions of explicit finite linear systems. Their positivity,
normalization, and compatibility under nested Dirichlet extensions are proved
from the finite maximum principle. No identification with a stochastic exit law
is required for the boundary correction in the hypothesis III argument.
-/

open scoped BigOperators Classical

namespace BouRabeeGwynne.FiniteConductanceNetwork

variable {V : Type*} [Fintype V] (N : FiniteConductanceNetwork V)

/-- The inverse of the already proved invertible finite Dirichlet operator. -/
noncomputable def dirichletInverse (A : Set V) (hA : N.BoundaryAccessible A) :
    (V → ℝ) ≃ₗ[ℝ] (V → ℝ) :=
  (LinearEquiv.ofBijective (N.dirichletOperator A)
    ⟨N.dirichletOperator_injective A hA,
      LinearMap.injective_iff_surjective.mp (N.dirichletOperator_injective A hA)⟩).symm

@[simp] theorem dirichletOperator_inverse (A : Set V) (hA : N.BoundaryAccessible A)
    (r : V → ℝ) : N.dirichletOperator A (N.dirichletInverse A hA r) = r :=
  (LinearEquiv.ofBijective (N.dirichletOperator A)
    ⟨N.dirichletOperator_injective A hA,
      LinearMap.injective_iff_surjective.mp (N.dirichletOperator_injective A hA)⟩).apply_symm_apply r

/-- Zero-boundary solution with the specified interior Laplacian. -/
noncomputable def poissonSolution (A : Set V) (hA : N.BoundaryAccessible A)
    (r : V → ℝ) : V → ℝ :=
  N.dirichletInverse A hA (fun v => if v ∈ A then r v else 0)

theorem poissonSolution_laplacian (A : Set V) (hA : N.BoundaryAccessible A)
    (r : V → ℝ) {v : V} (hv : v ∈ A) :
    N.laplacian (N.poissonSolution A hA r) v = r v := by
  have h := congr_fun (N.dirichletOperator_inverse A hA
    (fun v => if v ∈ A then r v else 0)) v
  simpa only [dirichletOperator_apply, hv, ite_true, poissonSolution] using h

theorem poissonSolution_boundary (A : Set V) (hA : N.BoundaryAccessible A)
    (r : V → ℝ) {v : V} (hv : v ∉ A) : N.poissonSolution A hA r v = 0 := by
  have h := congr_fun (N.dirichletOperator_inverse A hA
    (fun v => if v ∈ A then r v else 0)) v
  simpa only [dirichletOperator_apply, hv, ite_false, poissonSolution] using h

theorem poissonSolution_unique (A : Set V) (hA : N.BoundaryAccessible A)
    (r f : V → ℝ) (hL : ∀ v ∈ A, N.laplacian f v = r v)
    (hb : ∀ v, v ∉ A → f v = 0) : f = N.poissonSolution A hA r := by
  apply N.dirichletOperator_injective A hA
  funext v
  by_cases hv : v ∈ A
  · simp only [dirichletOperator_apply, hv, ite_true, hL v hv,
      N.poissonSolution_laplacian A hA r hv]
  · simp only [dirichletOperator_apply, hv, ite_false, hb v hv,
      N.poissonSolution_boundary A hA r hv]

/-- The source attached to a directed edge leaving the interior. -/
noncomputable def boundaryEdgeSource (A : Set V) (u w v : V) : ℝ :=
  if v = u ∧ u ∈ A ∧ w ∉ A then -N.a u w else 0

/-- The genuine zero-boundary Poisson response of a directed boundary edge. -/
noncomputable def boundaryEdgeResponse (A : Set V) (hA : N.BoundaryAccessible A)
    (u w : V) : V → ℝ := N.poissonSolution A hA (N.boundaryEdgeSource A u w)

theorem boundaryEdgeResponse_laplacian (A : Set V) (hA : N.BoundaryAccessible A)
    (u w : V) {v : V} (hv : v ∈ A) :
    N.laplacian (N.boundaryEdgeResponse A hA u w) v = N.boundaryEdgeSource A u w v :=
  N.poissonSolution_laplacian A hA _ hv

theorem boundaryEdgeResponse_boundary (A : Set V) (hA : N.BoundaryAccessible A)
    (u w : V) {v : V} (hv : v ∉ A) : N.boundaryEdgeResponse A hA u w v = 0 :=
  N.poissonSolution_boundary A hA _ hv

theorem boundaryEdgeResponse_nonneg (A : Set V) (hA : N.BoundaryAccessible A)
    (u w v : V) : 0 ≤ N.boundaryEdgeResponse A hA u w v := by
  have h := N.maximum_principle A hA (-N.boundaryEdgeResponse A hA u w) 0
    (fun x hx => by
      rw [N.laplacian_neg, N.boundaryEdgeResponse_laplacian A hA u w hx]
      unfold boundaryEdgeSource
      split_ifs
      · simpa using N.nonneg u w
      · simp)
    (fun x hx => by simp [N.boundaryEdgeResponse_boundary A hA u w hx]) v
  exact neg_nonpos.mp h

theorem boundaryEdgeResponse_eq_zero (A : Set V) (hA : N.BoundaryAccessible A)
    (u w : V) (h : ¬ (u ∈ A ∧ w ∉ A)) : N.boundaryEdgeResponse A hA u w = 0 := by
  apply N.homogeneous_solution_eq_zero A hA
  · intro v hv
    rw [N.boundaryEdgeResponse_laplacian A hA u w hv]
    simp only [boundaryEdgeSource]
    exact if_neg (fun hc => h hc.2)
  · intro v hv
    exact N.boundaryEdgeResponse_boundary A hA u w hv

theorem boundaryEdgeResponse_eq_zero_of_conductance (A : Set V)
    (hA : N.BoundaryAccessible A) (u w : V) (ha : N.a u w = 0) :
    N.boundaryEdgeResponse A hA u w = 0 := by
  apply N.homogeneous_solution_eq_zero A hA
  · intro v hv
    rw [N.boundaryEdgeResponse_laplacian A hA u w hv]
    simp [boundaryEdgeSource, ha]
  · intro v hv
    exact N.boundaryEdgeResponse_boundary A hA u w hv

theorem laplacian_finset_sum {I : Type*} (s : Finset I) (f : I → V → ℝ) (v : V) :
    N.laplacian (fun x => ∑ i ∈ s, f i x) v = ∑ i ∈ s, N.laplacian (f i) v := by
  classical
  simp only [laplacian, ← Finset.sum_sub_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The responses of all boundary edges sum to one in the interior and zero
outside. This is a theorem about the concrete Poisson system. -/
theorem sum_boundaryEdgeResponse (A : Set V) (hA : N.BoundaryAccessible A) (v : V) :
    (∑ u, ∑ w, N.boundaryEdgeResponse A hA u w v) = if v ∈ A then 1 else 0 := by
  let k : V → ℝ := fun x => ∑ u, ∑ w, N.boundaryEdgeResponse A hA u w x
  let j : V → ℝ := fun x => if x ∈ A then 1 else 0
  have heq : k = j := by
    apply N.dirichletOperator_injective A hA
    funext x
    by_cases hx : x ∈ A
    · simp only [dirichletOperator_apply, hx, ite_true]
      change N.laplacian (fun y => ∑ u, ∑ w, N.boundaryEdgeResponse A hA u w y) x = _
      rw [N.laplacian_finset_sum]
      simp only [N.laplacian_finset_sum, N.boundaryEdgeResponse_laplacian A hA _ _ hx]
      have hsum : (∑ u, ∑ w, N.boundaryEdgeSource A u w x) =
          ∑ w, if w ∉ A then -N.a x w else 0 := by
        rw [Finset.sum_eq_single x]
        · simp [boundaryEdgeSource, hx]
        · intro u _ hux
          simp [boundaryEdgeSource, Ne.symm hux]
        · simp
      rw [hsum]
      unfold laplacian
      apply Finset.sum_congr rfl
      intro w _
      by_cases hw : w ∈ A <;> simp [j, hx, hw]
    · simp only [dirichletOperator_apply, hx, ite_false]
      simp [k, j, hx, N.boundaryEdgeResponse_boundary A hA _ _ hx]
  exact congr_fun heq v

theorem boundaryEdgeResponse_le_one (A : Set V) (hA : N.BoundaryAccessible A)
    (u w v : V) : N.boundaryEdgeResponse A hA u w v ≤ 1 := by
  have h₁ : N.boundaryEdgeResponse A hA u w v ≤
      ∑ z, N.boundaryEdgeResponse A hA u z v :=
    Finset.single_le_sum (fun z _ => N.boundaryEdgeResponse_nonneg A hA u z v)
      (Finset.mem_univ w)
  have h₂ : (∑ z, N.boundaryEdgeResponse A hA u z v) ≤
      ∑ y, ∑ z, N.boundaryEdgeResponse A hA y z v :=
    Finset.single_le_sum (fun y _ => Finset.sum_nonneg
      (fun z _ => N.boundaryEdgeResponse_nonneg A hA y z v)) (Finset.mem_univ u)
  have h := h₁.trans h₂
  rw [N.sum_boundaryEdgeResponse A hA v] at h
  split_ifs at h <;> linarith

/-- On nested interiors, harmonic extension of an outer boundary-edge
response is exactly the difference of the two concrete Poisson responses. -/
theorem dirichletSolution_boundaryEdgeResponse {A B : Set V} (hBA : B ⊆ A)
    (hA : N.BoundaryAccessible A) (hB : N.BoundaryAccessible B)
    (u w : V) (hu : u ∈ A) (hw : w ∉ A) :
    N.dirichletSolution B hB (N.boundaryEdgeResponse A hA u w) =
      N.boundaryEdgeResponse A hA u w - N.boundaryEdgeResponse B hB u w := by
  apply N.dirichlet_unique B hB (N.dirichletSolution_spec B hB _)
  constructor
  · intro v hv
    rw [N.laplacian_sub, N.boundaryEdgeResponse_laplacian A hA u w (hBA hv),
      N.boundaryEdgeResponse_laplacian B hB u w hv]
    have hwB : w ∉ B := fun hwB => hw (hBA hwB)
    by_cases hvu : v = u
    · have huB : u ∈ B := hvu ▸ hv
      simp [boundaryEdgeSource, hvu, hu, huB, hw, hwB]
    · simp [boundaryEdgeSource, hvu]
  · intro v hv
    simp only [Pi.sub_apply, N.boundaryEdgeResponse_boundary B hB u w hv, sub_zero]

end BouRabeeGwynne.FiniteConductanceNetwork
