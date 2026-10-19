-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/Section3LocalMaximum.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.FiniteDirichlet

/-!
# Section 3: a maximum principle with the actual local graph boundary

Clamping unrelated exterior values reduces the local statement to the checked
finite-network maximum principle. Boundary approximation and the oscillation
of a comparison function then bound the harmonic error at an interior vertex.
-/

open scoped Classical BigOperators

namespace BouRabeeGwynne.FiniteConductanceNetwork

variable {V : Type*} [Fintype V] (N : FiniteConductanceNetwork V)

/-- Actual external graph boundary inside the fixed finite network. -/
def externalBoundary (A : Set V) : Set V :=
  {w | w ∉ A ∧ ∃ v ∈ A, 0 < N.a v w}

/-- Only exterior vertices adjacent to A need boundary control. Unrelated
vertices of the ambient network can have arbitrary values. -/
theorem local_maximum_principle (A : Set V) (haccess : N.BoundaryAccessible A)
    (h : V → ℝ) (M : ℝ) (hsub : ∀ v ∈ A, 0 ≤ N.laplacian h v)
    (hboundary : ∀ w ∈ N.externalBoundary A, h w ≤ M) :
    ∀ v ∈ A, h v ≤ M := by
  let f : V → ℝ := fun v => if v ∈ A then h v else min (h v) M
  have hL : ∀ v ∈ A, N.laplacian f v = N.laplacian h v := by
    intro v hv
    unfold laplacian
    apply Finset.sum_congr rfl
    intro w _
    by_cases hw : w ∈ A
    · simp only [f, hv, hw, ite_true]
    · by_cases ha : 0 < N.a v w
      · have hb := hboundary w ⟨hw, v, hv, ha⟩
        simp only [f, hv, hw, ite_true, ite_false, min_eq_left hb]
      · have ha0 : N.a v w = 0 := le_antisymm (le_of_not_gt ha) (N.nonneg v w)
        simp only [ha0, zero_mul]
  have hbound := N.maximum_principle A haccess f M
    (fun v hv => by rw [hL v hv]; exact hsub v hv)
    (fun w hw => by simp only [f, hw, ite_false]; exact min_le_right _ _)
  intro v hv
  simpa only [f, hv, ite_true] using hbound v

/-- Boundary approximation plus the oscillation of the comparison function
controls the harmonic error at an interior vertex. -/
theorem harmonic_error_le_boundary_error_add_oscillation
    (A : Set V) (haccess : N.BoundaryAccessible A) (h g : V → ℝ)
    (hh : ∀ v ∈ A, N.laplacian h v = 0) {η ω : ℝ}
    (hboundary : ∀ w ∈ N.externalBoundary A, |h w - g w| ≤ η)
    {v : V} (hv : v ∈ A)
    (hosc : ∀ w ∈ N.externalBoundary A, |g w - g v| ≤ ω) :
    |h v - g v| ≤ η + ω := by
  have hup : h v ≤ g v + (η + ω) := N.local_maximum_principle A haccess h _
    (fun w hw => le_of_eq (hh w hw).symm)
    (fun w hw => by
      have h₁ := (abs_le.mp (hboundary w hw)).2
      have h₂ := (abs_le.mp (hosc w hw)).2
      linarith) v hv
  have hlo : (-h) v ≤ -g v + (η + ω) := N.local_maximum_principle A haccess (-h) _
    (fun w hw => by simp only [N.laplacian_neg, hh w hw, neg_zero, le_refl])
    (fun w hw => by
      have h₁ := (abs_le.mp (hboundary w hw)).1
      have h₂ := (abs_le.mp (hosc w hw)).1
      change -h w ≤ -g v + (η + ω)
      linarith) v hv
  apply abs_le.mpr
  change -h v ≤ -g v + (η + ω) at hlo
  constructor <;> linarith

end BouRabeeGwynne.FiniteConductanceNetwork
