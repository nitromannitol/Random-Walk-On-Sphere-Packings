-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/DualDirichlet.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.DiscretePDEAlgebra

open scoped BigOperators Classical

namespace BouRabeeGwynne.FiniteConductanceNetwork

variable {V : Type*} [Fintype V] (N : FiniteConductanceNetwork V)

/-- The paper's oriented-edge dual energy. Off-edge terms vanish; admissible
fields are separately required to vanish on zero-conductance pairs. -/
noncomputable def dualEnergy (θ : V → V → ℝ) : ℝ :=
  ∑ v, ∑ w, (θ w v) ^ 2 / N.a w v

/-- Lemma 2.3 on a finite conductance network. The divergence and support
conditions refer to the actual edge field, not to an assumed energy estimate. -/
theorem dual_variational_principle (A : Set V) (f : V → ℝ) (θ : V → V → ℝ)
    (hθ : IsDiscreteVectorField θ)
    (hsupport : ∀ w v, N.a w v = 0 → θ w v = 0)
    (hboundary : ∀ v, v ∉ A → f v = 0)
    (hdiv : ∀ v ∈ A, discreteDiv θ v = discreteDiv (N.weightedGradient f) v) :
    N.dualEnergy (N.weightedGradient f) ≤ N.dualEnergy θ := by
  let ψ : V → V → ℝ := fun w v => θ w v - N.weightedGradient f w v
  have hψ : IsDiscreteVectorField ψ := by
    intro w v
    dsimp [ψ]
    rw [hθ w v, N.weightedGradient_antisymm f w v]
    ring
  have hψdiv : ∀ v, f v ≠ 0 → discreteDiv ψ v = 0 := by
    intro v hv
    have hvA : v ∈ A := by
      by_contra hnot
      exact hv (hboundary v hnot)
    change (∑ w, (θ w v - N.weightedGradient f w v)) = 0
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (hdiv v hvA)
  have horth := discrete_integration_by_parts_zero ψ f hψ hψdiv
  have hnonneg : 0 ≤ N.dualEnergy ψ := by
    apply Finset.sum_nonneg
    intro v _
    apply Finset.sum_nonneg
    intro w _
    exact div_nonneg (sq_nonneg _) (N.nonneg w v)
  have hterm (w v : V) :
      (θ w v) ^ 2 / N.a w v =
        (N.weightedGradient f w v) ^ 2 / N.a w v +
          2 * (ψ w v * discreteGrad f w v) + (ψ w v) ^ 2 / N.a w v := by
    by_cases ha : N.a w v = 0
    · simp [ψ, weightedGradient, ha, hsupport w v ha]
    · dsimp [ψ, weightedGradient]
      field_simp [ha]
      ring
  have hdecomp : N.dualEnergy θ = N.dualEnergy (N.weightedGradient f) +
      2 * (∑ v, ∑ w, ψ w v * discreteGrad f w v) + N.dualEnergy ψ := by
    simp only [dualEnergy]
    simp_rw [hterm]
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  rw [horth] at hdecomp
  linarith

end BouRabeeGwynne.FiniteConductanceNetwork
