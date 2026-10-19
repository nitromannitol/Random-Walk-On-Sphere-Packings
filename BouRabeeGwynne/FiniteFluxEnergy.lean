-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/FiniteFluxEnergy.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.DualDirichlet
import BouRabeeGwynne.FiniteDirichlet

open scoped BigOperators Classical

namespace BouRabeeGwynne.FiniteConductanceNetwork

variable {V : Type*} [Fintype V] (N : FiniteConductanceNetwork V)

/-- The primal and dual energy normalizations agree on weighted gradients,
including pairs with zero conductance. -/
theorem energy_eq_half_dualEnergy_weightedGradient (f : V → ℝ) :
    N.energy f = (1 / 2 : ℝ) * N.dualEnergy (N.weightedGradient f) := by
  unfold energy dualEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  unfold weightedGradient discreteGrad
  rw [N.symm w v]
  by_cases ha : N.a v w = 0
  · simp [ha]
  · field_simp [ha]

/-- The finite variational step of Proposition 2.6: a harmonic solution with
the prescribed boundary data is compared to an actual divergence-free flux.
The remaining right side is its genuine edge residual energy. -/
theorem energy_error_le_flux_residual (A : Set V) (hD hC : V → ℝ)
    (hsol : N.SolvesDirichlet A hC hD) (Φ : V → V → ℝ)
    (hΦ : IsDiscreteVectorField Φ)
    (hΦsupport : ∀ w v, N.a w v = 0 → Φ w v = 0)
    (hΦdiv : ∀ v ∈ A, discreteDiv Φ v = 0) :
    N.energy (hD - hC) ≤ (1 / 2 : ℝ) *
      N.dualEnergy (fun w v => Φ w v - N.weightedGradient hC w v) := by
  let θ : V → V → ℝ := fun w v => Φ w v - N.weightedGradient hC w v
  have hθ : IsDiscreteVectorField θ := by
    intro w v
    dsimp [θ]
    rw [hΦ w v, N.weightedGradient_antisymm hC w v]
    ring
  have hsupport : ∀ w v, N.a w v = 0 → θ w v = 0 := by
    intro w v ha
    simp [θ, hΦsupport w v ha, weightedGradient, ha]
  have hboundary : ∀ v, v ∉ A → (hD - hC) v = 0 := by
    intro v hv
    simp only [Pi.sub_apply, hsol.2 v hv, sub_self]
  have hdiv : ∀ v ∈ A,
      discreteDiv θ v = discreteDiv (N.weightedGradient (hD - hC)) v := by
    intro v hv
    calc
      discreteDiv θ v = discreteDiv Φ v - discreteDiv (N.weightedGradient hC) v := by
        simp only [discreteDiv, θ, Finset.sum_sub_distrib]
      _ = discreteDiv (N.weightedGradient (hD - hC)) v := by
        simp only [hΦdiv v hv, N.div_weightedGradient_eq_laplacian,
          N.laplacian_sub, hsol.1 v hv]
  rw [N.energy_eq_half_dualEnergy_weightedGradient]
  exact mul_le_mul_of_nonneg_left
    (N.dual_variational_principle A (hD - hC) θ hθ hsupport hboundary hdiv)
    (by norm_num)

/-- Localized finite variational estimate. The residual vanishes on pairs
whose two endpoints are outside the current interior, so the right side can
be bounded by a shrinking incident-edge mass during the Section 3 iteration. -/
theorem energy_error_le_incident_flux_residual (A : Set V) (hD hC : V → ℝ)
    (hsol : N.SolvesDirichlet A hC hD) (Φ : V → V → ℝ)
    (hΦ : IsDiscreteVectorField Φ)
    (hΦsupport : ∀ w v, N.a w v = 0 → Φ w v = 0)
    (hΦdiv : ∀ v ∈ A, discreteDiv Φ v = 0) :
    N.energy (hD - hC) ≤ (1 / 2 : ℝ) *
      (∑ v, ∑ w, if w ∈ A ∨ v ∈ A then
        (Φ w v - N.weightedGradient hC w v) ^ 2 / N.a w v else 0) := by
  let θ : V → V → ℝ := fun w v =>
    if w ∈ A ∨ v ∈ A then Φ w v - N.weightedGradient hC w v else 0
  have hθ : IsDiscreteVectorField θ := by
    intro w v
    by_cases hinc : w ∈ A ∨ v ∈ A
    · have hrev : v ∈ A ∨ w ∈ A := hinc.symm
      simp only [θ, if_pos hinc, if_pos hrev]
      rw [hΦ w v, N.weightedGradient_antisymm hC w v]
      ring
    · have hrev : ¬ (v ∈ A ∨ w ∈ A) := fun h => hinc h.symm
      simp only [θ, if_neg hinc, if_neg hrev, neg_zero]
  have hsupport : ∀ w v, N.a w v = 0 → θ w v = 0 := by
    intro w v ha
    simp only [θ, hΦsupport w v ha, weightedGradient, ha, zero_mul, sub_self,
      ite_self]
  have hboundary : ∀ v, v ∉ A → (hD - hC) v = 0 := by
    intro v hv
    simp only [Pi.sub_apply, hsol.2 v hv, sub_self]
  have hdiv : ∀ v ∈ A,
      discreteDiv θ v = discreteDiv (N.weightedGradient (hD - hC)) v := by
    intro v hv
    calc
      discreteDiv θ v = discreteDiv Φ v - discreteDiv (N.weightedGradient hC) v := by
        simp only [discreteDiv, θ, hv, or_true, if_true, Finset.sum_sub_distrib]
      _ = discreteDiv (N.weightedGradient (hD - hC)) v := by
        simp only [hΦdiv v hv, N.div_weightedGradient_eq_laplacian,
          N.laplacian_sub, hsol.1 v hv]
  have hbound := mul_le_mul_of_nonneg_left
    (N.dual_variational_principle A (hD - hC) θ hθ hsupport hboundary hdiv)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  rw [← N.energy_eq_half_dualEnergy_weightedGradient] at hbound
  have henergy : N.dualEnergy θ =
      ∑ v, ∑ w, if w ∈ A ∨ v ∈ A then
        (Φ w v - N.weightedGradient hC w v) ^ 2 / N.a w v else 0 := by
    unfold dualEnergy
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro w _
    by_cases hinc : w ∈ A ∨ v ∈ A <;> simp [θ, hinc]
  rw [henergy] at hbound
  exact hbound

end BouRabeeGwynne.FiniteConductanceNetwork
