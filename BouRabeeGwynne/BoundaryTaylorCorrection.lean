-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/BoundaryTaylorCorrection.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.BoundaryEdgeResponse
import BouRabeeGwynne.FiniteFluxEnergy

/-!
# Finite boundary correction for hypothesis III

The correction solves a specified Poisson equation on the actual finite
conductance network. Taking `R u w` to be the Taylor remainder removes the
exterior endpoint from the boundary flux residual. The variational estimate
below is proved for this constructed correction, with no assumed energy bound.
-/

open scoped BigOperators Classical

namespace BouRabeeGwynne.FiniteConductanceNetwork

variable {V : Type*} [Fintype V] (N : FiniteConductanceNetwork V)

noncomputable def boundaryCorrectionSource (A : Set V) (R : V → V → ℝ) (v : V) : ℝ :=
  -(∑ w, if w ∉ A then N.a v w * R v w else 0)

noncomputable def boundaryCorrection (A : Set V) (hA : N.BoundaryAccessible A)
    (R : V → V → ℝ) : V → ℝ :=
  N.poissonSolution A hA (N.boundaryCorrectionSource A R)

theorem boundaryCorrection_laplacian (A : Set V) (hA : N.BoundaryAccessible A)
    (R : V → V → ℝ) {v : V} (hv : v ∈ A) :
    N.laplacian (N.boundaryCorrection A hA R) v =
      -(∑ w, if w ∉ A then N.a v w * R v w else 0) :=
  N.poissonSolution_laplacian A hA _ hv

theorem boundaryCorrection_boundary (A : Set V) (hA : N.BoundaryAccessible A)
    (R : V → V → ℝ) {v : V} (hv : v ∉ A) : N.boundaryCorrection A hA R v = 0 :=
  N.poissonSolution_boundary A hA _ hv

theorem laplacian_const_mul (c : ℝ) (f : V → ℝ) (v : V) :
    N.laplacian (fun x => c * f x) v = c * N.laplacian f v := by
  have heq : (fun x => c * f x) = c • f := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
  rw [heq]
  exact N.laplacian_smul c f v

/-- The correction is exactly the weighted sum of concrete boundary-edge
responses. This representation supplies its nested-region cancellation. -/
theorem boundaryCorrection_eq_sum_response (A : Set V) (hA : N.BoundaryAccessible A)
    (R : V → V → ℝ) : N.boundaryCorrection A hA R =
      fun x => ∑ u, ∑ w, R u w * N.boundaryEdgeResponse A hA u w x := by
  symm
  apply N.poissonSolution_unique A hA
  · intro v hv
    rw [N.laplacian_finset_sum]
    simp only [N.laplacian_finset_sum, N.laplacian_const_mul,
      N.boundaryEdgeResponse_laplacian A hA _ _ hv]
    rw [Finset.sum_eq_single v]
    · unfold boundaryCorrectionSource
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro w _
      by_cases hw : w ∈ A <;> simp [boundaryEdgeSource, hv, hw] <;> ring
    · intro u _ huv
      simp [boundaryEdgeSource, Ne.symm huv]
    · simp
  · intro v hv
    simp [N.boundaryEdgeResponse_boundary A hA _ _ hv]

/-- A boundary correction never exceeds the largest absolute reward on a
positive-conductance edge actually leaving its interior. -/
theorem boundaryCorrection_abs_le (A : Set V) (hA : N.BoundaryAccessible A)
    (R : V → V → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hR : ∀ u ∈ A, ∀ w, w ∉ A → 0 < N.a u w → |R u w| ≤ C) (x : V) :
    |N.boundaryCorrection A hA R x| ≤ C := by
  rw [N.boundaryCorrection_eq_sum_response]
  have hterm : ∀ u w, |R u w * N.boundaryEdgeResponse A hA u w x| ≤
      C * N.boundaryEdgeResponse A hA u w x := by
    intro u w
    by_cases hedge : u ∈ A ∧ w ∉ A
    · by_cases ha : N.a u w = 0
      · simp [N.boundaryEdgeResponse_eq_zero_of_conductance A hA u w ha]
      · rw [abs_mul, abs_of_nonneg (N.boundaryEdgeResponse_nonneg A hA u w x)]
        exact mul_le_mul_of_nonneg_right
          (hR u hedge.1 w hedge.2 (lt_of_le_of_ne (N.nonneg u w) (Ne.symm ha)))
          (N.boundaryEdgeResponse_nonneg A hA u w x)
    · simp [N.boundaryEdgeResponse_eq_zero A hA u w hedge]
  calc
    _ ≤ ∑ u, |∑ w, R u w * N.boundaryEdgeResponse A hA u w x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u, ∑ w, |R u w * N.boundaryEdgeResponse A hA u w x| :=
      Finset.sum_le_sum (fun u _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ u, ∑ w, C * N.boundaryEdgeResponse A hA u w x :=
      Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun w _ => hterm u w))
    _ = C * (∑ u, ∑ w, N.boundaryEdgeResponse A hA u w x) := by
      simp only [Finset.mul_sum]
    _ ≤ C := by
      rw [N.sum_boundaryEdgeResponse A hA x]
      split_ifs <;> simp [hC]

/-- Only edges which become boundary edges after passing from `A` to `B`
contribute: their old exterior endpoint still lies in `A`. -/
noncomputable def newBoundaryCorrection (A B : Set V) (hB : N.BoundaryAccessible B)
    (R : V → V → ℝ) : V → ℝ :=
  N.boundaryCorrection B hB (fun u w => if w ∈ A then R u w else 0)

theorem newBoundaryCorrection_abs_le {A B : Set V} (hBA : B ⊆ A)
    (hB : N.BoundaryAccessible B) (R : V → V → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hR : ∀ u ∈ A, ∀ w ∈ A, 0 < N.a u w → |R u w| ≤ C) (x : V) :
    |N.newBoundaryCorrection A B hB R x| ≤ C := by
  apply N.boundaryCorrection_abs_le B hB _ hC
  intro u hu w _ ha
  by_cases hw : w ∈ A
  · simpa only [if_pos hw] using hR u (hBA hu) w hw ha
  · simpa only [if_neg hw, abs_zero] using hC

/-- The nested correction identity telescopes directly. Its extra term only
uses old interior-interior edges, so their remainders have the smaller scale. -/
theorem dirichletSolution_boundaryCorrection {A B : Set V} (hBA : B ⊆ A)
    (hA : N.BoundaryAccessible A) (hB : N.BoundaryAccessible B) (R : V → V → ℝ) :
    N.dirichletSolution B hB (N.boundaryCorrection A hA R) =
      N.boundaryCorrection A hA R - N.boundaryCorrection B hB R +
        N.newBoundaryCorrection A B hB R := by
  apply N.dirichlet_unique B hB (N.dirichletSolution_spec B hB _)
  constructor
  · intro v hv
    rw [N.laplacian_add, N.laplacian_sub,
      N.boundaryCorrection_laplacian A hA R (hBA hv),
      N.boundaryCorrection_laplacian B hB R hv]
    change -(∑ w, if w ∉ A then N.a v w * R v w else 0) -
        (-(∑ w, if w ∉ B then N.a v w * R v w else 0)) +
        N.laplacian (N.boundaryCorrection B hB
          (fun u w => if w ∈ A then R u w else 0)) v = 0
    rw [N.boundaryCorrection_laplacian B hB _ hv]
    have hs : (∑ w, if w ∉ B then N.a v w * R v w else 0) =
        (∑ w, if w ∉ A then N.a v w * R v w else 0) +
        ∑ w, if w ∉ B then N.a v w * (if w ∈ A then R v w else 0) else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro w _
      by_cases hwB : w ∈ B
      · simp [hwB, hBA hwB]
      · by_cases hwA : w ∈ A <;> simp [hwB, hwA]
    rw [hs]
    ring
  · intro v hv
    simp only [Pi.add_apply, Pi.sub_apply,
      N.boundaryCorrection_boundary B hB R hv, newBoundaryCorrection,
      N.boundaryCorrection_boundary B hB _ hv, sub_zero, add_zero]

/-- Antisymmetric boundary field with the prescribed outward reward. -/
noncomputable def boundaryRewardField (A : Set V) (R : V → V → ℝ) (w v : V) : ℝ :=
  if v ∈ A then (if w ∈ A then 0 else N.a v w * R v w)
  else (if w ∈ A then -(N.a w v * R w v) else 0)

theorem boundaryRewardField_antisymm (A : Set V) (R : V → V → ℝ) :
    IsDiscreteVectorField (N.boundaryRewardField A R) := by
  intro w v
  by_cases hv : v ∈ A <;> by_cases hw : w ∈ A <;> simp [boundaryRewardField, hv, hw]

theorem boundaryRewardField_support (A : Set V) (R : V → V → ℝ)
    (w v : V) (ha : N.a w v = 0) : N.boundaryRewardField A R w v = 0 := by
  have havw : N.a v w = 0 := (N.symm v w).trans ha
  simp [boundaryRewardField, ha, havw]

theorem boundaryRewardField_div (A : Set V) (R : V → V → ℝ)
    {v : V} (hv : v ∈ A) : discreteDiv (N.boundaryRewardField A R) v =
      ∑ w, if w ∉ A then N.a v w * R v w else 0 := by
  unfold discreteDiv
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : w ∈ A <;> simp [boundaryRewardField, hv, hw]

/-- Restrict the residual to incident edges and insert the boundary correction. -/
noncomputable def correctedIncidentFlux (A : Set V) (θ R : V → V → ℝ)
    (w v : V) : ℝ :=
  (if w ∈ A ∨ v ∈ A then θ w v else 0) + N.boundaryRewardField A R w v

theorem correctedIncidentFlux_antisymm (A : Set V) (θ R : V → V → ℝ)
    (hθ : IsDiscreteVectorField θ) : IsDiscreteVectorField (N.correctedIncidentFlux A θ R) := by
  intro w v
  have hβ := N.boundaryRewardField_antisymm A R w v
  by_cases hi : w ∈ A ∨ v ∈ A
  · have hr : v ∈ A ∨ w ∈ A := hi.symm
    simp only [correctedIncidentFlux, if_pos hi, if_pos hr, hθ w v, hβ]
    ring
  · have hr : ¬ (v ∈ A ∨ w ∈ A) := fun h => hi h.symm
    simp only [correctedIncidentFlux, if_neg hi, if_neg hr, zero_add, hβ]

theorem correctedIncidentFlux_support (A : Set V) (θ R : V → V → ℝ)
    (hθ : ∀ w v, N.a w v = 0 → θ w v = 0) (w v : V) (ha : N.a w v = 0) :
    N.correctedIncidentFlux A θ R w v = 0 := by
  simp [correctedIncidentFlux, hθ w v ha, N.boundaryRewardField_support A R w v ha]

theorem correctedIncidentFlux_div (A : Set V) (hA : N.BoundaryAccessible A)
    (e : V → ℝ) (θ R : V → V → ℝ)
    (hdiv : ∀ v ∈ A, discreteDiv θ v = N.laplacian e v) {v : V} (hv : v ∈ A) :
    discreteDiv (N.correctedIncidentFlux A θ R) v =
      N.laplacian (e - N.boundaryCorrection A hA R) v := by
  have hsplit : discreteDiv (N.correctedIncidentFlux A θ R) v =
      discreteDiv θ v + discreteDiv (N.boundaryRewardField A R) v := by
    simp only [discreteDiv, correctedIncidentFlux, hv, or_true, ite_true,
      Finset.sum_add_distrib]
  rw [hsplit, hdiv v hv, N.boundaryRewardField_div A R hv, N.laplacian_sub,
    N.boundaryCorrection_laplacian A hA R hv, sub_neg_eq_add]

/-- The corrected finite variational estimate used by hypothesis III. -/
theorem energy_boundaryCorrected_le_flux (A : Set V) (hA : N.BoundaryAccessible A)
    (e : V → ℝ) (θ R : V → V → ℝ) (hθ : IsDiscreteVectorField θ)
    (hsupport : ∀ w v, N.a w v = 0 → θ w v = 0)
    (he : ∀ v, v ∉ A → e v = 0)
    (hdiv : ∀ v ∈ A, discreteDiv θ v = N.laplacian e v) :
    N.energy (e - N.boundaryCorrection A hA R) ≤
      (1 / 2 : ℝ) * N.dualEnergy (N.correctedIncidentFlux A θ R) := by
  have hb : ∀ v, v ∉ A → (e - N.boundaryCorrection A hA R) v = 0 := by
    intro v hv
    simp [he v hv, N.boundaryCorrection_boundary A hA R hv]
  have hd : ∀ v ∈ A, discreteDiv (N.correctedIncidentFlux A θ R) v =
      discreteDiv (N.weightedGradient (e - N.boundaryCorrection A hA R)) v := by
    intro v hv
    rw [N.div_weightedGradient_eq_laplacian]
    exact N.correctedIncidentFlux_div A hA e θ R hdiv hv
  rw [N.energy_eq_half_dualEnergy_weightedGradient]
  exact mul_le_mul_of_nonneg_left
    (N.dual_variational_principle A (e - N.boundaryCorrection A hA R)
      (N.correctedIncidentFlux A θ R) (N.correctedIncidentFlux_antisymm A θ R hθ)
      (N.correctedIncidentFlux_support A θ R hsupport) hb hd) (by norm_num)

end BouRabeeGwynne.FiniteConductanceNetwork
