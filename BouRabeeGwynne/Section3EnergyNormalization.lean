-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/Section3EnergyNormalization.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.Section3ColumnEstimate
import BouRabeeGwynne.Section3EdgeSums
import BouRabeeGwynne.TilingNetwork

/-! Canonical network energy equals the column argument’s once-oriented energy. -/

open scoped Classical BigOperators

namespace BouRabeeGwynne.TilingData

variable {d : ℕ} (T : TilingData d)

lemma sum_orientedInteriorEdges_eq_half_ordered (R : Set T.V) [Fintype R]
    (A : Set R) (g : T.V → T.V → ℝ) (hsymm : ∀ v w, g v w = g w v) :
    (∑ p ∈ T.orientedInteriorEdges R A, g p.1 p.2) =
      (1 / 2 : ℝ) * ∑ v : R, ∑ w : R,
        if T.adj v w ∧ (v ∈ A ∨ w ∈ A) then g v w else 0 := by
  let F : Sym2 R → ℝ := Sym2.lift ⟨fun v w : R => g v w, fun v w => hsymm v w⟩
  have hsum : (∑ p ∈ T.orientedInteriorEdges R A, g p.1 p.2) =
      ∑ a ∈ (T.contactGraph R A).edgeFinset, F a := by
    rw [T.sum_orientedInteriorEdges]
    apply Finset.sum_congr rfl
    intro a _
    have hout : s(a.out.1, a.out.2) = a := Quot.out_eq a
    exact congrArg F hout
  rw [hsum, edge_sum_eq_half_sum_adjacent_pairs]
  simp only [contactGraph, F, Sym2.lift_mk]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  split_ifs with h
  · exact ite_eq_left h
  · exact ite_eq_right h

end BouRabeeGwynne.TilingData

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

/-- For zero exterior data, the finite network energy is exactly the column
argument's sum over each interior-incident edge once. -/
theorem incidentEnergy_eq_networkEnergy (R : Set T.V) [Fintype R] (A : Set R)
    (f : T.V → ℝ) (hzero : ∀ v : R, v ∉ A → f v = 0) :
    T.incidentEnergy R A f = (T.finiteNetwork R).energy (fun v : R => f v) := by
  unfold incidentEnergy
  rw [T.toTilingData.sum_orientedInteriorEdges_eq_half_ordered R A
    (fun v w => T.conductanceReal v w * (f w - f v) ^ 2)
    (fun v w => by rw [T.conductanceReal_symm v w]; ring)]
  unfold FiniteConductanceNetwork.energy
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  change (if T.adj v w ∧ (v ∈ A ∨ w ∈ A) then
    T.conductanceReal v w * (f w - f v) ^ 2 else 0) =
      T.conductanceReal v w * (f w - f v) ^ 2
  by_cases hadj : T.adj v w
  · by_cases hinc : v ∈ A ∨ w ∈ A
    · rw [if_pos ⟨hadj, hinc⟩]
    · have hv := hzero v (fun hv => hinc (Or.inl hv))
      have hw := hzero w (fun hw => hinc (Or.inr hw))
      simp only [hv, hw, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, ite_self]
  · have ha : T.conductanceReal v w = 0 := by simp [conductanceReal, hadj]
    simp only [ha, zero_mul, ite_self]

/-- The geometric mass has the same incident-edge normalization as the localized
flux residual bound, with no exterior-exterior contributions. -/
theorem incidentMass_eq_half_ordered (R : Set T.V) [Fintype R] (A : Set R) :
    T.incidentMass R A = (1 / 2 : ℝ) * ∑ v : R, ∑ w : R,
      if T.adj v w ∧ (v ∈ A ∨ w ∈ A) then
        (T.facetVolume v w).toReal * ‖T.pos w - T.pos v‖ else 0 := by
  unfold incidentMass
  apply T.toTilingData.sum_orientedInteriorEdges_eq_half_ordered R A
    (fun v w => (T.facetVolume v w).toReal * ‖T.pos w - T.pos v‖)
  intro v w
  exact congrArg₂ (fun a b : ℝ => a * b)
    (congrArg ENNReal.toReal (T.toTilingData.facetVolume_symm v w))
    (norm_sub_rev (T.pos w) (T.pos v))

end BouRabeeGwynne.OrthogonalTiling
