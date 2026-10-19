-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/HypIIIGeometricScale.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.Section3EnergyNormalization
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The actual hypothesis III bounds local tile diameters by incident mass. -/

open scoped Classical BigOperators ENNReal

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

theorem edgeMass_le_twice_incidentMass (R : Set T.V) [Fintype R] (A : Set R)
    {v w : R} (hv : v ∈ A) (ha : T.adj v w) :
    (T.facetVolume v w).toReal * ‖T.pos w - T.pos v‖ ≤ 2 * T.incidentMass R A := by
  let F : R → R → ℝ := fun u z =>
    if T.adj u z ∧ (u ∈ A ∨ z ∈ A) then
      (T.facetVolume u z).toReal * ‖T.pos z - T.pos u‖ else 0
  have hnonneg : ∀ u z, 0 ≤ F u z := by
    intro u z
    dsimp only [F]
    split_ifs <;> positivity
  have h₁ : F v w ≤ ∑ z, F v z :=
    Finset.single_le_sum (fun z _ => hnonneg v z) (Finset.mem_univ w)
  have h₂ : (∑ z, F v z) ≤ ∑ u, ∑ z, F u z :=
    Finset.single_le_sum (fun u _ => Finset.sum_nonneg (fun z _ => hnonneg u z))
      (Finset.mem_univ v)
  have h := h₁.trans h₂
  have hleft : F v w = (T.facetVolume v w).toReal * ‖T.pos w - T.pos v‖ := by
    simp only [F, ha, hv, true_or, and_self, ite_true]
  rw [hleft] at h
  apply h.trans_eq
  rw [T.incidentMass_eq_half_ordered]
  dsimp only [F]
  ring

/-- Every incident edge in the paper's supremum belongs to the actual finite
closed region. Consequently its maximum scale is bounded by total mass. -/
theorem incidentScale_le_rpow_incidentMass (R : Set T.V) [Fintype R] (A : Set R)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    {α : ℝ} (hα : 0 ≤ α) {v : R} (hv : v ∈ A) :
    T.incidentScale α v ≤ (ENNReal.ofReal (2 * T.incidentMass R A)).rpow α := by
  change (⨆ w : T.V, if T.adj v w then
    (T.edgeLength v w).rpow α * (T.facetVolume v w).rpow α else 0) ≤ _
  apply iSup_le
  intro w
  by_cases ha : T.adj v w
  · rw [if_pos ha]
    simp only [ENNReal.rpow_eq_pow]
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hα]
    apply ENNReal.rpow_le_rpow _ hα
    let wR : R := ⟨w, hneighbors v hv w ha⟩
    have hmass := T.edgeMass_le_twice_incidentMass R A (w := wR) hv ha
    have hfinite : T.edgeLength v w * T.facetVolume v w ≠ ∞ :=
      ENNReal.mul_ne_top (T.toTilingData.edgeLength_ne_top v w)
        (T.toTilingData.facetVolume_ne_top ha)
    have hreal : (T.edgeLength v w * T.facetVolume v w).toReal ≤
        2 * T.incidentMass R A := by
      rw [ENNReal.toReal_mul]
      change (ENNReal.ofReal ‖T.pos w - T.pos v‖).toReal *
        (T.facetVolume v w).toReal ≤ _
      rw [ENNReal.toReal_ofReal (norm_nonneg _), mul_comm]
      exact hmass
    calc
      _ = ENNReal.ofReal (T.edgeLength v w * T.facetVolume v w).toReal :=
        (ENNReal.ofReal_toReal hfinite).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hreal
  · simp only [if_neg ha, zero_le]

/-- Specialize the exact hypothesis III inequality, with no bound on exterior
cell diameters, to the mass of the current interior. -/
theorem cell_diam_le_rpow_incidentMass (R : Set T.V) [Fintype R] (A : Set R)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    {α : ℝ} (hα : 0 ≤ α) {C : ℝ≥0∞} (hC : C ≠ ∞)
    {v : R} (hv : v ∈ A)
    (hreg : (T.cell v).diamENN ≤ C * T.incidentScale α v) :
    Metric.diam (T.cell v).carrier ≤ C.toReal * (2 * T.incidentMass R A) ^ α := by
  have hmass : 0 ≤ 2 * T.incidentMass R A :=
    mul_nonneg (by norm_num) (T.incidentMass_nonneg R A)
  have hscale := T.incidentScale_le_rpow_incidentMass R A hneighbors hα hv
  have hbound := hreg.trans (mul_le_mul_right hscale C)
  simp only [ENNReal.rpow_eq_pow] at hbound
  rw [ENNReal.ofReal_rpow_of_nonneg hmass hα] at hbound
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top) hbound
  simpa only [ConvexPolytope.diamENN, ENNReal.toReal_ofReal Metric.diam_nonneg,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hmass α)] using hreal

end BouRabeeGwynne.OrthogonalTiling
