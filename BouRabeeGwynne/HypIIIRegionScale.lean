-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/HypIIIRegionScale.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.HypIIIGeometricScale
import BouRabeeGwynne.RegionDiameter
import Mathlib.Analysis.SpecificLimits.Normed

/-! Hypothesis III turns geometric mass decay into vanishing current diameters. -/

open scoped ENNReal Topology
open Filter

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

theorem regionDiameter_le_rpow_incidentMass (R : Set T.V) [Fintype R] (A : Set R)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    {α : ℝ} (hα : 0 ≤ α) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hreg : ∀ v ∈ A, (T.cell v).diamENN ≤ C * T.incidentScale α v) :
    T.toTilingData.regionDiameter R A ≤ C.toReal * (2 * T.incidentMass R A) ^ α := by
  have hm := T.incidentMass_nonneg R A
  apply T.toTilingData.regionDiameter_le R A
    (mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (by positivity) α))
  intro v hv
  exact T.cell_diam_le_rpow_incidentMass R A hneighbors hα hC hv (hreg v hv)

theorem regionDiameter_le_geometric_of_mass (R : Set T.V) [Fintype R]
    (A : ℕ → Set R)
    (hneighbors : ∀ n v, v ∈ A n → ∀ w, T.adj v w → w ∈ R)
    {α : ℝ} (hα : 0 ≤ α) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hreg : ∀ n v, v ∈ A n → (T.cell v).diamENN ≤ C * T.incidentScale α v)
    {I : ℝ} (hI : 0 ≤ I)
    (hmass : ∀ n, T.incidentMass R (A n) ≤ I * (1 / 2 : ℝ) ^ n) :
    ∀ n, T.toTilingData.regionDiameter R (A n) ≤
      (C.toReal * (2 * I) ^ α) * ((1 / 2 : ℝ) ^ α) ^ n := by
  intro n
  have hm := T.incidentMass_nonneg R (A n)
  calc
    _ ≤ C.toReal * (2 * T.incidentMass R (A n)) ^ α :=
      T.regionDiameter_le_rpow_incidentMass R (A n) (hneighbors n) hα hC (hreg n)
    _ ≤ C.toReal * (2 * (I * (1 / 2 : ℝ) ^ n)) ^ α := by
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      apply Real.rpow_le_rpow (by positivity) _ hα
      exact mul_le_mul_of_nonneg_left (hmass n) (by norm_num)
    _ = _ := by
      rw [← mul_assoc, Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      ring

/-- A fixed finite network eventually has empty interior under the genuine
mass decay and the original hypothesis III inequality. -/
theorem eventually_empty_of_geometric_mass_hypIII (hd : 1 ≤ d)
    (R : Set T.V) [Fintype R] (A : ℕ → Set R)
    (hneighbors : ∀ n v, v ∈ A n → ∀ w, T.adj v w → w ∈ R)
    {α : ℝ} (hα : 0 < α) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hreg : ∀ n v, v ∈ A n → (T.cell v).diamENN ≤ C * T.incidentScale α v)
    {I : ℝ} (hI : 0 ≤ I)
    (hmass : ∀ n, T.incidentMass R (A n) ≤ I * (1 / 2 : ℝ) ^ n) :
    ∀ᶠ n in atTop, A n = ∅ := by
  have hr0 : 0 ≤ (1 / 2 : ℝ) ^ α := Real.rpow_nonneg (by norm_num) α
  have hr1 : (1 / 2 : ℝ) ^ α < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα
  have hlim : Tendsto (fun n : ℕ =>
      (C.toReal * (2 * I) ^ α) * ((1 / 2 : ℝ) ^ α) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := C.toReal * (2 * I) ^ α)).mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1)
  apply T.toTilingData.eventually_empty_of_regionDiameter_tendsto_zero hd R A
  exact squeeze_zero (fun n => T.toTilingData.regionDiameter_nonneg R (A n))
    (T.regionDiameter_le_geometric_of_mass R A hneighbors hα.le hC hreg hI hmass) hlim

end BouRabeeGwynne.OrthogonalTiling
