module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/Section3MassTrimming.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.Section3EnergyNormalization
public import BouRabeeGwynne.Section3Iteration

@[expose] public section

/-! Exact finite trimming estimates, with the global edge length factor explicit. -/

open scoped Classical BigOperators
open BouRabeeGwynne.FiniteConductanceNetwork

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

/-- A retained crossing edge is charged to its actual gradient energy.
The length and gradient cutoffs are independent. -/
lemma facet_weight_le_scaled_gradient_energy {v w : T.V}
    (hvw : T.adj v w) (f : T.V → ℝ) {L ℓ : ℝ}
    (hℓ : 0 < ℓ) (hlength : ‖T.pos w - T.pos v‖ ≤ L)
    (hgradient : ℓ < |f w - f v|) :
    (T.facetVolume v w).toReal * ‖T.pos w - T.pos v‖ ≤
      (L ^ 2 / ℓ ^ 2) * (T.conductanceReal v w * (f w - f v) ^ 2) := by
  have hL : 0 ≤ L := (norm_nonneg _).trans hlength
  have hsquare : ‖T.pos w - T.pos v‖ ^ 2 ≤ L ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hL).mpr hlength
  have hgrad : ℓ ^ 2 ≤ (f w - f v) ^ 2 := by
    have h := (sq_le_sq₀ hℓ.le (abs_nonneg _)).mpr hgradient.le
    simpa only [sq_abs] using h
  calc
    _ = T.conductanceReal v w * ‖T.pos w - T.pos v‖ ^ 2 :=
      (T.conductanceReal_mul_edge_norm_sq hvw).symm
    _ ≤ T.conductanceReal v w * L ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare (T.conductanceReal_nonneg _ _)
    _ = (L ^ 2 / ℓ ^ 2) * (T.conductanceReal v w * ℓ ^ 2) := by
      field_simp [hℓ.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hgrad (T.conductanceReal_nonneg _ _))
      (div_nonneg (sq_nonneg _) (sq_nonneg _))

/-- Mass of edges with both endpoints in the designated bad set. -/
noncomputable def internalMass (R : Set T.V) [Fintype R] (B : Set R) : ℝ :=
  (1 / 2 : ℝ) * ∑ v : R, ∑ w : R,
    if T.adj v w ∧ v ∈ B ∧ w ∈ B then
      (T.facetVolume v w).toReal * ‖T.pos w - T.pos v‖ else 0

/-- The trimming rule bounds all retained boundary edges by actual gradient
energy. The remaining internal bad edges will be bounded by a geometric cylinder. -/
theorem incidentMass_trimmed_le_internalMass_add_energy
    (R : Set T.V) [Fintype R] (A : Set R) (f : T.V → ℝ) (κ δ : ℝ)
    (hlength : ∀ v w : R, T.adj v w → ‖T.pos w - T.pos v‖ ≤ δ) :
    T.incidentMass R ((T.finiteNetwork R).trimmedErrorSet A (fun v => f v) κ δ) ≤
      T.internalMass R (errorBadSet A (fun v => f v) κ) +
        (T.finiteNetwork R).energy (fun v => f v) := by
  let N := T.finiteNetwork R
  let B := errorBadSet A (fun v : R => f v) κ
  let S := N.trimmedErrorSet A (fun v : R => f v) κ δ
  have hterm (v w : R) :
      (if T.adj v w ∧ (v ∈ S ∨ w ∈ S) then
        (T.facetVolume v w).toReal * ‖T.pos w - T.pos v‖ else 0) ≤
      (if T.adj v w ∧ v ∈ B ∧ w ∈ B then
        (T.facetVolume v w).toReal * ‖T.pos w - T.pos v‖ else 0) +
      T.conductanceReal v w * (f w - f v) ^ 2 := by
    have hE : 0 ≤ T.conductanceReal v w * (f w - f v) ^ 2 :=
      mul_nonneg (T.conductanceReal_nonneg _ _) (sq_nonneg _)
    have hM : 0 ≤ (T.facetVolume v w).toReal * ‖T.pos w - T.pos v‖ :=
      mul_nonneg ENNReal.toReal_nonneg (norm_nonneg _)
    by_cases hinc : T.adj v w ∧ (v ∈ S ∨ w ∈ S)
    · rw [if_pos hinc]
      by_cases hbad : v ∈ B ∧ w ∈ B
      · rw [if_pos ⟨hinc.1, hbad⟩]
        exact le_add_of_nonneg_right hE
      · have hlarge : δ < |f w - f v| := by
          rcases hinc.2 with hv | hw
          · have hwB : w ∉ B := fun hw => hbad ⟨hv.1, hw⟩
            simpa only [abs_sub_comm] using hv.2 w
              (T.conductanceReal_pos_iff.mpr hinc.1) hwB
          · have hvB : v ∉ B := fun hv => hbad ⟨hv, hw.1⟩
            exact hw.2 v (T.conductanceReal_pos_iff.mpr (T.adj_symm hinc.1)) hvB
        rw [if_neg (fun h => hbad h.2), zero_add]
        exact T.facet_weight_le_gradient_energy hinc.1 f (hlength v w hinc.1) hlarge
    · rw [if_neg hinc]
      exact add_nonneg (by split_ifs; exact hM; exact le_rfl) hE
  rw [T.incidentMass_eq_half_ordered]
  change _ ≤ (1 / 2 : ℝ) * (∑ v : R, ∑ w : R,
      if T.adj v w ∧ v ∈ B ∧ w ∈ B then
        (T.facetVolume v w).toReal * ‖T.pos w - T.pos v‖ else 0) +
      (1 / 2 : ℝ) * (∑ v : R, ∑ w : R,
        T.conductanceReal v w * (f w - f v) ^ 2)
  rw [← mul_add, ← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro v _
  exact Finset.sum_le_sum (fun w _ => hterm v w)

/-- The version needed when boundary edges may meet cells larger than the
current interior scale. The coefficient records the actual global length
bound; no estimate on an exterior cell's shrinking diameter is assumed. -/
theorem incidentMass_trimmed_le_internalMass_add_scaled_energy
    (R : Set T.V) [Fintype R] (A : Set R) (f : T.V → ℝ) (κ : ℝ)
    {L ℓ : ℝ} (hℓ : 0 < ℓ)
    (hlength : ∀ v w : R, T.adj v w → ‖T.pos w - T.pos v‖ ≤ L) :
    T.incidentMass R ((T.finiteNetwork R).trimmedErrorSet A (fun v => f v) κ ℓ) ≤
      T.internalMass R (errorBadSet A (fun v => f v) κ) +
        (L ^ 2 / ℓ ^ 2) * (T.finiteNetwork R).energy (fun v => f v) := by
  let N := T.finiteNetwork R
  let B := errorBadSet A (fun v : R => f v) κ
  let S := N.trimmedErrorSet A (fun v : R => f v) κ ℓ
  let c := L ^ 2 / ℓ ^ 2
  have hc : 0 ≤ c := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hterm (v w : R) :
      (if T.adj v w ∧ (v ∈ S ∨ w ∈ S) then
        (T.facetVolume v w).toReal * ‖T.pos w - T.pos v‖ else 0) ≤
      (if T.adj v w ∧ v ∈ B ∧ w ∈ B then
        (T.facetVolume v w).toReal * ‖T.pos w - T.pos v‖ else 0) +
      c * (T.conductanceReal v w * (f w - f v) ^ 2) := by
    have hE : 0 ≤ c * (T.conductanceReal v w * (f w - f v) ^ 2) :=
      mul_nonneg hc (mul_nonneg (T.conductanceReal_nonneg _ _) (sq_nonneg _))
    have hM : 0 ≤ (T.facetVolume v w).toReal * ‖T.pos w - T.pos v‖ :=
      mul_nonneg ENNReal.toReal_nonneg (norm_nonneg _)
    by_cases hinc : T.adj v w ∧ (v ∈ S ∨ w ∈ S)
    · rw [if_pos hinc]
      by_cases hbad : v ∈ B ∧ w ∈ B
      · rw [if_pos ⟨hinc.1, hbad⟩]
        exact le_add_of_nonneg_right hE
      · have hlarge : ℓ < |f w - f v| := by
          rcases hinc.2 with hv | hw
          · have hwB : w ∉ B := fun hw => hbad ⟨hv.1, hw⟩
            simpa only [abs_sub_comm] using hv.2 w
              (T.conductanceReal_pos_iff.mpr hinc.1) hwB
          · have hvB : v ∉ B := fun hv => hbad ⟨hv, hw.1⟩
            exact hw.2 v (T.conductanceReal_pos_iff.mpr (T.adj_symm hinc.1)) hvB
        rw [if_neg (fun h => hbad h.2), zero_add]
        exact T.facet_weight_le_scaled_gradient_energy hinc.1 f hℓ
          (hlength v w hinc.1) hlarge
    · rw [if_neg hinc]
      exact add_nonneg (by split_ifs; exact hM; exact le_rfl) hE
  rw [T.incidentMass_eq_half_ordered]
  change _ ≤ (1 / 2 : ℝ) * (∑ v : R, ∑ w : R,
      if T.adj v w ∧ v ∈ B ∧ w ∈ B then
        (T.facetVolume v w).toReal * ‖T.pos w - T.pos v‖ else 0) +
      c * ((1 / 2 : ℝ) * (∑ v : R, ∑ w : R,
        T.conductanceReal v w * (f w - f v) ^ 2))
  calc
    _ ≤ (1 / 2 : ℝ) * (∑ v : R, ∑ w : R,
        ((if T.adj v w ∧ v ∈ B ∧ w ∈ B then
          (T.facetVolume v w).toReal * ‖T.pos w - T.pos v‖ else 0) +
        c * (T.conductanceReal v w * (f w - f v) ^ 2))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro v _
      exact Finset.sum_le_sum (fun w _ => hterm v w)
    _ = _ := by
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      ring

end BouRabeeGwynne.OrthogonalTiling
