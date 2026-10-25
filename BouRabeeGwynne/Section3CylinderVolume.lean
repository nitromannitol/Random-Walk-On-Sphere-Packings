module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/Section3CylinderVolume.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.Section3Projection
public import BouRabeeGwynne.PyramidSlices

@[expose] public section

/-!
# Section 3: volume of an orthogonal cylinder

The measure is computed from genuine perpendicular slices and translation isometries.
-/

open scoped ENNReal MeasureTheory
open MeasureTheory

namespace BouRabeeGwynne

variable {d : ℕ}

/-- The cylinder with horizontal base `Y` and line parameters in `[a,b]`. -/
def orthogonalCylinder (e : Euc d) (a b : ℝ) (Y : Set (Euc d)) : Set (Euc d) :=
  {x | hyperplaneProjection e x ∈ Y ∧ inner ℝ e x / inner ℝ e e ∈ Set.Icc a b}

lemma measurableSet_orthogonalCylinder (e : Euc d) (a b : ℝ)
    {Y : Set (Euc d)} (hY : MeasurableSet Y) :
    MeasurableSet (orthogonalCylinder e a b Y) := by
  exact (hY.preimage (hyperplaneProjection e).continuous.measurable).inter
    (measurableSet_Icc.preimage (by fun_prop :
      Measurable (fun x : Euc d => inner ℝ e x / inner ℝ e e)))

lemma orthogonalCylinder_slice (e : Euc d) (he : e ≠ 0) (a b t : ℝ)
    {Y : Set (Euc d)} (hY : ∀ y ∈ Y, inner ℝ e y = 0) :
    orthogonalCylinder e a b Y ∩ perpendicularSlice 0 e t =
      if t ∈ Set.Icc a b then (fun y => y + t • e) '' Y else ∅ := by
  have hn : inner ℝ e e ≠ 0 := (real_inner_self_pos.mpr he).ne'
  have hcoord (x : Euc d) (hx : x ∈ perpendicularSlice 0 e t) :
      inner ℝ e x / inner ℝ e e = t := by
    have h := (mem_perpendicularSlice 0 e x t).mp hx
    simp only [sub_zero] at h
    rw [h, mul_div_cancel_right₀ _ hn]
  ext x
  by_cases ht : t ∈ Set.Icc a b
  · rw [if_pos ht]
    constructor
    · rintro ⟨⟨hxY, _⟩, hslice⟩
      refine ⟨hyperplaneProjection e x, hxY, ?_⟩
      change hyperplaneProjection e x + t • e = x
      rw [hyperplaneProjection_apply, hcoord x hslice, sub_add_cancel]
    · rintro ⟨y, hy, rfl⟩
      have hc : inner ℝ e (y + t • e) / inner ℝ e e = t := by
        rw [inner_add_right, inner_smul_right, hY y hy, zero_add,
          mul_div_cancel_right₀ _ hn]
      refine ⟨⟨?_, by simpa only [hc] using ht⟩, ?_⟩
      · rw [hyperplaneProjection_add_smul he, hyperplaneProjection_eq_self e (hY y hy)]
        exact hy
      · change y + t • e ∈ perpendicularSlice 0 e t
        rw [mem_perpendicularSlice, sub_zero, inner_add_right,
          inner_smul_right, hY y hy, zero_add]
  · rw [if_neg ht]
    constructor
    · rintro ⟨⟨_, hc⟩, hslice⟩
      exact ht ((hcoord x hslice) ▸ hc)
    · exact False.elim

/-- Fubini gives the exact base-area times physical-height formula, including
zero-dimensional bases when `d = 1`. -/
theorem orthogonalCylinder_volume (e : Euc d) (he : e ≠ 0) (a b : ℝ)
    {Y : Set (Euc d)} (hYm : MeasurableSet Y)
    (hY : ∀ y ∈ Y, inner ℝ e y = 0) :
    μHE[d] (orthogonalCylinder e a b Y) =
      ‖e‖ₑ * ENNReal.ofReal (b - a) * μHE[d - 1] Y := by
  have hvolume : μHE[d] (orthogonalCylinder e a b Y) = ‖e‖ₑ *
      ∫⁻ t : ℝ, μHE[d - 1]
        (orthogonalCylinder e a b Y ∩ perpendicularSlice 0 e t) := by
    simpa only [finrank_euclideanSpace_fin, perpendicularSlice, vadd_eq_add] using
      EuclideanGeometry.euclideanHausdorffMeasure_eq_lintegral (0 : Euc d) he
        (measurableSet_orthogonalCylinder e a b hYm)
  have hslices : (fun t : ℝ => μHE[d - 1]
      (orthogonalCylinder e a b Y ∩ perpendicularSlice 0 e t)) =
      (Set.Icc a b).indicator (fun _ => μHE[d - 1] Y) := by
    funext t
    rw [orthogonalCylinder_slice e he a b t hY]
    by_cases ht : t ∈ Set.Icc a b
    · rw [if_pos ht, Set.indicator_of_mem ht]
      exact (isometry_add_right (t • e)).euclideanHausdorffMeasure_image Y
    · rw [if_neg ht, Set.indicator_of_notMem ht, measure_empty]
  rw [hvolume, hslices, lintegral_indicator measurableSet_Icc, lintegral_const,
    Measure.restrict_apply_univ, Real.volume_Icc]
  ring

end BouRabeeGwynne
