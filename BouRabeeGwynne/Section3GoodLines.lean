-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/Section3GoodLines.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.Section3Projection

/-! Good scalar line parameters from a strict surface-measure margin. -/

open scoped ENNReal MeasureTheory
open MeasureTheory

namespace BouRabeeGwynne

variable {d : ℕ}

lemma unitLine_isometry {u : Euc d} (hu : ‖u‖ = 1) :
    Isometry (fun t : ℝ => t • u) := by
  apply Isometry.of_dist_eq
  intro s t
  rw [dist_eq_norm, ← sub_smul, norm_smul, hu, mul_one, dist_eq_norm]

lemma unitLine_interval_measure {u : Euc d} (hu : ‖u‖ = 1) (a b : ℝ) :
    μHE[1] ((fun t : ℝ => t • u) '' Set.Ioo a b) = ENNReal.ofReal (b - a) := by
  rw [(unitLine_isometry hu).euclideanHausdorffMeasure_image]
  have hreal : (μHE[1] : Measure ℝ) = volume := by
    simpa using (InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := ℝ))
  rw [hreal, Real.volume_Ioo]

/-- Any scalar interval longer than a bad base's total measure contains a good
line parameter. The strict length margin avoids an endpoint-attainment assumption. -/
theorem exists_unitLine_parameter_outside {u : Euc d} (hu : ‖u‖ = 1)
    (Y : Set (Euc d)) {a b : ℝ}
    (hY : μHE[1] Y < ENNReal.ofReal (b - a)) :
    ∃ t ∈ Set.Ioo a b, t • u ∉ Y := by
  have hnot : ¬ (fun t : ℝ => t • u) '' Set.Ioo a b ⊆ Y := by
    intro hsub
    have hle := measure_mono hsub (μ := μHE[1])
    rw [unitLine_interval_measure hu a b] at hle
    exact (not_lt_of_ge hle) hY
  obtain ⟨y, ⟨t, ht, rfl⟩, hy⟩ := Set.not_subset.mp hnot
  exact ⟨t, ht, hy⟩

theorem exists_unitLine_parameter_outside_of_bound {u : Euc d} (hu : ‖u‖ = 1)
    (Y : Set (Euc d)) {a b ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hY : μHE[1] Y ≤ ENNReal.ofReal ℓ) (hgap : ℓ < b - a) :
    ∃ t ∈ Set.Ioo a b, t • u ∉ Y :=
  exists_unitLine_parameter_outside hu Y
    (hY.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (hℓ.trans_lt hgap)).mpr hgap))

end BouRabeeGwynne
