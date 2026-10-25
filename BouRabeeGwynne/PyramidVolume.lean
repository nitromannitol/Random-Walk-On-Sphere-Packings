module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/PyramidVolume.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.PyramidSlices
public import BouRabeeGwynne.ConeIntegrals

@[expose] public section

open scoped ENNReal MeasureTheory
open MeasureTheory

namespace BouRabeeGwynne

/-- Exact pyramid volume from actual perpendicular sections and homothety. -/
theorem pyramid_volume {d : ℕ} (hd : 1 ≤ d) (a : Euc d) {e : Euc d}
    (he : e ≠ 0) {s : Set (Euc d)} (hs : IsCompact s) (hconv : Convex ℝ s)
    (hne : s.Nonempty) {r : ℝ} (hr : 0 < r)
    (hbase : s ⊆ perpendicularSlice a e r) :
    μHE[d] (convexHull ℝ (insert a s)) =
      ‖e‖ₑ * ENNReal.ofReal (r / (d : ℝ)) * μHE[d - 1] s := by
  let C := convexHull ℝ (insert a s)
  have hC : IsCompact C := isCompact_convexHull_insert_of_convex a hs hconv
  have hvolume : μHE[d] C = ‖e‖ₑ *
      ∫⁻ t : ℝ, μHE[d - 1] (C ∩ perpendicularSlice a e t) := by
    simpa only [finrank_euclideanSpace_fin, perpendicularSlice, vadd_eq_add] using
      EuclideanGeometry.euclideanHausdorffMeasure_eq_lintegral a he hC.isClosed.measurableSet
  have hsection :
      (fun t : ℝ => μHE[d - 1] (C ∩ perpendicularSlice a e t)) =ᵐ[volume]
      (Set.Icc (0 : ℝ) r).indicator
        (fun t : ℝ => (‖t / r‖₊ : ℝ≥0∞) ^ (d - 1) * μHE[d - 1] s) := by
    filter_upwards [volume.ae_ne (0 : ℝ)] with t ht0
    by_cases ht : t ∈ Set.Icc (0 : ℝ) r
    · rw [Set.indicator_of_mem ht]
      have h := pyramid_slice_measure a he hconv hne hr hbase ht ht0 (d - 1)
      simpa only [C, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_pow] using h
    · rw [Set.indicator_of_notMem ht]
      change μHE[d - 1] (convexHull ℝ (insert a s) ∩ perpendicularSlice a e t) = 0
      rw [pyramid_slice_eq_empty a he hconv hne hr hbase ht, measure_empty]
  have hm : Measurable (fun t : ℝ => (‖t / r‖₊ : ℝ≥0∞) ^ (d - 1)) := by fun_prop
  rw [hvolume, lintegral_congr_ae hsection, lintegral_indicator measurableSet_Icc,
    lintegral_mul_const _ hm, lintegral_nnnorm_scaled_pow_Icc hr (d - 1)]
  have hdim : ((d - 1 : ℕ) : ℝ) + 1 = d := by exact_mod_cast Nat.sub_add_cancel hd
  rw [hdim, mul_assoc]

end BouRabeeGwynne
