-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/Section3Projection.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.ProjectedBase
import BouRabeeGwynne.FacetMeasure

/-!
# Section 3: projection estimates for column integrals

The actual orthogonal projection is a contraction. Consequently it does not
increase normalized Hausdorff measure, so every projected facet has finite
measure bounded by the original contact area.
-/

open scoped MeasureTheory ENNReal
open MeasureTheory

namespace BouRabeeGwynne

lemma hyperplaneProjection_norm_le {d : ℕ} (e x : Euc d) :
    ‖hyperplaneProjection e x‖ ≤ ‖x‖ := by
  by_cases he : e = 0
  · simp [hyperplaneProjection_apply, he]
  · let z := (inner ℝ e x / inner ℝ e e) • e
    have hperp : inner ℝ (hyperplaneProjection e x) e = 0 := by
      rw [real_inner_comm]
      exact inner_hyperplaneProjection he x
    have hpz : inner ℝ (hyperplaneProjection e x) z = 0 := by
      dsimp [z]
      rw [inner_smul_right, hperp, mul_zero]
    have hdecomp : hyperplaneProjection e x + z = x := by
      change hyperplaneProjection e x + (inner ℝ e x / inner ℝ e e) • e = x
      rw [hyperplaneProjection_apply, sub_add_cancel]
    have hnorm := norm_add_sq_real (hyperplaneProjection e x) z
    rw [hpz, mul_zero, add_zero, hdecomp] at hnorm
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    nlinarith [sq_nonneg ‖z‖]

lemma hyperplaneProjection_lipschitz {d : ℕ} (e : Euc d) :
    LipschitzWith 1 (hyperplaneProjection e) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [map_sub, NNReal.coe_one, one_mul, dist_eq_norm] using
    hyperplaneProjection_norm_le e (x - y)

lemma lipschitzOne_euclideanHausdorffMeasure_image_le {d k : ℕ}
    {P : Euc d → Euc d} (hP : LipschitzWith 1 P) (s : Set (Euc d)) :
    μHE[k] (P '' s) ≤ μHE[k] s := by
  have hH : μH[(k : ℝ)] (P '' s) ≤ μH[(k : ℝ)] s := by
    simpa using hP.hausdorffMeasure_image_le (d := (k : ℝ)) (Nat.cast_nonneg k) s
  simp only [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply]
  exact smul_le_smul_left _ hH

namespace OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

lemma projected_facet_measure_le (e : Euc d) (v w : T.V) :
    μHE[d - 1] (hyperplaneProjection e '' T.facet v w) ≤ T.facetVolume v w :=
  lipschitzOne_euclideanHausdorffMeasure_image_le (hyperplaneProjection_lipschitz e) _

lemma projected_facet_compact (e : Euc d) (v w : T.V) :
    IsCompact (hyperplaneProjection e '' T.facet v w) :=
  (T.toTilingData.facet_compact v w).image (hyperplaneProjection e).continuous

lemma projected_facet_measure_ne_top (e : Euc d) {v w : T.V} (hvw : T.adj v w) :
    μHE[d - 1] (hyperplaneProjection e '' T.facet v w) ≠ ⊤ :=
  ne_top_of_le_ne_top (T.toTilingData.facetVolume_ne_top hvw)
    (T.projected_facet_measure_le e v w)

end OrthogonalTiling
end BouRabeeGwynne
