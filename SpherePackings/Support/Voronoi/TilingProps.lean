import SpherePackings.Support.Voronoi.Tiling
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Mesh, tile volume and nearest vertices of Voronoi tilings
-/

open Metric MeasureTheory
open scoped ENNReal

namespace SpherePackings.Voronoi

open BouRabeeGwynne

variable {d : ℕ} {S D : Set (Euc d)} {r R : ℝ}

/-- Every tile has diameter at most `2R`. -/
theorem voronoiTiling_mesh_le (h : GoodVoronoi S D r R) :
    (voronoiTiling S D h).mesh ≤ ENNReal.ofReal (2 * R) := by
  refine iSup_le fun v => ?_
  have hsub : ((voronoiTiling S D h).cell v).carrier ⊆
      closedBall ((voronoiTiling S D h).pos v) R := by
    rw [voronoiTiling_cell]
    exact h.outer _ (voronoiTiling_pos S D h v)
  rw [ConvexPolytope.diamENN]
  exact ENNReal.ofReal_le_ofReal
    ((diam_mono hsub isBounded_closedBall).trans (diam_closedBall h.R_pos.le))

/-- Every tile has volume at least that of the ball of radius `r`. -/
theorem volume_ball_le_minTileVolume (h : GoodVoronoi S D r R) :
    volume (ball (0 : Euc d) r) ≤ (voronoiTiling S D h).minTileVolume := by
  refine le_iInf fun v => ?_
  have hin : closedBall ((voronoiTiling S D h).pos v) r ⊆
      ((voronoiTiling S D h).cell v).carrier := by
    rw [voronoiTiling_cell]
    exact h.inner _ (voronoiTiling_pos S D h v)
  have hball : volume (ball (0 : Euc d) r) = volume (ball ((voronoiTiling S D h).pos v) r) :=
    (Measure.addHaar_ball_center volume _ r).symm
  rw [ConvexPolytope.volume, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hball]
  exact measure_mono (ball_subset_closedBall.trans hin)

/-- A point of `D` lies within `R` of the position of a vertex whose cell contains it. -/
theorem exists_vertex_dist_le (h : GoodVoronoi S D r R) {z : Euc d} (hz : z ∈ D) :
    ∃ v : (voronoiTiling S D h).V, dist z ((voronoiTiling S D h).pos v) ≤ R := by
  obtain ⟨s, hs, hzs⟩ := h.cover z hz
  have hact : s ∈ activePoints S D := ⟨hs, z, hzs, hz⟩
  obtain ⟨v, hv⟩ := voronoiTiling_pos_surjective S D h hact
  exact ⟨v, by rw [hv]; exact mem_closedBall.1 (h.outer s hact hzs)⟩

/-- Every point of `D` has a nearest vertex. -/
theorem exists_nearest_vertex (h : GoodVoronoi S D r R) {z : Euc d} (hz : z ∈ D) :
    ∃ v : (voronoiTiling S D h).V, ∀ w : (voronoiTiling S D h).V,
      dist z ((voronoiTiling S D h).pos v) ≤ dist z ((voronoiTiling S D h).pos w) := by
  obtain ⟨v₀, hv₀⟩ := exists_vertex_dist_le h hz
  -- the vertices within `R` of `z` have positions in the finite set `S ∩ cthickening (6 R) D`
  have hfin : {w : (voronoiTiling S D h).V | dist z ((voronoiTiling S D h).pos w) ≤ R}.Finite := by
    refine (h.finite.preimage Subtype.val_injective.injOn).subset fun w hw => ?_
    have hw' : dist z w.1 ≤ R := hw
    exact ⟨w.2.1, mem_cthickening_of_dist_le w.1 z (6 * R) D hz
      (by rw [dist_comm]; linarith [h.R_pos])⟩
  obtain ⟨v, hvR, hmin⟩ := Set.exists_min_image _
    (fun w => dist z ((voronoiTiling S D h).pos w)) hfin ⟨v₀, hv₀⟩
  have hvR' : dist z ((voronoiTiling S D h).pos v) ≤ R := hvR
  refine ⟨v, fun w => ?_⟩
  by_cases hw : dist z ((voronoiTiling S D h).pos w) ≤ R
  · exact hmin w hw
  · exact hvR'.trans (not_le.1 hw).le

end SpherePackings.Voronoi
