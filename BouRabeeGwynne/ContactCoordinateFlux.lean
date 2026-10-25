module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/ContactCoordinateFlux.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.CoordinateHyperplane
public import BouRabeeGwynne.FacetProjection
public import BouRabeeGwynne.FacetMeasure

@[expose] public section

open scoped ENNReal MeasureTheory
open MeasureTheory

namespace BouRabeeGwynne

noncomputable section

variable {n : ℕ}

/-- Coordinate flux transport onto the actual perpendicular hyperplane. -/
theorem coordinate_hyperplane_integral_perpendicular_projection
    (i : Fin (n + 1)) (a : Euc (n + 1)) (c : ℝ) (ha : a i ≠ 0)
    {s : Set (Euc (n + 1))} (hs : s ⊆ {x | inner ℝ a x = c})
    (f : Euc (n + 1) → ℝ) :
    (∫ x in s, (a i / ‖a‖) * f x ∂μHE[n]) =
      Real.sign (a i) * ∫ y in hyperplaneProjection (coordinateAxis i) '' s,
        f (coordinatePlaneGraph i a c (coordinateProjection i y)) ∂μHE[n] := by
  have hproj : coordinateProjection i '' (hyperplaneProjection (coordinateAxis i) '' s) =
      coordinateProjection i '' s := by
    rw [Set.image_image]
    congr 1
    funext x
    exact coordinateProjection_hyperplaneProjection i x
  have htrans := coordinate_perpendicular_integral_projection i
    (s := hyperplaneProjection (coordinateAxis i) '' s)
    (by rintro y ⟨x, hx, rfl⟩; exact inner_hyperplaneProjection (coordinateAxis_ne_zero i) x)
    (fun y => f (coordinatePlaneGraph i a c (coordinateProjection i y)))
  rw [hproj] at htrans
  have hfun : (fun y : Euc n => f (coordinatePlaneGraph i a c
      (coordinateProjection i (coordinatePlaneGraph i (coordinateAxis i) 0 y)))) =
      (fun y => f (coordinatePlaneGraph i a c y)) := by
    funext y
    unfold coordinateProjection coordinatePlaneGraph
    rw [LinearIsometryEquiv.apply_symm_apply, horizontalProjection_hyperplaneGraph]
  rw [hfun] at htrans
  rw [htrans]
  simpa only [smul_eq_mul] using coordinate_hyperplane_integral_projection i a c ha hs f

namespace OrthogonalTiling

variable (T : OrthogonalTiling (n + 1))

lemma facet_subset_normal_plane {v w : T.V} (hvw : T.adj v w)
    {x : Euc (n + 1)} (hx : x ∈ T.facet v w) :
    T.facet v w ⊆ {y | inner ℝ (T.pos w - T.pos v) y = inner ℝ (T.pos w - T.pos v) x} := by
  intro y hy
  exact sub_eq_zero.mp (by simpa only [inner_sub_right] using T.orthogonal hvw hy hx)

/-- Positive contact flux is integration over its exact upper-endpoint projection. -/
theorem integral_upper_contact_eq_projection (i : Fin (n + 1))
    {v w : T.V} (hvw : T.adj v w) (hn : 0 < (T.pos w - T.pos v) i)
    (f : Euc (n + 1) → ℝ) :
    (∫ x in T.facet v w, ((T.pos w - T.pos v) i / ‖T.pos w - T.pos v‖) * f x ∂μHE[n]) =
      ∫ y in hyperplaneProjection (coordinateAxis i) '' T.facet v w,
        f ((T.cell v).upperEndpoint (coordinateAxis i) (coordinateAxis_ne_zero i) y) ∂μHE[n] := by
  obtain ⟨x, hx⟩ := hvw.2.1
  rw [coordinate_hyperplane_integral_perpendicular_projection i (T.pos w - T.pos v)
    (inner ℝ (T.pos w - T.pos v) x) hn.ne' (T.facet_subset_normal_plane hvw hx) f,
    Real.sign_of_pos hn, one_mul]
  have hK : IsCompact (hyperplaneProjection (coordinateAxis i) '' T.facet v w) :=
    (T.toTilingData.facet_compact v w).image (hyperplaneProjection (coordinateAxis i)).continuous
  apply setIntegral_congr_fun hK.measurableSet
  rintro y ⟨z, hz, rfl⟩
  dsimp only
  rw [coordinateProjection_hyperplaneProjection,
    coordinatePlaneGraph_projection i (T.pos w - T.pos v)
      (inner ℝ (T.pos w - T.pos v) x) hn.ne' (T.facet_subset_normal_plane hvw hx hz),
    T.upperEndpoint_projection_of_mem_facet (by omega) (coordinateAxis_ne_zero i) hvw
      (by simpa only [inner_coordinateAxis_right] using hn) hz]

/-- Negative contact flux is minus integration over the lower-endpoint projection. -/
theorem integral_lower_contact_eq_projection (i : Fin (n + 1))
    {v w : T.V} (hvw : T.adj v w) (hn : (T.pos w - T.pos v) i < 0)
    (f : Euc (n + 1) → ℝ) :
    (∫ x in T.facet v w, ((T.pos w - T.pos v) i / ‖T.pos w - T.pos v‖) * f x ∂μHE[n]) =
      -(∫ y in hyperplaneProjection (coordinateAxis i) '' T.facet v w,
        f ((T.cell v).lowerEndpoint (coordinateAxis i) (coordinateAxis_ne_zero i) y) ∂μHE[n]) := by
  obtain ⟨x, hx⟩ := hvw.2.1
  rw [coordinate_hyperplane_integral_perpendicular_projection i (T.pos w - T.pos v)
    (inner ℝ (T.pos w - T.pos v) x) hn.ne (T.facet_subset_normal_plane hvw hx) f,
    Real.sign_of_neg hn, neg_one_mul]
  congr 1
  have hK : IsCompact (hyperplaneProjection (coordinateAxis i) '' T.facet v w) :=
    (T.toTilingData.facet_compact v w).image (hyperplaneProjection (coordinateAxis i)).continuous
  apply setIntegral_congr_fun hK.measurableSet
  rintro y ⟨z, hz, rfl⟩
  dsimp only
  rw [coordinateProjection_hyperplaneProjection,
    coordinatePlaneGraph_projection i (T.pos w - T.pos v)
      (inner ℝ (T.pos w - T.pos v) x) hn.ne (T.facet_subset_normal_plane hvw hx hz),
    T.lowerEndpoint_projection_of_mem_facet (by omega) (coordinateAxis_ne_zero i) hvw
      (by simpa only [inner_coordinateAxis_right] using hn) hz]

end OrthogonalTiling
end
end BouRabeeGwynne
