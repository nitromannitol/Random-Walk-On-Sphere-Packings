module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/CoordinateHyperplane.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.HyperplaneGraph
public import BouRabeeGwynne.PaperObjects
public import BouRabeeGwynne.ProjectedBase
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-! Coordinate versions of the exact affine-hyperplane area and flux formulas. -/

open scoped ENNReal MeasureTheory
open MeasureTheory

namespace BouRabeeGwynne

noncomputable section

variable {n : ℕ}

/-- Reindex Euclidean coordinates so that `i` is the distinguished coordinate. -/
def coordinateChart (i : Fin (n + 1)) :
    Euc (n + 1) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Option (Fin n)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finSuccEquiv' i)

@[simp] lemma coordinateChart_none (i : Fin (n + 1)) (x : Euc (n + 1)) :
    coordinateChart i x none = x i := rfl

@[simp] lemma coordinateChart_some (i : Fin (n + 1)) (x : Euc (n + 1)) (j : Fin n) :
    coordinateChart i x (some j) = x (i.succAbove j) := rfl

/-- Delete coordinate `i`, retaining the Euclidean norm on the remaining coordinates. -/
def coordinateProjection (i : Fin (n + 1)) (x : Euc (n + 1)) : Euc n :=
  horizontalProjection (coordinateChart i x)

@[simp] lemma coordinateProjection_apply (i : Fin (n + 1)) (x : Euc (n + 1)) (j : Fin n) :
    coordinateProjection i x j = x (i.succAbove j) := rfl

/-- Parametrize the affine plane `a·x=c` using every coordinate except `i`. -/
def coordinatePlaneGraph (i : Fin (n + 1)) (a : Euc (n + 1)) (c : ℝ)
    (y : Euc n) : Euc (n + 1) :=
  (coordinateChart i).symm (hyperplaneGraph (coordinateChart i a) c y)

lemma coordinatePlaneGraph_projection (i : Fin (n + 1)) (a : Euc (n + 1)) (c : ℝ)
    (ha : a i ≠ 0) {x : Euc (n + 1)} (hx : inner ℝ a x = c) :
    coordinatePlaneGraph i a c (coordinateProjection i x) = x := by
  unfold coordinatePlaneGraph coordinateProjection
  rw [hyperplaneGraph_horizontalProjection (coordinateChart i a) c ha
    (by rw [(coordinateChart i).inner_map_map]; exact hx)]
  exact (coordinateChart i).symm_apply_apply x

theorem coordinatePlaneGraph_image_projection (i : Fin (n + 1))
    (a : Euc (n + 1)) (c : ℝ) (ha : a i ≠ 0) {s : Set (Euc (n + 1))}
    (hs : s ⊆ {x | inner ℝ a x = c}) :
    coordinatePlaneGraph i a c '' (coordinateProjection i '' s) = s := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa only [coordinatePlaneGraph_projection i a c ha (hs hz)] using hz
  · intro hx
    exact ⟨coordinateProjection i x, ⟨x, hx, rfl⟩,
      coordinatePlaneGraph_projection i a c ha (hs hx)⟩

/-- Signed coordinate-normal surface integral on an arbitrary part of a plane. -/
theorem coordinate_hyperplane_integral_projection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin (n + 1)) (a : Euc (n + 1)) (c : ℝ) (ha : a i ≠ 0)
    {s : Set (Euc (n + 1))} (hs : s ⊆ {x | inner ℝ a x = c}) (f : Euc (n + 1) → E) :
    (∫ x in s, (a i / ‖a‖) • f x ∂μHE[n]) =
      Real.sign (a i) • ∫ y in coordinateProjection i '' s,
        f (coordinatePlaneGraph i a c y) ∂volume := by
  have hplane : coordinateChart i '' s ⊆
      {x | inner ℝ (coordinateChart i a) x = c} := by
    rintro x ⟨y, hy, rfl⟩
    change inner ℝ (coordinateChart i a) (coordinateChart i y) = c
    rw [(coordinateChart i).inner_map_map]
    exact hs hy
  have h := hyperplane_integral_projection (coordinateChart i a) c ha hplane
    (fun x => f ((coordinateChart i).symm x))
  have htransport :=
    (coordinateChart i).toIsometryEquiv.measurePreserving_euclideanHausdorffMeasure n
      |>.setIntegral_image_emb (coordinateChart i).toHomeomorph.measurableEmbedding
        (fun x => ((coordinateChart i a) none / ‖coordinateChart i a‖) •
          f ((coordinateChart i).symm x)) s
  change (∫ x in coordinateChart i '' s,
      ((coordinateChart i a) none / ‖coordinateChart i a‖) •
        f ((coordinateChart i).symm x) ∂μHE[n]) =
    ∫ x in s, ((coordinateChart i a) none / ‖coordinateChart i a‖) •
      f ((coordinateChart i).symm (coordinateChart i x)) ∂μHE[n] at htransport
  rw [Fintype.card_fin, htransport] at h
  change (∫ x in s, (a i / ‖a‖) • f x ∂μHE[n]) =
    Real.sign (a i) • ∫ y in (fun x => horizontalProjection (coordinateChart i x)) '' s,
      f ((coordinateChart i).symm (hyperplaneGraph (coordinateChart i a) c y)) ∂volume
  simpa only [coordinateChart_none, LinearIsometryEquiv.norm_map,
    LinearIsometryEquiv.symm_apply_apply, Set.image_image, coordinateProjection,
    coordinatePlaneGraph] using h

/-- Exact area factor with the chosen coordinate deleted from the projection. -/
theorem coordinate_hyperplane_measure_projection
    (i : Fin (n + 1)) (a : Euc (n + 1)) (c : ℝ) (ha : a i ≠ 0)
    {s : Set (Euc (n + 1))} (hs : s ⊆ {x | inner ℝ a x = c}) :
    μHE[n] s = ENNReal.ofReal (‖a‖ / |a i|) * volume (coordinateProjection i '' s) := by
  have hplane : coordinateChart i '' s ⊆
      {x | inner ℝ (coordinateChart i a) x = c} := by
    rintro x ⟨y, hy, rfl⟩
    change inner ℝ (coordinateChart i a) (coordinateChart i y) = c
    rw [(coordinateChart i).inner_map_map]
    exact hs hy
  have h := hyperplaneGraph_measure_image (coordinateChart i a) c ha
    (horizontalProjection '' (coordinateChart i '' s))
  rw [hyperplaneGraph_image_projection (coordinateChart i a) c ha hplane,
    (coordinateChart i).isometry.euclideanHausdorffMeasure_image] at h
  change μHE[n] s = ENNReal.ofReal (‖a‖ / |a i|) *
    volume ((fun x => horizontalProjection (coordinateChart i x)) '' s)
  simpa only [Fintype.card_fin, LinearIsometryEquiv.norm_map, coordinateChart_none,
    Set.image_image, coordinateProjection] using h

end

end BouRabeeGwynne


open scoped ENNReal MeasureTheory
open MeasureTheory

namespace BouRabeeGwynne

noncomputable section

variable {n : ℕ}

def coordinateAxis (i : Fin (n + 1)) : Euc (n + 1) :=
  EuclideanSpace.basisFun (Fin (n + 1)) ℝ i

@[simp] lemma coordinateAxis_self (i : Fin (n + 1)) : coordinateAxis i i = 1 := by
  simp [coordinateAxis, EuclideanSpace.basisFun_apply, PiLp.single_apply]

@[simp] lemma coordinateAxis_succAbove (i : Fin (n + 1)) (j : Fin n) :
    coordinateAxis i (i.succAbove j) = 0 := by
  simp [coordinateAxis, EuclideanSpace.basisFun_apply, PiLp.single_apply, Fin.succAbove_ne, Fin.ne_succAbove]

@[simp] lemma norm_coordinateAxis (i : Fin (n + 1)) : ‖coordinateAxis i‖ = 1 :=
  (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).norm_eq_one i

lemma coordinateAxis_ne_zero (i : Fin (n + 1)) : coordinateAxis i ≠ 0 := by
  intro h
  have hh := congrArg (fun x : Euc (n + 1) => x i) h
  simpa only [coordinateAxis_self, PiLp.zero_apply, one_ne_zero] using hh

@[simp] lemma inner_coordinateAxis (i : Fin (n + 1)) (x : Euc (n + 1)) :
    inner ℝ (coordinateAxis i) x = x i :=
  EuclideanSpace.basisFun_inner (ι := Fin (n + 1)) (𝕜 := ℝ) x i

@[simp] lemma inner_coordinateAxis_right (i : Fin (n + 1)) (x : Euc (n + 1)) :
    inner ℝ x (coordinateAxis i) = x i :=
  EuclideanSpace.inner_basisFun_real (ι := Fin (n + 1)) x i

lemma continuous_coordinateProjection (i : Fin (n + 1)) :
    Continuous (coordinateProjection i) :=
  (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp
    (continuous_pi fun j => PiLp.continuous_apply 2 _ (i.succAbove j))

lemma coordinateProjection_hyperplaneProjection (i : Fin (n + 1)) (x : Euc (n + 1)) :
    coordinateProjection i (hyperplaneProjection (coordinateAxis i) x) =
      coordinateProjection i x := by
  ext j
  simp only [coordinateProjection_apply, hyperplaneProjection_apply, PiLp.sub_apply,
    PiLp.smul_apply, smul_eq_mul, coordinateAxis_succAbove, mul_zero, sub_zero]

lemma coordinatePlaneGraph_axis_projection (i : Fin (n + 1)) (x : Euc (n + 1)) :
    coordinatePlaneGraph i (coordinateAxis i) 0 (coordinateProjection i x) =
      hyperplaneProjection (coordinateAxis i) x := by
  have h := coordinatePlaneGraph_projection i (coordinateAxis i) 0
    (by rw [coordinateAxis_self]; exact one_ne_zero)
    (inner_hyperplaneProjection (coordinateAxis_ne_zero i) x)
  simpa only [coordinateProjection_hyperplaneProjection] using h

theorem coordinate_perpendicular_measure_projection (i : Fin (n + 1))
    {s : Set (Euc (n + 1))} (hs : s ⊆ {x | inner ℝ (coordinateAxis i) x = 0}) :
    μHE[n] s = volume (coordinateProjection i '' s) := by
  simpa only [norm_coordinateAxis, coordinateAxis_self, abs_one, div_one,
    ENNReal.ofReal_one, one_mul] using
    coordinate_hyperplane_measure_projection i (coordinateAxis i) 0
      (by rw [coordinateAxis_self]; exact one_ne_zero) hs

theorem coordinate_perpendicular_integral_projection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin (n + 1)) {s : Set (Euc (n + 1))}
    (hs : s ⊆ {x | inner ℝ (coordinateAxis i) x = 0}) (f : Euc (n + 1) → E) :
    (∫ x in s, f x ∂μHE[n]) =
      ∫ y in coordinateProjection i '' s,
        f (coordinatePlaneGraph i (coordinateAxis i) 0 y) ∂volume := by
  simpa only [norm_coordinateAxis, coordinateAxis_self, div_one, one_smul,
    Real.sign_one] using
    coordinate_hyperplane_integral_projection i (coordinateAxis i) 0
      (by rw [coordinateAxis_self]; exact one_ne_zero) hs f

namespace ConvexPolytope

variable (P : ConvexPolytope (n + 1))

lemma projectedBase_coordinate_measure_ne_top (i : Fin (n + 1)) :
    μHE[n] (P.projectedBase (coordinateAxis i) (coordinateAxis_ne_zero i)) ≠ ⊤ := by
  rw [coordinate_perpendicular_measure_projection i (fun _ hx => hx.1)]
  exact ((P.isCompact_projectedBase (coordinateAxis_ne_zero i)).image
    (continuous_coordinateProjection i)).measure_ne_top

end ConvexPolytope
end
end BouRabeeGwynne
