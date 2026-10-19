-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/HyperplaneGraph.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.GraphMeasure
import Mathlib.Basic.Real.Sign
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

open scoped BigOperators ENNReal MeasureTheory
open MeasureTheory

namespace BouRabeeGwynne

noncomputable section

variable {ι : Type*}

/-- Delete the distinguished coordinate of a Euclidean vector. -/
def horizontalProjection (x : EuclideanSpace ℝ (Option ι)) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => x (some i))

@[simp] lemma horizontalProjection_apply (x : EuclideanSpace ℝ (Option ι)) (i : ι) :
    horizontalProjection x i = x (some i) := rfl

/-- The slope of a hyperplane whose distinguished normal coordinate is nonzero. -/
def hyperplaneSlope (a : EuclideanSpace ℝ (Option ι)) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => -a (some i) / a none)

@[simp] lemma hyperplaneSlope_apply (a : EuclideanSpace ℝ (Option ι)) (i : ι) :
    hyperplaneSlope a i = -a (some i) / a none := rfl

/-- The vertical intercept of the plane `inner a x = c`. -/
def hyperplaneIntercept (a : EuclideanSpace ℝ (Option ι)) (c : ℝ) :
    EuclideanSpace ℝ (Option ι) :=
  WithLp.toLp 2 (fun i => Option.casesOn i (c / a none) (fun _ => 0))

@[simp] lemma hyperplaneIntercept_none (a : EuclideanSpace ℝ (Option ι)) (c : ℝ) :
    hyperplaneIntercept a c none = c / a none := rfl

@[simp] lemma hyperplaneIntercept_some (a : EuclideanSpace ℝ (Option ι)) (c : ℝ) (i : ι) :
    hyperplaneIntercept a c (some i) = 0 := rfl

variable [Fintype ι]

/-- The affine graph parametrization of the hyperplane with normal `a` and offset `c`. -/
def hyperplaneGraph (a : EuclideanSpace ℝ (Option ι)) (c : ℝ) :
    EuclideanSpace ℝ ι → EuclideanSpace ℝ (Option ι) :=
  affineGraph (hyperplaneSlope a) (hyperplaneIntercept a c)

@[simp] lemma hyperplaneGraph_apply_some (a : EuclideanSpace ℝ (Option ι)) (c : ℝ)
    (q : EuclideanSpace ℝ ι) (i : ι) : hyperplaneGraph a c q (some i) = q i := by
  simp [hyperplaneGraph, affineGraph]

lemma inner_hyperplaneSlope (a : EuclideanSpace ℝ (Option ι)) (q : EuclideanSpace ℝ ι) :
    inner ℝ (hyperplaneSlope a) q = -(∑ i, a (some i) * q i) / a none := by
  simp only [PiLp.inner_apply, Real.inner_apply, hyperplaneSlope_apply]
  calc
    (∑ i, (-a (some i) / a none) * q i) =
        ∑ i, -(a (some i) * q i) / a none := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [← Finset.sum_div, Finset.sum_neg_distrib]

lemma hyperplaneGraph_apply_none (a : EuclideanSpace ℝ (Option ι)) (c : ℝ)
    (q : EuclideanSpace ℝ ι) :
    hyperplaneGraph a c q none = (c - ∑ i, a (some i) * q i) / a none := by
  change inner ℝ (hyperplaneSlope a) q + c / a none = _
  rw [inner_hyperplaneSlope]
  ring

@[simp] theorem horizontalProjection_hyperplaneGraph (a : EuclideanSpace ℝ (Option ι))
    (c : ℝ) (q : EuclideanSpace ℝ ι) :
    horizontalProjection (hyperplaneGraph a c q) = q := by
  ext i
  simp

/-- Every graph point satisfies the actual affine hyperplane equation. -/
theorem inner_hyperplaneGraph (a : EuclideanSpace ℝ (Option ι)) (c : ℝ)
    (ha : a none ≠ 0) (q : EuclideanSpace ℝ ι) :
    inner ℝ a (hyperplaneGraph a c q) = c := by
  simp only [PiLp.inner_apply, Fintype.sum_option, Real.inner_apply,
    hyperplaneGraph_apply_none, hyperplaneGraph_apply_some]
  field_simp
  ring

/-- Projection and graph parametrization are inverses on the entire hyperplane. -/
theorem hyperplaneGraph_horizontalProjection (a : EuclideanSpace ℝ (Option ι)) (c : ℝ)
    (ha : a none ≠ 0) {x : EuclideanSpace ℝ (Option ι)} (hx : inner ℝ a x = c) :
    hyperplaneGraph a c (horizontalProjection x) = x := by
  ext i
  cases i with
  | none =>
      rw [hyperplaneGraph_apply_none]
      simp only [horizontalProjection_apply]
      apply (div_eq_iff ha).mpr
      simp only [PiLp.inner_apply, Fintype.sum_option, Real.inner_apply] at hx
      linarith
  | some i => simp

theorem range_hyperplaneGraph (a : EuclideanSpace ℝ (Option ι)) (c : ℝ)
    (ha : a none ≠ 0) :
    Set.range (hyperplaneGraph a c) = {x | inner ℝ a x = c} := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    exact inner_hyperplaneGraph a c ha q
  · intro hx
    exact ⟨horizontalProjection x, hyperplaneGraph_horizontalProjection a c ha hx⟩

/-- An arbitrary projected set parametrizes exactly the corresponding part of the plane. -/
theorem hyperplaneGraph_image (a : EuclideanSpace ℝ (Option ι)) (c : ℝ)
    (ha : a none ≠ 0) (s : Set (EuclideanSpace ℝ ι)) :
    hyperplaneGraph a c '' s =
      {x | inner ℝ a x = c ∧ horizontalProjection x ∈ s} := by
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨inner_hyperplaneGraph a c ha q, by simpa using hq⟩
  · rintro ⟨hx, hs⟩
    exact ⟨horizontalProjection x, hs, hyperplaneGraph_horizontalProjection a c ha hx⟩

theorem hyperplaneGraph_image_projection (a : EuclideanSpace ℝ (Option ι)) (c : ℝ)
    (ha : a none ≠ 0) {s : Set (EuclideanSpace ℝ (Option ι))}
    (hs : s ⊆ {x | inner ℝ a x = c}) :
    hyperplaneGraph a c '' (horizontalProjection '' s) = s := by
  ext x
  constructor
  · rintro ⟨q, ⟨y, hy, rfl⟩, rfl⟩
    simpa only [hyperplaneGraph_horizontalProjection a c ha (hs hy)] using hy
  · intro hx
    exact ⟨horizontalProjection x, ⟨x, hx, rfl⟩,
      hyperplaneGraph_horizontalProjection a c ha (hs hx)⟩

lemma norm_sq_option (a : EuclideanSpace ℝ (Option ι)) :
    ‖a‖ ^ 2 = (a none) ^ 2 + ∑ i, (a (some i)) ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fintype.sum_option]

lemma hyperplaneSlope_norm_sq (a : EuclideanSpace ℝ (Option ι)) :
    ‖hyperplaneSlope a‖ ^ 2 = (∑ i, (a (some i)) ^ 2) / (a none) ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, hyperplaneSlope_apply, div_pow, neg_sq,
    ← Finset.sum_div]

/-- The normalized graph area factor in terms of the actual normal vector.
No nonemptiness hypothesis on the horizontal coordinate type is used. -/
theorem hyperplaneGraph_areaFactor (a : EuclideanSpace ℝ (Option ι)) (ha : a none ≠ 0) :
    Real.sqrt (1 + ‖hyperplaneSlope a‖ ^ 2) = ‖a‖ / |a none| := by
  have hsq : 1 + ‖hyperplaneSlope a‖ ^ 2 = ‖a‖ ^ 2 / (a none) ^ 2 := by
    rw [hyperplaneSlope_norm_sq, norm_sq_option]
    field_simp <;> ring
  rw [hsq, Real.sqrt_div (sq_nonneg _) _, Real.sqrt_sq (norm_nonneg a),
    Real.sqrt_sq_eq_abs]

theorem hyperplaneGraph_measure_image (a : EuclideanSpace ℝ (Option ι)) (c : ℝ)
    (ha : a none ≠ 0) (s : Set (EuclideanSpace ℝ ι)) :
    μHE[Fintype.card ι] (hyperplaneGraph a c '' s) =
      ENNReal.ofReal (‖a‖ / |a none|) * volume s := by
  change μHE[Fintype.card ι]
    (affineGraph (hyperplaneSlope a) (hyperplaneIntercept a c) '' s) = _
  rw [affineGraph_measure_image, hyperplaneGraph_areaFactor a ha]

theorem hyperplaneGraph_integral_image {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : EuclideanSpace ℝ (Option ι)) (c : ℝ) (ha : a none ≠ 0)
    (s : Set (EuclideanSpace ℝ ι)) (f : EuclideanSpace ℝ (Option ι) → E) :
    (∫ x in hyperplaneGraph a c '' s, f x ∂μHE[Fintype.card ι]) =
      (‖a‖ / |a none|) • ∫ q in s, f (hyperplaneGraph a c q) ∂volume := by
  exact (affineGraph_integral_image (hyperplaneSlope a) (hyperplaneIntercept a c) s f).trans
    (by rw [hyperplaneGraph_areaFactor a ha]; rfl)

lemma normal_coordinate_areaFactor (a : EuclideanSpace ℝ (Option ι)) (ha : a none ≠ 0) :
    (a none / ‖a‖) * (‖a‖ / |a none|) = Real.sign (a none) := by
  have hane : a ≠ 0 := by
    intro h
    exact ha (congrArg (fun x : EuclideanSpace ℝ (Option ι) => x none) h)
  have hn : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr hane
  rcases ha.lt_or_gt with hneg | hpos
  · rw [Real.sign_of_neg hneg, abs_of_neg hneg]
    field_simp <;> ring
  · rw [Real.sign_of_pos hpos, abs_of_pos hpos]
    field_simp

/-- The signed distinguished-coordinate flux of the unit normal. This exact
identity holds for arbitrary subsets and Bochner-integral functions. -/
theorem hyperplaneGraph_signed_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : EuclideanSpace ℝ (Option ι)) (c : ℝ) (ha : a none ≠ 0)
    (s : Set (EuclideanSpace ℝ ι)) (f : EuclideanSpace ℝ (Option ι) → E) :
    (∫ x in hyperplaneGraph a c '' s, (a none / ‖a‖) • f x ∂μHE[Fintype.card ι]) =
      Real.sign (a none) • ∫ q in s, f (hyperplaneGraph a c q) ∂volume := by
  rw [integral_smul, hyperplaneGraph_integral_image a c ha,
    smul_smul, normal_coordinate_areaFactor a ha]

/-- Signed flux written directly on any subset of the hyperplane. -/
theorem hyperplane_integral_projection {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : EuclideanSpace ℝ (Option ι)) (c : ℝ) (ha : a none ≠ 0)
    {s : Set (EuclideanSpace ℝ (Option ι))} (hs : s ⊆ {x | inner ℝ a x = c})
    (f : EuclideanSpace ℝ (Option ι) → E) :
    (∫ x in s, (a none / ‖a‖) • f x ∂μHE[Fintype.card ι]) =
      Real.sign (a none) •
        ∫ q in horizontalProjection '' s, f (hyperplaneGraph a c q) ∂volume := by
  calc
    _ = ∫ x in hyperplaneGraph a c '' (horizontalProjection '' s),
        (a none / ‖a‖) • f x ∂μHE[Fintype.card ι] := by
      rw [hyperplaneGraph_image_projection a c ha hs]
    _ = _ := hyperplaneGraph_signed_integral a c ha _ f

end

end BouRabeeGwynne
