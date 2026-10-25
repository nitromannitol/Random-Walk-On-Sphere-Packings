module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/GraphMeasure.lean` at commit cf73d6e); unchanged apart from this header.
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic.Ring

@[expose] public section

open scoped BigOperators ENNReal MeasureTheory
open MeasureTheory

namespace BouRabeeGwynne

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The linear graph of the scalar functional represented by `b`.
The new coordinate is `none`; the original coordinates are `some i`. -/
def graphLinear (b : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Option ι) where
  toFun x := WithLp.toLp 2 (fun i => Option.casesOn i (inner ℝ b x) (fun j => x j))
  map_add' x y := by
    ext i
    cases i <;> simp [inner_add_right]
  map_smul' c x := by
    ext i
    cases i <;> simp [inner_smul_right]

@[simp]
lemma graphLinear_apply_none (b x : EuclideanSpace ℝ ι) :
    graphLinear b x none = inner ℝ b x := rfl

@[simp]
lemma graphLinear_apply_some (b x : EuclideanSpace ℝ ι) (i : ι) :
    graphLinear b x (some i) = x i := rfl

lemma graphLinear_injective (b : EuclideanSpace ℝ ι) :
    Function.Injective (graphLinear b) := by
  intro x y h
  ext i
  exact congrArg (fun z : EuclideanSpace ℝ (Option ι) => z (some i)) h

lemma inner_graphLinear (b x y : EuclideanSpace ℝ ι) :
    inner ℝ (graphLinear b x) (graphLinear b y) =
      inner ℝ x y + inner ℝ b x * inner ℝ b y := by
  simp only [PiLp.inner_apply, Fintype.sum_option,
    graphLinear_apply_none, graphLinear_apply_some, Real.inner_apply]
  ring

lemma graphLinear_gram (b : EuclideanSpace ℝ ι) [DecidableEq ι] :
    Matrix.gram ℝ (fun i => graphLinear b (EuclideanSpace.basisFun ι ℝ i)) =
      1 + Matrix.replicateCol Unit (fun i => b i) *
        Matrix.replicateRow Unit (fun i => b i) := by
  ext i j
  rw [Matrix.gram_apply, inner_graphLinear]
  simp only [EuclideanSpace.inner_basisFun_real]
  simp [Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply,
    Matrix.replicateCol, Matrix.replicateRow, EuclideanSpace.basisFun_apply,
    PiLp.single_apply, eq_comm]

/-- The graph area factor, valid also for a zero-dimensional domain. -/
theorem graphLinear_normDet (b : EuclideanSpace ℝ ι) :
    (graphLinear b).normDet = Real.sqrt (1 + ‖b‖ ^ 2) := by
  classical
  have hsq := (graphLinear b).normDet_sq_eq_det_gram (EuclideanSpace.basisFun ι ℝ)
  change (graphLinear b).normDet ^ 2 = _ at hsq
  rw [graphLinear_gram, Matrix.det_one_add_replicateCol_mul_replicateRow] at hsq
  have hnorm : (fun i => b i) ⬝ᵥ (fun i => b i) = ‖b‖ ^ 2 := by
    simp only [dotProduct, ← pow_two, EuclideanSpace.real_norm_sq_eq]
  rw [hnorm] at hsq
  rw [← hsq, Real.sqrt_sq (graphLinear b).normDet_nonneg]

/-- In dimension one the graph domain is a point and its area factor is one. -/
lemma graphLinear_normDet_of_isEmpty [IsEmpty ι] (b : EuclideanSpace ℝ ι) :
    (graphLinear b).normDet = 1 := by
  have hb : b = 0 := Subsingleton.elim _ _
  simp [graphLinear_normDet, hb]

/-- Exact normalized Hausdorff area of a linear scalar graph. -/
theorem graphLinear_measure_image (b : EuclideanSpace ℝ ι)
    (s : Set (EuclideanSpace ℝ ι)) :
    μHE[Fintype.card ι] (graphLinear b '' s) =
      ENNReal.ofReal (Real.sqrt (1 + ‖b‖ ^ 2)) * volume s := by
  simpa only [finrank_euclideanSpace, graphLinear_normDet] using
    (graphLinear b).euclideanHausdorffMeasure_image_eq_normDet_mul_volume s

/-- A translated scalar graph, allowing an arbitrary affine graph plane. -/
def affineGraph (b : EuclideanSpace ℝ ι) (c : EuclideanSpace ℝ (Option ι))
    (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ (Option ι) :=
  graphLinear b x + c

lemma affineGraph_isClosedEmbedding (b : EuclideanSpace ℝ ι)
    (c : EuclideanSpace ℝ (Option ι)) : Topology.IsClosedEmbedding (affineGraph b c) := by
  exact (IsometryEquiv.addRight c).toHomeomorph.isClosedEmbedding.comp
    (LinearMap.isClosedEmbedding_of_injective
      (LinearMap.ker_eq_bot.mpr (graphLinear_injective b)))

/-- Exact normalized surface measure for every subset of an affine scalar graph. -/
theorem affineGraph_measure_image (b : EuclideanSpace ℝ ι)
    (c : EuclideanSpace ℝ (Option ι)) (s : Set (EuclideanSpace ℝ ι)) :
    μHE[Fintype.card ι] (affineGraph b c '' s) =
      ENNReal.ofReal (Real.sqrt (1 + ‖b‖ ^ 2)) * volume s := by
  calc
    μHE[Fintype.card ι] (affineGraph b c '' s) =
        μHE[Fintype.card ι] (graphLinear b '' s) := by
      change μHE[Fintype.card ι] ((fun x => graphLinear b x + c) '' s) = _
      simpa only [Set.image_image, IsometryEquiv.addRight_apply] using
        (IsometryEquiv.addRight c).isometry.euclideanHausdorffMeasure_image
          (d := Fintype.card ι) (graphLinear b '' s)
    _ = _ := graphLinear_measure_image b s

theorem affineGraph_restrict_range (b : EuclideanSpace ℝ ι)
    (c : EuclideanSpace ℝ (Option ι)) :
    (μHE[Fintype.card ι]).restrict (Set.range (affineGraph b c)) =
      ENNReal.ofReal (Real.sqrt (1 + ‖b‖ ^ 2)) •
        (volume : Measure (EuclideanSpace ℝ ι)).map (affineGraph b c) := by
  ext s hs
  rw [Measure.restrict_apply hs, Measure.smul_apply,
    Measure.map_apply (affineGraph_isClosedEmbedding b c).continuous.measurable hs]
  change μHE[Fintype.card ι] (s ∩ Set.range (affineGraph b c)) =
    ENNReal.ofReal (Real.sqrt (1 + ‖b‖ ^ 2)) * volume (affineGraph b c ⁻¹' s)
  rw [← Set.image_preimage_eq_inter_range, affineGraph_measure_image]

/-- The surface measure on an affine graph is the graph image of scaled volume. -/
theorem affineGraph_restrict_image (b : EuclideanSpace ℝ ι)
    (c : EuclideanSpace ℝ (Option ι)) (s : Set (EuclideanSpace ℝ ι)) :
    (μHE[Fintype.card ι]).restrict (affineGraph b c '' s) =
      ENNReal.ofReal (Real.sqrt (1 + ‖b‖ ^ 2)) •
        (volume.restrict s).map (affineGraph b c) := by
  have h := congrArg (fun μ : Measure (EuclideanSpace ℝ (Option ι)) =>
    μ.restrict (affineGraph b c '' s)) (affineGraph_restrict_range b c)
  rw [Measure.restrict_restrict_of_subset (Set.image_subset_range _ _),
    Measure.restrict_smul,
    (affineGraph_isClosedEmbedding b c).measurableEmbedding.restrict_map,
    Set.preimage_image_eq _ (affineGraph_isClosedEmbedding b c).injective] at h
  exact h

/-- Bochner integral transport with the normalized graph surface-area factor. -/
theorem affineGraph_integral_image {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : EuclideanSpace ℝ ι) (c : EuclideanSpace ℝ (Option ι))
    (s : Set (EuclideanSpace ℝ ι)) (f : EuclideanSpace ℝ (Option ι) → E) :
    (∫ z in affineGraph b c '' s, f z ∂μHE[Fintype.card ι]) =
      Real.sqrt (1 + ‖b‖ ^ 2) • ∫ x in s, f (affineGraph b c x) ∂volume := by
  rw [affineGraph_restrict_image, integral_smul_measure,
    (affineGraph_isClosedEmbedding b c).integral_map,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]

end

end BouRabeeGwynne
