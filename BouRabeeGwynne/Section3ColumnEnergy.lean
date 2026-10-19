-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/Section3ColumnEnergy.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.Section3Projection
import BouRabeeGwynne.Section3WeightedEnergy
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Real.Sqrt

/-!
# Section 3: the integrated column-gradient estimate

For a finite collection of actual oriented contacts, integrate the sum of
absolute gradients over the projected contacts. Projection decreases surface
measure, and Cauchy–Schwarz gives the product of discrete edge energy and
facet-area times edge-length mass. An edge collection with one orientation
per edge gives exactly the normalization in Lemma 3.1.
-/

open scoped BigOperators Classical MeasureTheory ENNReal
open MeasureTheory

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

noncomputable def columnVariation (e : Euc d) (E : Finset (T.V × T.V))
    (f : T.V → ℝ) (y : Euc d) : ℝ :=
  ∑ a ∈ E, (hyperplaneProjection e '' T.facet a.1 a.2).indicator
    (fun _ => |f a.2 - f a.1|) y

lemma columnVariation_integrable (e : Euc d) (E : Finset (T.V × T.V))
    (hE : ∀ a ∈ E, T.adj a.1 a.2) (f : T.V → ℝ) :
    Integrable (T.columnVariation e E f) μHE[d - 1] := by
  apply integrable_finsetSum
  intro a ha
  apply (integrable_indicator_iff (T.projected_facet_compact e a.1 a.2).measurableSet).mpr
  exact integrableOn_const (T.projected_facet_measure_ne_top e (hE a ha))

lemma integral_columnVariation (e : Euc d) (E : Finset (T.V × T.V))
    (hE : ∀ a ∈ E, T.adj a.1 a.2) (f : T.V → ℝ) :
    (∫ y, T.columnVariation e E f y ∂μHE[d - 1]) =
      ∑ a ∈ E, (μHE[d - 1] (hyperplaneProjection e '' T.facet a.1 a.2)).toReal *
        |f a.2 - f a.1| := by
  unfold columnVariation
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [integral_indicator_const _ (T.projected_facet_compact e a.1 a.2).measurableSet]
    rfl
  · intro a ha
    apply (integrable_indicator_iff
      (T.projected_facet_compact e a.1 a.2).measurableSet).mpr
    exact integrableOn_const (T.projected_facet_measure_ne_top e (hE a ha))

lemma integral_columnVariation_le_facetSum (e : Euc d) (E : Finset (T.V × T.V))
    (hE : ∀ a ∈ E, T.adj a.1 a.2) (f : T.V → ℝ) :
    (∫ y, T.columnVariation e E f y ∂μHE[d - 1]) ≤
      ∑ a ∈ E, |f a.2 - f a.1| * (T.facetVolume a.1 a.2).toReal := by
  rw [T.integral_columnVariation e E hE f]
  apply Finset.sum_le_sum
  intro a ha
  rw [mul_comm]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact ENNReal.toReal_mono (T.toTilingData.facetVolume_ne_top (hE a ha))
    (T.projected_facet_measure_le e a.1 a.2)

theorem facetSum_le_sqrt_energy_mul_sqrt_mass (E : Finset (T.V × T.V))
    (hE : ∀ a ∈ E, T.adj a.1 a.2) (f : T.V → ℝ) :
    (∑ a ∈ E, |f a.2 - f a.1| * (T.facetVolume a.1 a.2).toReal) ≤
      Real.sqrt (∑ a ∈ E, T.conductanceReal a.1 a.2 * (f a.2 - f a.1) ^ 2) *
        Real.sqrt (∑ a ∈ E, (T.facetVolume a.1 a.2).toReal *
          ‖T.pos a.2 - T.pos a.1‖) := by
  let A : T.V × T.V → ℝ := fun a => T.conductanceReal a.1 a.2 * (f a.2 - f a.1) ^ 2
  let B : T.V × T.V → ℝ := fun a =>
    T.conductanceReal a.1 a.2 * ‖T.pos a.2 - T.pos a.1‖ ^ 2
  have hcs := Real.sum_sqrt_mul_sqrt_le E
    (fun a => show 0 ≤ A a from mul_nonneg (T.conductanceReal_nonneg _ _) (sq_nonneg _))
    (fun a => show 0 ≤ B a from mul_nonneg (T.conductanceReal_nonneg _ _) (sq_nonneg _))
  have hterm (a : T.V × T.V) (ha : a ∈ E) :
      Real.sqrt (A a) * Real.sqrt (B a) =
        |f a.2 - f a.1| * (T.facetVolume a.1 a.2).toReal := by
    have hn := ne_of_gt (T.edge_norm_pos (hE a ha))
    have halength : T.conductanceReal a.1 a.2 * ‖T.pos a.2 - T.pos a.1‖ =
        (T.facetVolume a.1 a.2).toReal := by
      rw [T.conductanceReal_of_adj (hE a ha)]
      exact div_mul_cancel₀ _ hn
    dsimp [A, B]
    rw [Real.sqrt_mul (T.conductanceReal_nonneg _ _), Real.sqrt_sq_eq_abs,
      Real.sqrt_mul (T.conductanceReal_nonneg _ _), Real.sqrt_sq (norm_nonneg _)]
    calc
      _ = (Real.sqrt (T.conductanceReal a.1 a.2) *
          Real.sqrt (T.conductanceReal a.1 a.2)) *
            (|f a.2 - f a.1| * ‖T.pos a.2 - T.pos a.1‖) := by ring
      _ = |f a.2 - f a.1| *
          (T.conductanceReal a.1 a.2 * ‖T.pos a.2 - T.pos a.1‖) := by
        rw [Real.mul_self_sqrt (T.conductanceReal_nonneg _ _)]
        ring
      _ = _ := by rw [halength]
  have hsum : (∑ a ∈ E, B a) =
      ∑ a ∈ E, (T.facetVolume a.1 a.2).toReal * ‖T.pos a.2 - T.pos a.1‖ := by
    apply Finset.sum_congr rfl
    intro a ha
    exact T.conductanceReal_mul_edge_norm_sq (hE a ha)
  simpa only [Finset.sum_congr rfl hterm, hsum] using hcs

theorem integral_columnVariation_le_energy (e : Euc d) (E : Finset (T.V × T.V))
    (hE : ∀ a ∈ E, T.adj a.1 a.2) (f : T.V → ℝ) :
    (∫ y, T.columnVariation e E f y ∂μHE[d - 1]) ≤
      Real.sqrt (∑ a ∈ E, T.conductanceReal a.1 a.2 * (f a.2 - f a.1) ^ 2) *
        Real.sqrt (∑ a ∈ E, (T.facetVolume a.1 a.2).toReal *
          ‖T.pos a.2 - T.pos a.1‖) :=
  (T.integral_columnVariation_le_facetSum e E hE f).trans
    (T.facetSum_le_sqrt_energy_mul_sqrt_mass E hE f)

end BouRabeeGwynne.OrthogonalTiling
