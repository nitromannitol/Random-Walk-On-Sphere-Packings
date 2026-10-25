module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/CoordinateVolume.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.PaperObjects
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Exact volume-preserving coordinate splitting for polytope slicing. -/

open MeasureTheory

namespace BouRabeeGwynne

noncomputable section

variable {n : ℕ}

/-- Separate coordinate `i` from the remaining Euclidean coordinates.
The target is ordered with the horizontal coordinate first for Fubini. -/
def coordinateVolumeEquiv (i : Fin (n + 1)) : Euc (n + 1) ≃ᵐ Euc n × ℝ :=
  ((MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)).symm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i)).trans
      ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.toLp 2 (Fin n → ℝ))).trans MeasurableEquiv.prodComm)

@[simp] lemma coordinateVolumeEquiv_apply (i : Fin (n + 1)) (x : Euc (n + 1)) :
    coordinateVolumeEquiv i x = (WithLp.toLp 2 (fun j => x (i.succAbove j)), x i) := rfl

/-- Insert the line parameter at coordinate `i`. -/
def coordinateInsert (i : Fin (n + 1)) (y : Euc n) (t : ℝ) : Euc (n + 1) :=
  (coordinateVolumeEquiv i).symm (y, t)

/-- Both Euclidean volume and the zero-dimensional horizontal volume have their
actual product normalization; no Jacobian constant is assumed. -/
theorem measurePreserving_coordinateVolumeEquiv (i : Fin (n + 1)) :
    MeasurePreserving (coordinateVolumeEquiv i) := by
  have h₁ := PiLp.volume_preserving_ofLp (Fin (n + 1))
  have h₂ := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have h₃ := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (PiLp.volume_preserving_toLp (Fin n))
  have h₄ : MeasurePreserving (Prod.swap : ℝ × Euc n → Euc n × ℝ) := Measure.measurePreserving_swap
  exact h₄.comp (h₃.comp (h₂.comp h₁))

/-- Fubini along an actual coordinate line in Euclidean space. -/
theorem integral_eq_integral_coordinate_slices
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin (n + 1)) (f : Euc (n + 1) → E) (hf : Integrable f) :
    (∫ x, f x) = ∫ y : Euc n, ∫ t : ℝ, f (coordinateInsert i y t) := by
  have hmp := (measurePreserving_coordinateVolumeEquiv i).symm
  have hint := hmp.integrable_comp_of_integrable hf
  calc
    (∫ x, f x) = ∫ z : Euc n × ℝ, f ((coordinateVolumeEquiv i).symm z) :=
      (hmp.integral_comp (coordinateVolumeEquiv i).symm.measurableEmbedding f).symm
    _ = _ := integral_prod _ hint

end

end BouRabeeGwynne
