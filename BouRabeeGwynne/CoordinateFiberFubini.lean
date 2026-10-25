module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/CoordinateFiberFubini.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.CoordinateHyperplane
public import BouRabeeGwynne.CoordinateVolume
public import BouRabeeGwynne.SupportFaceProjection
public import BouRabeeGwynne.FiberCalculus
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

@[expose] public section

open scoped ENNReal MeasureTheory
open MeasureTheory

namespace BouRabeeGwynne

noncomputable section

variable {n : ℕ}

@[simp] lemma coordinateProjection_coordinatePlaneGraph (i : Fin (n + 1))
    (a : Euc (n + 1)) (c : ℝ) (y : Euc n) :
    coordinateProjection i (coordinatePlaneGraph i a c y) = y := by
  unfold coordinateProjection coordinatePlaneGraph
  rw [LinearIsometryEquiv.apply_symm_apply, horizontalProjection_hyperplaneGraph]

lemma inner_coordinatePlaneGraph (i : Fin (n + 1)) (a : Euc (n + 1))
    (c : ℝ) (ha : a i ≠ 0) (y : Euc n) :
    inner ℝ a (coordinatePlaneGraph i a c y) = c := by
  rw [← (coordinateChart i).inner_map_map]
  unfold coordinatePlaneGraph
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact inner_hyperplaneGraph (coordinateChart i a) c ha y

@[simp] lemma coordinateProjection_coordinateInsert (i : Fin (n + 1))
    (y : Euc n) (t : ℝ) : coordinateProjection i (coordinateInsert i y t) = y := by
  have h := congrArg Prod.fst ((coordinateVolumeEquiv i).apply_symm_apply (y, t))
  exact h

@[simp] lemma coordinateInsert_apply (i : Fin (n + 1)) (y : Euc n) (t : ℝ) :
    coordinateInsert i y t i = t := by
  have h := congrArg Prod.snd ((coordinateVolumeEquiv i).apply_symm_apply (y, t))
  exact h

lemma coordinateInsert_eq_line (i : Fin (n + 1)) (y : Euc n) (t : ℝ) :
    coordinateInsert i y t = coordinatePlaneGraph i (coordinateAxis i) 0 y +
      t • coordinateAxis i := by
  calc
    coordinateInsert i y t =
        hyperplaneProjection (coordinateAxis i) (coordinateInsert i y t) +
          (inner ℝ (coordinateAxis i) (coordinateInsert i y t) /
            inner ℝ (coordinateAxis i) (coordinateAxis i)) • coordinateAxis i :=
      (hyperplaneProjection_decomposition _ _).symm
    _ = _ := by
      rw [← coordinatePlaneGraph_axis_projection, coordinateProjection_coordinateInsert]
      simp only [inner_coordinateAxis, coordinateInsert_apply, coordinateAxis_self, div_one]

namespace ConvexPolytope

variable (P : ConvexPolytope (n + 1))

lemma axisGraph_mem_projectedBase (i : Fin (n + 1)) {y : Euc n}
    (hy : y ∈ coordinateProjection i ''
      P.projectedBase (coordinateAxis i) (coordinateAxis_ne_zero i)) :
    coordinatePlaneGraph i (coordinateAxis i) 0 y ∈
      P.projectedBase (coordinateAxis i) (coordinateAxis_ne_zero i) := by
  obtain ⟨x, hx, rfl⟩ := hy
  rw [coordinatePlaneGraph_axis_projection,
    hyperplaneProjection_eq_self (coordinateAxis i) hx.1]
  exact hx

lemma coordinateInsert_not_mem_of_not_mem_projectedBase (i : Fin (n + 1)) {y : Euc n}
    (hy : y ∉ coordinateProjection i ''
      P.projectedBase (coordinateAxis i) (coordinateAxis_ne_zero i)) (t : ℝ) :
    coordinateInsert i y t ∉ P.carrier := by
  intro hx
  apply hy
  refine ⟨hyperplaneProjection (coordinateAxis i) (coordinateInsert i y t), ?_, ?_⟩
  · rw [P.projectedBase_eq_image (coordinateAxis_ne_zero i)]
    exact ⟨coordinateInsert i y t, hx, rfl⟩
  · rw [coordinateProjection_hyperplaneProjection, coordinateProjection_coordinateInsert]

/-- Fubini and the one-dimensional FTC on the exact closed fibers of the cell. -/
theorem integral_coordinate_fderiv_eq_endpoint_integral
    (i : Fin (n + 1)) {W : Set (Euc (n + 1))} (hW : IsOpen W)
    (hPW : P.carrier ⊆ W) {h : Euc (n + 1) → ℝ} (hh : ContDiffOn ℝ 1 h W) :
    (∫ x in P.carrier, (fderiv ℝ h x) (coordinateAxis i) ∂MeasureTheory.volume) =
      ∫ y in P.projectedBase (coordinateAxis i) (coordinateAxis_ne_zero i),
        (h (P.upperEndpoint (coordinateAxis i) (coordinateAxis_ne_zero i) y) -
          h (P.lowerEndpoint (coordinateAxis i) (coordinateAxis_ne_zero i) y)) ∂μHE[n] := by
  classical
  let e := coordinateAxis i
  let he := coordinateAxis_ne_zero i
  let B := coordinateProjection i '' P.projectedBase e he
  let b : Euc n → Euc (n + 1) := coordinatePlaneGraph i e 0
  let f : Euc (n + 1) → ℝ := fun x => (fderiv ℝ h x) e
  let g : Euc (n + 1) → ℝ := fun y =>
    h (P.upperEndpoint e he y) - h (P.lowerEndpoint e he y)
  have hB : MeasurableSet B :=
    ((P.isCompact_projectedBase he).image (continuous_coordinateProjection i)).measurableSet
  have hP : MeasurableSet P.carrier := P.compact.measurableSet
  have hfcont : ContinuousOn f P.carrier :=
    ((hh.continuousOn_fderiv_of_isOpen hW le_rfl).clm_apply continuousOn_const).mono hPW
  have hf : IntegrableOn f P.carrier := hfcont.integrableOn_compact P.compact
  have hfi : Integrable (P.carrier.indicator f) := (integrable_indicator_iff hP).mpr hf
  have hfiber (y : Euc n) :
      (∫ t : ℝ, P.carrier.indicator f (coordinateInsert i y t)) =
        B.indicator (fun y => g (b y)) y := by
    by_cases hy : y ∈ B
    · rw [Set.indicator_of_mem hy]
      have hb := P.axisGraph_mem_projectedBase i hy
      have hset : (fun t : ℝ => b y + t • e) ⁻¹' P.carrier =
          Set.Icc (P.lowerFiber e he (b y)) (P.upperFiber e he (b y)) :=
        P.line_preimage_eq_Icc he (b y) hb.2.1
      have hint : (fun t : ℝ => P.carrier.indicator f (coordinateInsert i y t)) =
          (Set.Icc (P.lowerFiber e he (b y)) (P.upperFiber e he (b y))).indicator
            (fun t => f (b y + t • e)) := by
        funext t
        rw [coordinateInsert_eq_line]
        change P.carrier.indicator f (b y + t • e) = _
        by_cases ht : t ∈ Set.Icc (P.lowerFiber e he (b y)) (P.upperFiber e he (b y))
        · have htP : b y + t • e ∈ P.carrier := by
            change t ∈ (fun t : ℝ => b y + t • e) ⁻¹' P.carrier
            rwa [hset]
          simp only [Set.indicator_of_mem htP, Set.indicator_of_mem ht]
        · have htP : b y + t • e ∉ P.carrier := by
            change t ∉ (fun t : ℝ => b y + t • e) ⁻¹' P.carrier
            rwa [hset]
          simp only [Set.indicator_of_notMem htP, Set.indicator_of_notMem ht]
      rw [hint, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hb.2.2]
      exact P.integral_fderiv_fiber_eq_sub he (b y) hb.2.1 hb.2.2 hW hPW hh
    · rw [Set.indicator_of_notMem hy]
      have hz : (fun t : ℝ => P.carrier.indicator f (coordinateInsert i y t)) = 0 := by
        funext t
        exact Set.indicator_of_notMem (P.coordinateInsert_not_mem_of_not_mem_projectedBase i hy t) f
      rw [hz]
      change (∫ _t : ℝ, (0 : ℝ)) = 0
      simp only [integral_zero]
  calc
    (∫ x in P.carrier, (fderiv ℝ h x) (coordinateAxis i)) =
        ∫ x, P.carrier.indicator f x := (integral_indicator hP).symm
    _ = ∫ y : Euc n, ∫ t : ℝ, P.carrier.indicator f (coordinateInsert i y t) :=
      integral_eq_integral_coordinate_slices i _ hfi
    _ = ∫ y : Euc n, B.indicator (fun y => g (b y)) y :=
      integral_congr_ae (Filter.Eventually.of_forall hfiber)
    _ = ∫ y in B, g (b y) := integral_indicator hB
    _ = ∫ y in P.projectedBase e he, g y ∂μHE[n] :=
      (coordinate_perpendicular_integral_projection i (fun _ hy => hy.1) g).symm

end ConvexPolytope
end
end BouRabeeGwynne
