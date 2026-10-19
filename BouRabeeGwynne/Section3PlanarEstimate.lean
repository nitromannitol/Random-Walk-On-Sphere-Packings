-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/Section3PlanarEstimate.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.Section3Boxes
import BouRabeeGwynne.Section3GoodLines
import BouRabeeGwynne.Section3ColumnEstimate
import BouRabeeGwynne.CoordinateHyperplane
import Mathlib.Tactic.FinCases

/-! Planar good boxes and the uniform error estimate from actual column measures. -/

open scoped Classical ENNReal BigOperators MeasureTheory
open MeasureTheory

namespace BouRabeeGwynne

lemma planar_hyperplaneProjection (i : Fin 2) (x : Euc 2) :
    hyperplaneProjection (coordinateAxis i.rev) x = x i • coordinateAxis i := by
  simp only [hyperplaneProjection_apply, inner_coordinateAxis, coordinateAxis_self, div_one]
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [coordinateAxis,
      EuclideanSpace.basisFun_apply, PiLp.single_apply, PiLp.sub_apply, PiLp.smul_apply]

namespace OrthogonalTiling

variable (T : OrthogonalTiling 2)

lemma abs_le_of_good_planar_cut (R : Set T.V) (A : Set R)
    (f : T.V → ℝ) (η : ℝ) (i : Fin 2) (t : ℝ)
    (ht : t • coordinateAxis i ∉ T.columnBadSet R A (coordinateAxis i.rev)
      (coordinateAxis_ne_zero i.rev) f η)
    {v : R} (hv : v ∈ A) {x : Euc 2} (hx : x ∈ (T.cell v).carrier)
    (hxi : x i = t) : |f v| ≤ η := by
  by_contra h
  apply ht
  refine ⟨v, hv, ?_, lt_of_not_ge h⟩
  rw [(T.cell v).projectedBase_eq_image]
  exact ⟨x, hx, by rw [planar_hyperplaneProjection, hxi]⟩

/-- The rectangle construction used for planar convergence. Each cut lies
strictly outside the target point and avoids the actual bad-column base. -/
theorem exists_planar_good_box (R : Set T.V) (A : Set R) (f : T.V → ℝ)
    (η : ℝ) (x₀ : Euc 2) {ℓ r : ℝ} (hℓ : 0 ≤ ℓ) (hr : ℓ < r)
    (hbad : ∀ i : Fin 2, μHE[1]
      (T.columnBadSet R A (coordinateAxis i.rev) (coordinateAxis_ne_zero i.rev) f η)
        ≤ ENNReal.ofReal ℓ) :
    ∃ lower upper : Fin 2 → ℝ,
      (∀ i, lower i ∈ Set.Ioo (x₀ i - 2 * r) (x₀ i - r)) ∧
      (∀ i, upper i ∈ Set.Ioo (x₀ i + r) (x₀ i + 2 * r)) ∧
      (∀ v ∈ A, (∃ i, ∃ x ∈ (T.cell v).carrier,
        x i = lower i ∨ x i = upper i) → |f v| ≤ η) := by
  have hlower (i : Fin 2) := exists_unitLine_parameter_outside_of_bound
    (norm_coordinateAxis i)
    (T.columnBadSet R A (coordinateAxis i.rev) (coordinateAxis_ne_zero i.rev) f η)
    hℓ (hbad i) (show ℓ < (x₀ i - r) - (x₀ i - 2 * r) by linarith)
  have hupper (i : Fin 2) := exists_unitLine_parameter_outside_of_bound
    (norm_coordinateAxis i)
    (T.columnBadSet R A (coordinateAxis i.rev) (coordinateAxis_ne_zero i.rev) f η)
    hℓ (hbad i) (show ℓ < (x₀ i + 2 * r) - (x₀ i + r) by linarith)
  choose lower hlower_mem hlower_good using hlower
  choose upper hupper_mem hupper_good using hupper
  refine ⟨lower, upper, hlower_mem, hupper_mem, ?_⟩
  rintro v hv ⟨i, x, hx, hxi | hxi⟩
  · exact T.abs_le_of_good_planar_cut R A f η i _ (hlower_good i) hv hx hxi
  · exact T.abs_le_of_good_planar_cut R A f η i _ (hupper_good i) hv hx hxi

/-- A deliberately nonsharp diameter bound suffices for the qualitative
convergence theorem and avoids an unproved endpoint choice. -/
lemma planar_good_box_diameter (x₀ : Euc 2) {r : ℝ} (hr : 0 ≤ r)
    (lower upper : Fin 2 → ℝ)
    (hlo : ∀ i, lower i ∈ Set.Ioo (x₀ i - 2 * r) (x₀ i - r))
    (hhi : ∀ i, upper i ∈ Set.Ioo (x₀ i + r) (x₀ i + 2 * r)) :
    ∀ x ∈ slabIntersection (fun i => innerSL ℝ (coordinateAxis i)) lower upper,
    ∀ y ∈ slabIntersection (fun i => innerSL ℝ (coordinateAxis i)) lower upper,
      dist x y ≤ 8 * r := by
  intro x hx y hy
  have hcoord (i : Fin 2) : |x i - y i| ≤ 4 * r := by
    have hx' := hx i
    have hy' := hy i
    change lower i < inner ℝ (coordinateAxis i) x ∧
      inner ℝ (coordinateAxis i) x < upper i at hx'
    change lower i < inner ℝ (coordinateAxis i) y ∧
      inner ℝ (coordinateAxis i) y < upper i at hy'
    simp only [inner_coordinateAxis] at hx' hy'
    exact abs_le.mpr ⟨by linarith [(hlo i).1, (hhi i).2],
      by linarith [(hlo i).1, (hhi i).2]⟩
  have hs (i : Fin 2) : (x i - y i) ^ 2 ≤ (4 * r) ^ 2 := by
    simpa only [← pow_two, sq_abs] using mul_self_le_mul_self (abs_nonneg _) (hcoord i)
  have hnorm : ‖x - y‖ ^ 2 ≤ 2 * (4 * r) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ i : Fin 2, (4 * r) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [PiLp.sub_apply] using hs i
      _ = _ := by simp
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (x - y)]

/-- Planar maximum-principle assembly. The column measure is an input supplied
by the independently proved column estimate; no bound on the interior error
is assumed. Whole cells define the local rectangle region. -/
theorem planar_error_le_of_column_measure
    (R : Set T.V) [Fintype R] (A : Set R)
    (haccess : (T.finiteNetwork R).BoundaryAccessible A)
    (h g : T.V → ℝ)
    (hsol : (T.finiteNetwork R).SolvesDirichlet A (fun v => g v) (fun v => h v))
    {η ω ℓ r : ℝ} (hη : 0 ≤ η) (hω : 0 ≤ ω) (hℓ : 0 ≤ ℓ) (hr : ℓ < r)
    (hbad : ∀ i : Fin 2, μHE[1]
      (T.columnBadSet R A (coordinateAxis i.rev) (coordinateAxis_ne_zero i.rev)
        (h - g) η) ≤ ENNReal.ofReal ℓ)
    (hmesh : T.mesh ≠ ∞)
    (hmod : ∀ v w : R, dist (T.pos w) (T.pos v) ≤ T.mesh.toReal + 8 * r →
      |g w - g v| ≤ ω) : ∀ v ∈ A, |h v - g v| ≤ η + ω := by
  intro v hv
  obtain ⟨lower, upper, hlo, hhi, hgood⟩ :=
    T.exists_planar_good_box R A (h - g) η (T.pos v) hℓ hr hbad
  have hpos : 0 < r := hℓ.trans_lt hr
  have hvbox : T.pos v ∈
      slabIntersection (fun i => innerSL ℝ (coordinateAxis i)) lower upper := by
    intro i
    change lower i < inner ℝ (coordinateAxis i) (T.pos v) ∧
      inner ℝ (coordinateAxis i) (T.pos v) < upper i
    rw [inner_coordinateAxis]
    exact ⟨by linarith [(hlo i).2], by linarith [(hhi i).1]⟩
  apply T.error_le_of_good_box R A haccess (fun v => h v) (fun v => g v) hsol
    (fun i => innerSL ℝ (coordinateAxis i)) lower upper hη hω
    (fun w hw hcut => ?_) hmesh
    (planar_good_box_diameter (T.pos v) hpos.le lower upper hlo hhi) hv hvbox
    (fun w hw => hmod v w hw)
  apply hgood w hw
  obtain ⟨i, x, hx, hcut⟩ := hcut
  exact ⟨i, x, hx, by simpa only [innerSL_apply_apply, inner_coordinateAxis] using hcut⟩

/-- The planar PDE estimate with its exact upstream energy and mass inputs.
Its right side can be made arbitrarily small by fixing a continuity radius
and then sending the mesh-dependent energy constant to zero. -/
theorem planar_error_le_of_energy_bound
    (R : Set T.V) [Fintype R] (A : Set R)
    (haccess : (T.finiteNetwork R).BoundaryAccessible A)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    (hcellD : ∀ v ∈ A, (T.cell v).carrier ⊆ interior T.domain)
    (h g : T.V → ℝ)
    (hsol : (T.finiteNetwork R).SolvesDirichlet A (fun v => g v) (fun v => h v))
    {C K η ω r : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) (hη : 0 < η) (hω : 0 ≤ ω)
    (henergy : T.incidentEnergy R A (h - g) ≤ C ^ 2 * T.incidentMass R A)
    (hmass : T.incidentMass R A ≤ K)
    (hr : C * K / η < r) (hmesh : T.mesh ≠ ∞)
    (hmod : ∀ v w : R, dist (T.pos w) (T.pos v) ≤ T.mesh.toReal + 8 * r →
      |g w - g v| ≤ ω) : ∀ v ∈ A, |h v - g v| ≤ η + ω := by
  have hzero : ∀ v : R, v ∉ A → (h - g) v = 0 := by
    intro v hv
    exact sub_eq_zero.mpr (hsol.2 v hv)
  have hm := T.incidentMass_nonneg R A
  have hsquare : T.incidentEnergy R A (h - g) * T.incidentMass R A ≤
      (C * T.incidentMass R A) ^ 2 := by
    calc
      _ ≤ (C ^ 2 * T.incidentMass R A) * T.incidentMass R A :=
        mul_le_mul_of_nonneg_right henergy hm
      _ = _ := by ring
  have hsqrt := Real.sqrt_le_iff.mpr ⟨mul_nonneg hC hm, hsquare⟩
  rw [Real.sqrt_mul (T.incidentEnergy_nonneg R A (h - g))] at hsqrt
  apply T.planar_error_le_of_column_measure R A haccess h g hsol hη.le hω
    (div_nonneg (mul_nonneg hC hK) hη.le) hr _ hmesh hmod
  intro i
  exact (T.column_bad_measure_le (by norm_num) (coordinateAxis i.rev)
    (coordinateAxis_ne_zero i.rev) R A hneighbors hcellD (h - g) hzero hη).trans
    (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
      (hsqrt.trans (mul_le_mul_of_nonneg_left hmass hC)) hη.le))

end OrthogonalTiling
end BouRabeeGwynne
