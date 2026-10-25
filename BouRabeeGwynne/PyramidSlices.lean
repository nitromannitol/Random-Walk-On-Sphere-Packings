module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/PyramidSlices.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.DualCells
public import Mathlib.Analysis.InnerProductSpace.Orthogonal

@[expose] public section

open scoped Topology ENNReal MeasureTheory
open MeasureTheory

namespace BouRabeeGwynne

variable {d : ℕ}

/-- The actual affine slice used by the Euclidean volume disintegration theorem. -/
noncomputable def perpendicularSlice (a e : Euc d) (t : ℝ) : AffineSubspace ℝ (Euc d) :=
  AffineSubspace.mk' (t • e + a) (ℝ ∙ e)ᗮ

lemma mem_perpendicularSlice (a e z : Euc d) (t : ℝ) :
    z ∈ perpendicularSlice a e t ↔
      inner ℝ e (z - a) = t * inner ℝ e e := by
  rw [perpendicularSlice, AffineSubspace.mem_mk',
    Submodule.mem_orthogonal_singleton_iff_inner_right]
  change inner ℝ e (z - (t • e + a)) = 0 ↔ _
  have h : z - (t • e + a) = (z - a) - t • e := by abel
  rw [h, inner_sub_right, inner_smul_right, sub_eq_zero]

lemma inner_homothety_sub (a e y : Euc d) (u : ℝ) :
    inner ℝ e (AffineMap.homothety a u y - a) = u * inner ℝ e (y - a) := by
  simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add,
    add_sub_cancel_right, inner_smul_right]

/-- Exact homothety parametrization of the convex-base pyramid. -/
theorem convexHull_insert_eq_homothety_image (a : Euc d) {s : Set (Euc d)}
    (hs : Convex ℝ s) (hne : s.Nonempty) :
    convexHull ℝ (insert a s) =
      (fun q : ℝ × Euc d => AffineMap.homothety a q.1 q.2) ''
        (Set.Icc (0 : ℝ) 1 ×ˢ s) := by
  rw [convexHull_insert_eq_segment_image a hs hne]
  apply congrArg (fun f : ℝ × Euc d → Euc d => f '' (Set.Icc (0 : ℝ) 1 ×ˢ s))
  funext q
  simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
  module

/-- A homothetic base point has slice parameter equal to its scale times the
base height. The nonzero direction gives a cancellable squared norm. -/
lemma homothety_mem_perpendicularSlice_iff (a : Euc d) {e y : Euc d}
    (he : e ≠ 0) {r : ℝ} (hy : y ∈ perpendicularSlice a e r) (u t : ℝ) :
    AffineMap.homothety a u y ∈ perpendicularSlice a e t ↔ u * r = t := by
  rw [mem_perpendicularSlice] at hy ⊢
  rw [inner_homothety_sub, hy, ← mul_assoc]
  constructor
  · exact mul_right_cancel₀ (real_inner_self_pos.mpr he).ne'
  · intro h
    rw [h]

/-- Every nonempty pyramid slice has height between the apex and the base. -/
lemma pyramid_slice_height_mem (a : Euc d) {e : Euc d} (he : e ≠ 0)
    {s : Set (Euc d)} (hs : Convex ℝ s) (hne : s.Nonempty)
    {r : ℝ} (hr : 0 < r) (hbase : s ⊆ perpendicularSlice a e r)
    {t : ℝ} {z : Euc d}
    (hz : z ∈ convexHull ℝ (insert a s)) (hzt : z ∈ perpendicularSlice a e t) :
    t ∈ Set.Icc (0 : ℝ) r := by
  rw [convexHull_insert_eq_homothety_image a hs hne] at hz
  obtain ⟨⟨u, y⟩, ⟨hu, hy⟩, rfl⟩ := hz
  have hut := (homothety_mem_perpendicularSlice_iff a he (hbase hy) u t).mp hzt
  constructor <;> nlinarith [hu.1, hu.2]

/-- The exact perpendicular section of a pyramid is a homothetic copy of its
base, including the degenerate apex section. -/
theorem pyramid_slice_eq_homothety (a : Euc d) {e : Euc d} (he : e ≠ 0)
    {s : Set (Euc d)} (hs : Convex ℝ s) (hne : s.Nonempty)
    {r : ℝ} (hr : 0 < r) (hbase : s ⊆ perpendicularSlice a e r)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) r) :
    convexHull ℝ (insert a s) ∩ perpendicularSlice a e t =
      AffineMap.homothety a (t / r) '' s := by
  ext z
  constructor
  · rintro ⟨hz, hzt⟩
    rw [convexHull_insert_eq_homothety_image a hs hne] at hz
    obtain ⟨⟨u, y⟩, ⟨_hu, hy⟩, rfl⟩ := hz
    have hut := (homothety_mem_perpendicularSlice_iff a he (hbase hy) u t).mp hzt
    have hu : u = t / r := (eq_div_iff hr.ne').mpr hut
    exact ⟨y, hy, by rw [hu]⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [convexHull_insert_eq_homothety_image a hs hne]
      exact ⟨(t / r, y), ⟨⟨div_nonneg ht.1 hr.le, (div_le_one₀ hr).mpr ht.2⟩, hy⟩,
        rfl⟩
    · apply (homothety_mem_perpendicularSlice_iff a he (hbase hy) (t / r) t).mpr
      exact div_mul_cancel₀ t hr.ne'

theorem pyramid_slice_eq_empty (a : Euc d) {e : Euc d} (he : e ≠ 0)
    {s : Set (Euc d)} (hs : Convex ℝ s) (hne : s.Nonempty)
    {r : ℝ} (hr : 0 < r) (hbase : s ⊆ perpendicularSlice a e r)
    {t : ℝ} (ht : t ∉ Set.Icc (0 : ℝ) r) :
    convexHull ℝ (insert a s) ∩ perpendicularSlice a e t = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro z ⟨hz, hzt⟩
  exact ht (pyramid_slice_height_mem a he hs hne hr hbase hz hzt)

/-- Away from the single apex parameter, normalized surface measure obeys the
exact homothety scaling factor. This is the integrand in the volume proof. -/
theorem pyramid_slice_measure (a : Euc d) {e : Euc d} (he : e ≠ 0)
    {s : Set (Euc d)} (hs : Convex ℝ s) (hne : s.Nonempty)
    {r : ℝ} (hr : 0 < r) (hbase : s ⊆ perpendicularSlice a e r)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) r) (ht0 : t ≠ 0) (k : ℕ) :
    μHE[k] (convexHull ℝ (insert a s) ∩ perpendicularSlice a e t) =
      ‖t / r‖₊ ^ k • μHE[k] s := by
  rw [pyramid_slice_eq_homothety a he hs hne hr hbase ht]
  exact euclideanHausdorffMeasure_homothety_image k a (div_ne_zero ht0 hr.ne') s

end BouRabeeGwynne
