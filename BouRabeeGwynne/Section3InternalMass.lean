module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/Section3InternalMass.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.Section3MassTrimming
public import BouRabeeGwynne.Section3CylinderVolume
public import BouRabeeGwynne.DualVolume
public import BouRabeeGwynne.DualVolumeSums

@[expose] public section

/-! Actual bad-bad dual cells and their cylinder mass bound. -/

open scoped Classical BigOperators MeasureTheory ENNReal
open MeasureTheory

namespace BouRabeeGwynne.TilingData

variable {d : ℕ} (T : TilingData d)

lemma orientedInteriorEdges_no_reverse (R : Set T.V) [Fintype R] (A : Set R)
    (p : T.V × T.V) (hp : p ∈ T.orientedInteriorEdges R A)
    (q : T.V × T.V) (hq : q ∈ T.orientedInteriorEdges R A) (hpq : p ≠ q) :
    p ≠ q.swap := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
  intro heq
  have h₁ : a.out.1 = b.out.2 := Subtype.ext (congrArg Prod.fst heq)
  have h₂ : a.out.2 = b.out.1 := Subtype.ext (congrArg Prod.snd heq)
  have hab : a = b := by
    calc
      a = s(a.out.1, a.out.2) := (Quot.out_eq a).symm
      _ = s(b.out.2, b.out.1) := by rw [h₁, h₂]
      _ = s(b.out.1, b.out.2) := Sym2.eq_swap
      _ = b := Quot.out_eq b
  exact hpq (congrArg (T.orientedContactPair R) hab)

end BouRabeeGwynne.TilingData

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

lemma isCompact_columnBadSet (R : Set T.V) [Fintype R] (A : Set R)
    (e : Euc d) (he : e ≠ 0) (f : T.V → ℝ) (τ : ℝ) :
    IsCompact (T.columnBadSet R A e he f τ) := by
  have heq : T.columnBadSet R A e he f τ =
      ⋃ v ∈ {v : R | v ∈ A ∧ τ < |f v|}, (T.cell v).projectedBase e he := by
    ext y
    simp only [columnBadSet, Set.mem_setOf_eq, Set.mem_iUnion]
    aesop
  rw [heq]
  exact (Set.toFinite _).isCompact_biUnion
    (fun v _ => (T.cell v).isCompact_projectedBase he)

lemma columnBadSet_perpendicular (R : Set T.V) (A : Set R)
    (e : Euc d) (he : e ≠ 0) (f : T.V → ℝ) (τ : ℝ) :
    ∀ y ∈ T.columnBadSet R A e he f τ, inner ℝ e y = 0 := by
  rintro y ⟨v, hv, hy, hlarge⟩
  exact hy.1

lemma cell_subset_badCylinder (R : Set T.V) (A : Set R)
    (e : Euc d) (he : e ≠ 0) (f : T.V → ℝ) (τ a b : ℝ)
    (hheight : ∀ v ∈ A, ∀ x ∈ (T.cell v).carrier,
      inner ℝ e x / inner ℝ e e ∈ Set.Icc a b)
    {v : R} (hv : v ∈ A) (hlarge : τ < |f v|) :
    (T.cell v).carrier ⊆ orthogonalCylinder e a b (T.columnBadSet R A e he f τ) := by
  intro x hx
  refine ⟨⟨v, hv, ?_, hlarge⟩, hheight v hv x hx⟩
  rw [(T.cell v).projectedBase_eq_image he]
  exact ⟨x, hx, rfl⟩

/-- Actual dual cells of bad-bad edges lie in the bad-column cylinder. -/
lemma dualPolytope_subset_badCylinder (R : Set T.V) (A : Set R)
    (e : Euc d) (he : e ≠ 0) (f : T.V → ℝ) (τ a b : ℝ)
    (hheight : ∀ v ∈ A, ∀ x ∈ (T.cell v).carrier,
      inner ℝ e x / inner ℝ e e ∈ Set.Icc a b)
    {v w : R} (hv : v ∈ A) (hw : w ∈ A)
    (hlargev : τ < |f v|) (hlargew : τ < |f w|) :
    T.toTilingData.dualPolytope v w ⊆
      orthogonalCylinder e a b (T.columnBadSet R A e he f τ) :=
  (T.toTilingData.dualPolytope_subset_cells v w).trans (Set.union_subset
    (T.cell_subset_badCylinder R A e he f τ a b hheight hv hlargev)
    (T.cell_subset_badCylinder R A e he f τ a b hheight hw hlargew))

noncomputable def internalEdges (R : Set T.V) [Fintype R] (B : Set R) :
    Finset (T.V × T.V) :=
  (T.toTilingData.orientedInteriorEdges R B).filter
    (fun p => p.1 ∈ Subtype.val '' B ∧ p.2 ∈ Subtype.val '' B)

lemma mem_subtype_image_iff (R : Set T.V) (B : Set R) (v : R) :
    (v : T.V) ∈ Subtype.val '' B ↔ v ∈ B := by
  constructor
  · rintro ⟨w, hw, heq⟩
    exact (Subtype.ext heq : w = v) ▸ hw
  · exact fun hv => ⟨v, hv, rfl⟩

lemma internalMass_eq_sum_internalEdges (R : Set T.V) [Fintype R] (B : Set R) :
    T.internalMass R B = ∑ p ∈ T.internalEdges R B,
      (T.facetVolume p.1 p.2).toReal * ‖T.pos p.2 - T.pos p.1‖ := by
  rw [internalEdges, Finset.sum_filter]
  let g : T.V → T.V → ℝ := fun v w =>
    if v ∈ Subtype.val '' B ∧ w ∈ Subtype.val '' B then
      (T.facetVolume v w).toReal * ‖T.pos w - T.pos v‖ else 0
  have hsymm : ∀ v w, g v w = g w v := by
    intro v w
    simp only [g, T.toTilingData.facetVolume_symm v w, norm_sub_rev,
      and_comm]
  rw [T.toTilingData.sum_orientedInteriorEdges_eq_half_ordered R B g hsymm]
  unfold internalMass
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  simp only [g, T.mem_subtype_image_iff]
  by_cases ha : T.adj v w <;> by_cases hv : v ∈ B <;>
    by_cases hw : w ∈ B <;> simp [ha, hv, hw]

/-- Generic once-oriented facet mass is bounded by the actual volume of a
containing measurable set. This uses the proved dual-volume and disjointness
theorems rather than assuming a geometric packing bound. -/
theorem sum_facet_weight_le_dim_mul_volume (hd : 1 ≤ d)
    (E : Finset (T.V × T.V)) (hE : ∀ p ∈ E, T.adj p.1 p.2)
    (hrev : ∀ p ∈ E, ∀ q ∈ E, p ≠ q → p ≠ q.swap)
    {S : Set (Euc d)} (hS : μHE[d] S ≠ ∞)
    (hcontain : ∀ p ∈ E, T.toTilingData.dualPolytope p.1 p.2 ⊆ S) :
    (∑ p ∈ E, (T.facetVolume p.1 p.2).toReal * ‖T.pos p.2 - T.pos p.1‖) ≤
      (d : ℝ) * (μHE[d] S).toReal := by
  have hbound := T.toTilingData.sum_dualVolume_le_measure hd E hE hrev hcontain
  have hreal := ENNReal.toReal_mono hS hbound
  rw [ENNReal.toReal_sum (fun p _ => (T.toTilingData.dualVolume_lt_top p.1 p.2).ne)]
    at hreal
  calc
    _ = ∑ p ∈ E, (d : ℝ) * (T.toTilingData.dualVolume p.1 p.2).toReal := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [mul_comm]
      exact T.edgeLength_mul_facetVolume_eq_dim_mul_dualVolume hd (hE p hp)
    _ = (d : ℝ) * ∑ p ∈ E, (T.toTilingData.dualVolume p.1 p.2).toReal :=
      (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hreal (Nat.cast_nonneg d)

/-- A fixed finite-volume collar containing the actual endpoint cells bounds
the total incident mass uniformly. This supplies the initial mass input for
both the planar argument and the Hypothesis II iteration. -/
theorem incidentMass_le_dim_mul_volume (hd : 1 ≤ d)
    (R : Set T.V) [Fintype R] (A : Set R) {Q : Set (Euc d)}
    (hQ : μHE[d] Q ≠ ∞) (hcellQ : ∀ v : R, (T.cell v).carrier ⊆ Q) :
    T.incidentMass R A ≤ (d : ℝ) * (μHE[d] Q).toReal := by
  unfold incidentMass
  apply T.sum_facet_weight_le_dim_mul_volume hd
    (T.toTilingData.orientedInteriorEdges R A)
    (T.toTilingData.orientedInteriorEdges_adj R A)
    (T.toTilingData.orientedInteriorEdges_no_reverse R A) hQ
  intro p hp
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
  change T.toTilingData.dualPolytope a.out.1 a.out.2 ⊆ Q
  exact (T.toTilingData.dualPolytope_subset_cells a.out.1 a.out.2).trans
    (Set.union_subset (hcellQ a.out.1) (hcellQ a.out.2))

/-- The internal bad-edge mass is controlled by its bad-column cylinder,
the geometric input for the genuine trimming contraction. -/
theorem internalMass_bad_le_cylinder_volume (hd : 1 ≤ d)
    (R : Set T.V) [Fintype R] (A : Set R) (f : T.V → ℝ) (τ : ℝ)
    (e : Euc d) (he : e ≠ 0) (a b : ℝ)
    (hheight : ∀ v ∈ A, ∀ x ∈ (T.cell v).carrier,
      inner ℝ e x / inner ℝ e e ∈ Set.Icc a b)
    (hfinite : μHE[d]
      (orthogonalCylinder e a b (T.columnBadSet R A e he f τ)) ≠ ∞) :
    T.internalMass R (FiniteConductanceNetwork.errorBadSet A (fun v => f v) τ) ≤
      (d : ℝ) * (μHE[d]
        (orthogonalCylinder e a b (T.columnBadSet R A e he f τ))).toReal := by
  let B := FiniteConductanceNetwork.errorBadSet A (fun v : R => f v) τ
  rw [T.internalMass_eq_sum_internalEdges]
  apply T.sum_facet_weight_le_dim_mul_volume hd (T.internalEdges R B)
  · intro p hp
    exact T.toTilingData.orientedInteriorEdges_adj R B p (Finset.mem_filter.mp hp).1
  · intro p hp q hq hpq
    exact T.toTilingData.orientedInteriorEdges_no_reverse R B p
      (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1 hpq
  · exact hfinite
  · intro p hp
    obtain ⟨v, hv, hvp⟩ := (Finset.mem_filter.mp hp).2.1
    obtain ⟨w, hw, hwp⟩ := (Finset.mem_filter.mp hp).2.2
    rw [← hvp, ← hwp]
    exact T.dualPolytope_subset_badCylinder R A e he f τ a b hheight
      hv.1 hw.1 hv.2 hw.2

/-- Exact cylinder volume turns a bad-column measure bound into internal
edge mass. The direction need not be normalized. -/
theorem internalMass_bad_le_of_column_bound (hd : 1 ≤ d)
    (R : Set T.V) [Fintype R] (A : Set R) (f : T.V → ℝ) (τ : ℝ)
    (e : Euc d) (he : e ≠ 0) (a b : ℝ) (hab : a ≤ b)
    (hheight : ∀ v ∈ A, ∀ x ∈ (T.cell v).carrier,
      inner ℝ e x / inner ℝ e e ∈ Set.Icc a b)
    {β : ℝ} (hβ : 0 ≤ β)
    (hbad : μHE[d - 1] (T.columnBadSet R A e he f τ) ≤ ENNReal.ofReal β) :
    T.internalMass R (FiniteConductanceNetwork.errorBadSet A (fun v => f v) τ) ≤
      (d : ℝ) * ‖e‖ * (b - a) * β := by
  let Y := T.columnBadSet R A e he f τ
  have hY : μHE[d - 1] Y ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbad
  have hcyl := orthogonalCylinder_volume e he a b
    (T.isCompact_columnBadSet R A e he f τ).measurableSet
    (T.columnBadSet_perpendicular R A e he f τ)
  have hfinite : μHE[d] (orthogonalCylinder e a b Y) ≠ ∞ := by
    rw [hcyl]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top enorm_ne_top ENNReal.ofReal_ne_top) hY
  have hreal : (μHE[d - 1] Y).toReal ≤ β := by
    simpa only [ENNReal.toReal_ofReal hβ] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hbad
  calc
    _ ≤ (d : ℝ) * (μHE[d] (orthogonalCylinder e a b Y)).toReal :=
      T.internalMass_bad_le_cylinder_volume hd R A f τ e he a b hheight hfinite
    _ = (d : ℝ) * ‖e‖ * (b - a) * (μHE[d - 1] Y).toReal := by
      rw [hcyl, ENNReal.toReal_mul, ENNReal.toReal_mul, toReal_enorm,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hreal
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg d) (norm_nonneg _))
        (sub_nonneg.mpr hab))

/-- The genuine geometric trimming estimate. It combines actual column paths,
surface integrals, disjoint dual volumes, the cylinder formula, and the finite
gradient estimate. It applies to every function with zero exterior data. -/
theorem incidentMass_trimmed_le_contraction_factor (hd : 1 ≤ d)
    (R : Set T.V) [Fintype R] (A : Set R)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    (hcellD : ∀ v ∈ A, (T.cell v).carrier ⊆ interior T.domain)
    (f : T.V → ℝ) (hzero : ∀ v : R, v ∉ A → f v = 0)
    (e : Euc d) (he : e ≠ 0) (a b : ℝ) (hab : a ≤ b)
    (hheight : ∀ v ∈ A, ∀ x ∈ (T.cell v).carrier,
      inner ℝ e x / inner ℝ e e ∈ Set.Icc a b)
    {C τ L ℓ : ℝ} (hC : 0 ≤ C) (hτ : 0 < τ) (hℓ : 0 < ℓ)
    (hlength : ∀ v w : R, T.adj v w → ‖T.pos w - T.pos v‖ ≤ L)
    (henergy : T.incidentEnergy R A f ≤ C ^ 2 * T.incidentMass R A) :
    T.incidentMass R ((T.finiteNetwork R).trimmedErrorSet A (fun v => f v) τ ℓ) ≤
      ((d : ℝ) * ‖e‖ * (b - a) * C / τ + (L ^ 2 / ℓ ^ 2) * C ^ 2) *
        T.incidentMass R A := by
  have hm := T.incidentMass_nonneg R A
  have hsq : T.incidentEnergy R A f * T.incidentMass R A ≤
      (C * T.incidentMass R A) ^ 2 := by
    calc
      _ ≤ (C ^ 2 * T.incidentMass R A) * T.incidentMass R A :=
        mul_le_mul_of_nonneg_right henergy hm
      _ = _ := by ring
  have hsqrt := Real.sqrt_le_iff.mpr ⟨mul_nonneg hC hm, hsq⟩
  rw [Real.sqrt_mul (T.incidentEnergy_nonneg R A f)] at hsqrt
  have hbad : μHE[d - 1] (T.columnBadSet R A e he f τ) ≤
      ENNReal.ofReal (C * T.incidentMass R A / τ) :=
    (T.column_bad_measure_le hd e he R A hneighbors hcellD f hzero hτ).trans
      (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hsqrt hτ.le))
  have hinter := T.internalMass_bad_le_of_column_bound hd R A f τ e he a b hab
    hheight (div_nonneg (mul_nonneg hC hm) hτ.le) hbad
  have hE : (T.finiteNetwork R).energy (fun v : R => f v) ≤
      C ^ 2 * T.incidentMass R A := by
    rw [← T.incidentEnergy_eq_networkEnergy R A f hzero]
    exact henergy
  calc
    _ ≤ T.internalMass R (FiniteConductanceNetwork.errorBadSet A (fun v => f v) τ) +
        (L ^ 2 / ℓ ^ 2) * (T.finiteNetwork R).energy (fun v => f v) :=
      T.incidentMass_trimmed_le_internalMass_add_scaled_energy R A f τ hℓ hlength
    _ ≤ (d : ℝ) * ‖e‖ * (b - a) * (C * T.incidentMass R A / τ) +
        (L ^ 2 / ℓ ^ 2) * (C ^ 2 * T.incidentMass R A) :=
      add_le_add hinter (mul_le_mul_of_nonneg_left hE
        (div_nonneg (sq_nonneg _) (sq_nonneg _)))
    _ = _ := by ring

end BouRabeeGwynne.OrthogonalTiling
