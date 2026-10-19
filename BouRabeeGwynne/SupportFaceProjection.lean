-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/SupportFaceProjection.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.ProjectedBase

/-!
# Supporting faces and the actual endpoints of polytope fibers

These identities retain redundant halfspace constraints.  A later partition
must deduplicate their planes before summing surface integrals.
-/

namespace BouRabeeGwynne

lemma hyperplaneProjection_decomposition {d : ℕ} (e x : Euc d) :
    hyperplaneProjection e x + (inner ℝ e x / inner ℝ e e) • e = x := by
  rw [hyperplaneProjection_apply, sub_add_cancel]

namespace ConvexPolytope

variable {d : ℕ} (P : ConvexPolytope d)

/-- The actual slice of the cell on the boundary plane of a supplied constraint. -/
def supportFace (p : Euc d × ℝ) : Set (Euc d) :=
  P.carrier ∩ {x | inner ℝ p.1 x = p.2}

/-- The part of the projected base where a constraint realizes the upper endpoint. -/
noncomputable def upperActiveRegion (e : Euc d) (he : e ≠ 0)
    (p : Euc d × ℝ) : Set (Euc d) :=
  {y | y ∈ P.projectedBase e he ∧
    planeParameter e y p = P.upperFiber e he y}

noncomputable def lowerActiveRegion (e : Euc d) (he : e ≠ 0)
    (p : Euc d × ℝ) : Set (Euc d) :=
  {y | y ∈ P.projectedBase e he ∧
    planeParameter e y p = P.lowerFiber e he y}

lemma isCompact_supportFace (p : Euc d × ℝ) :
    IsCompact (P.supportFace p) :=
  P.compact.inter_right (isClosed_eq (continuous_const.inner continuous_id) continuous_const)

lemma planeParameter_eq_iff {e y : Euc d} {p : Euc d × ℝ}
    (hn : inner ℝ p.1 e ≠ 0) (t : ℝ) :
    planeParameter e y p = t ↔ inner ℝ p.1 (y + t • e) = p.2 := by
  rw [planeParameter, div_eq_iff hn, inner_add_right, inner_smul_right]
  constructor <;> intro h <;> linarith

lemma upperEndpoint_mem_supportFace {e : Euc d} (he : e ≠ 0)
    {p : Euc d × ℝ} (hn : inner ℝ p.1 e ≠ 0) {y : Euc d}
    (hy : y ∈ P.upperActiveRegion e he p) :
    P.upperEndpoint e he y ∈ P.supportFace p := by
  refine ⟨(P.mem_line_iff he y _).mpr ⟨hy.1.2.1, hy.1.2.2, le_rfl⟩, ?_⟩
  exact (planeParameter_eq_iff hn _).mp hy.2

lemma lowerEndpoint_mem_supportFace {e : Euc d} (he : e ≠ 0)
    {p : Euc d × ℝ} (hn : inner ℝ p.1 e ≠ 0) {y : Euc d}
    (hy : y ∈ P.lowerActiveRegion e he p) :
    P.lowerEndpoint e he y ∈ P.supportFace p := by
  refine ⟨(P.mem_line_iff he y _).mpr ⟨hy.1.2.1, le_rfl, hy.1.2.2⟩, ?_⟩
  exact (planeParameter_eq_iff hn _).mp hy.2

lemma upperFiber_eq_lineParameter_of_mem_supportFace
    {e : Euc d} (he : e ≠ 0) {p : Euc d × ℝ}
    (hp : p ∈ P.halfspaces) (hn : 0 < inner ℝ p.1 e)
    {x : Euc d} (hx : x ∈ P.supportFace p) :
    P.upperFiber e he (hyperplaneProjection e x) = inner ℝ e x / inner ℝ e e := by
  have hline := (P.mem_line_iff he (hyperplaneProjection e x)
    (inner ℝ e x / inner ℝ e e)).mp
    (by simpa only [hyperplaneProjection_decomposition] using hx.1)
  have hparam : planeParameter e (hyperplaneProjection e x) p =
      inner ℝ e x / inner ℝ e e := by
    apply (planeParameter_eq_iff hn.ne' _).mpr
    rw [hyperplaneProjection_decomposition]
    exact hx.2
  have hup := (P.le_upperFiber_iff he (hyperplaneProjection e x)
    (P.upperFiber e he (hyperplaneProjection e x))).mp le_rfl p hp hn
  exact le_antisymm (hup.trans_eq hparam) hline.2.2

lemma lowerFiber_eq_lineParameter_of_mem_supportFace
    {e : Euc d} (he : e ≠ 0) {p : Euc d × ℝ}
    (hp : p ∈ P.halfspaces) (hn : inner ℝ p.1 e < 0)
    {x : Euc d} (hx : x ∈ P.supportFace p) :
    P.lowerFiber e he (hyperplaneProjection e x) = inner ℝ e x / inner ℝ e e := by
  have hline := (P.mem_line_iff he (hyperplaneProjection e x)
    (inner ℝ e x / inner ℝ e e)).mp
    (by simpa only [hyperplaneProjection_decomposition] using hx.1)
  have hparam : planeParameter e (hyperplaneProjection e x) p =
      inner ℝ e x / inner ℝ e e := by
    apply (planeParameter_eq_iff hn.ne _).mpr
    rw [hyperplaneProjection_decomposition]
    exact hx.2
  have hlo := (P.lowerFiber_le_iff he (hyperplaneProjection e x)
    (P.lowerFiber e he (hyperplaneProjection e x))).mp le_rfl p hp hn
  exact le_antisymm hline.2.1 (hparam.symm.trans_le hlo)

theorem upperEndpoint_projection_of_mem_supportFace
    {e : Euc d} (he : e ≠ 0) {p : Euc d × ℝ}
    (hp : p ∈ P.halfspaces) (hn : 0 < inner ℝ p.1 e)
    {x : Euc d} (hx : x ∈ P.supportFace p) :
    P.upperEndpoint e he (hyperplaneProjection e x) = x := by
  rw [upperEndpoint, P.upperFiber_eq_lineParameter_of_mem_supportFace he hp hn hx,
    hyperplaneProjection_decomposition]

theorem lowerEndpoint_projection_of_mem_supportFace
    {e : Euc d} (he : e ≠ 0) {p : Euc d × ℝ}
    (hp : p ∈ P.halfspaces) (hn : inner ℝ p.1 e < 0)
    {x : Euc d} (hx : x ∈ P.supportFace p) :
    P.lowerEndpoint e he (hyperplaneProjection e x) = x := by
  rw [lowerEndpoint, P.lowerFiber_eq_lineParameter_of_mem_supportFace he hp hn hx,
    hyperplaneProjection_decomposition]

/-- Projection identifies a positive supporting face exactly with its upper active region. -/
theorem project_supportFace_eq_upperActiveRegion
    {e : Euc d} (he : e ≠ 0) {p : Euc d × ℝ}
    (hp : p ∈ P.halfspaces) (hn : 0 < inner ℝ p.1 e) :
    hyperplaneProjection e '' P.supportFace p = P.upperActiveRegion e he p := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [P.projectedBase_eq_image he]
      exact ⟨x, hx.1, rfl⟩
    · apply (planeParameter_eq_iff hn.ne' _).mpr
      change inner ℝ p.1 (P.upperEndpoint e he (hyperplaneProjection e x)) = p.2
      rw [P.upperEndpoint_projection_of_mem_supportFace he hp hn hx]
      exact hx.2
  · intro hy
    exact ⟨P.upperEndpoint e he y, P.upperEndpoint_mem_supportFace he hn.ne' hy,
      P.project_upperEndpoint he hy.1⟩

theorem project_supportFace_eq_lowerActiveRegion
    {e : Euc d} (he : e ≠ 0) {p : Euc d × ℝ}
    (hp : p ∈ P.halfspaces) (hn : inner ℝ p.1 e < 0) :
    hyperplaneProjection e '' P.supportFace p = P.lowerActiveRegion e he p := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [P.projectedBase_eq_image he]
      exact ⟨x, hx.1, rfl⟩
    · apply (planeParameter_eq_iff hn.ne _).mpr
      change inner ℝ p.1 (P.lowerEndpoint e he (hyperplaneProjection e x)) = p.2
      rw [P.lowerEndpoint_projection_of_mem_supportFace he hp hn hx]
      exact hx.2
  · intro hy
    exact ⟨P.lowerEndpoint e he y, P.lowerEndpoint_mem_supportFace he hn.ne hy,
      P.project_lowerEndpoint he hy.1⟩

theorem supportFace_eq_upperEndpoint_image
    {e : Euc d} (he : e ≠ 0) {p : Euc d × ℝ}
    (hp : p ∈ P.halfspaces) (hn : 0 < inner ℝ p.1 e) :
    P.supportFace p = P.upperEndpoint e he '' P.upperActiveRegion e he p := by
  rw [← P.project_supportFace_eq_upperActiveRegion he hp hn, ← Set.image_comp]
  exact (Set.EqOn.image_eq_self (fun x hx =>
    P.upperEndpoint_projection_of_mem_supportFace he hp hn hx)).symm

theorem supportFace_eq_lowerEndpoint_image
    {e : Euc d} (he : e ≠ 0) {p : Euc d × ℝ}
    (hp : p ∈ P.halfspaces) (hn : inner ℝ p.1 e < 0) :
    P.supportFace p = P.lowerEndpoint e he '' P.lowerActiveRegion e he p := by
  rw [← P.project_supportFace_eq_lowerActiveRegion he hp hn, ← Set.image_comp]
  exact (Set.EqOn.image_eq_self (fun x hx =>
    P.lowerEndpoint_projection_of_mem_supportFace he hp hn hx)).symm

/-- Every nonempty fiber has at least one positive constraint at its upper endpoint. -/
theorem projectedBase_eq_iUnion_upperActiveRegion {e : Euc d} (he : e ≠ 0) :
    P.projectedBase e he = ⋃ p ∈ P.upperConstraints e, P.upperActiveRegion e he p := by
  ext y
  constructor
  · intro hy
    obtain ⟨p, hp, hn, hactive⟩ := P.exists_upperFiber_active he y
    exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr
      ⟨Finset.mem_filter.mpr ⟨hp, hn⟩, hy, (planeParameter_eq_iff hn.ne' _).mpr hactive⟩⟩
  · intro hy
    obtain ⟨p, _, h⟩ := Set.mem_iUnion₂.mp hy
    exact h.1

theorem projectedBase_eq_iUnion_lowerActiveRegion {e : Euc d} (he : e ≠ 0) :
    P.projectedBase e he = ⋃ p ∈ P.lowerConstraints e, P.lowerActiveRegion e he p := by
  ext y
  constructor
  · intro hy
    obtain ⟨p, hp, hn, hactive⟩ := P.exists_lowerFiber_active he y
    exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr
      ⟨Finset.mem_filter.mpr ⟨hp, hn⟩, hy, (planeParameter_eq_iff hn.ne _).mpr hactive⟩⟩
  · intro hy
    obtain ⟨p, _, h⟩ := Set.mem_iUnion₂.mp hy
    exact h.1

end ConvexPolytope
end BouRabeeGwynne
