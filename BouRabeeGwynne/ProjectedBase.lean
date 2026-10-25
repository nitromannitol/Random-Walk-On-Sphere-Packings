module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/ProjectedBase.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.FiberEndpoints

@[expose] public section

namespace BouRabeeGwynne

/-- Orthogonal projection onto the hyperplane perpendicular to `e`, written as
an actual continuous linear map. The main geometric uses have `e ≠ 0`. -/
noncomputable def hyperplaneProjection {d : ℕ} (e : Euc d) : Euc d →L[ℝ] Euc d :=
  ContinuousLinearMap.id ℝ (Euc d) -
    (innerSL ℝ e).smulRight ((inner ℝ e e)⁻¹ • e)

lemma hyperplaneProjection_apply {d : ℕ} (e x : Euc d) :
    hyperplaneProjection e x = x - (inner ℝ e x / inner ℝ e e) • e := by
  simp only [hyperplaneProjection, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, smul_smul, div_eq_mul_inv]

lemma inner_hyperplaneProjection {d : ℕ} {e : Euc d} (he : e ≠ 0) (x : Euc d) :
    inner ℝ e (hyperplaneProjection e x) = 0 := by
  have hn := (real_inner_self_pos.mpr he).ne'
  rw [hyperplaneProjection_apply, inner_sub_right, inner_smul_right,
    div_mul_cancel₀ _ hn, sub_self]

lemma hyperplaneProjection_self {d : ℕ} {e : Euc d} (he : e ≠ 0) :
    hyperplaneProjection e e = 0 := by
  rw [hyperplaneProjection_apply, div_self (real_inner_self_pos.mpr he).ne',
    one_smul, sub_self]

lemma hyperplaneProjection_eq_self {d : ℕ} (e : Euc d) {y : Euc d}
    (hy : inner ℝ e y = 0) : hyperplaneProjection e y = y := by
  rw [hyperplaneProjection_apply, hy, zero_div, zero_smul, sub_zero]

lemma hyperplaneProjection_add_smul {d : ℕ} {e : Euc d} (he : e ≠ 0)
    (y : Euc d) (t : ℝ) :
    hyperplaneProjection e (y + t • e) = hyperplaneProjection e y := by
  rw [map_add, map_smul, hyperplaneProjection_self he, smul_zero, add_zero]

namespace ConvexPolytope

variable {d : ℕ} (P : ConvexPolytope d)

/-- The exact base of the nonempty line fibers, on the perpendicular hyperplane. -/
noncomputable def projectedBase (e : Euc d) (he : e ≠ 0) : Set (Euc d) :=
  {y | inner ℝ e y = 0 ∧ P.parallelConstraintsHold e y ∧
    P.lowerFiber e he y ≤ P.upperFiber e he y}

/-- The finite-halfspace feasibility definition of the base agrees with the
actual orthogonal image of the cell. No polytope projection theorem is assumed. -/
theorem projectedBase_eq_image {e : Euc d} (he : e ≠ 0) :
    P.projectedBase e he = hyperplaneProjection e '' P.carrier := by
  ext y
  constructor
  · rintro ⟨hy, hparallel, hbounds⟩
    have hp : y + P.lowerFiber e he y • e ∈ P.carrier :=
      (P.mem_line_iff he y _).mpr ⟨hparallel, le_rfl, hbounds⟩
    refine ⟨y + P.lowerFiber e he y • e, hp, ?_⟩
    rw [hyperplaneProjection_add_smul he, hyperplaneProjection_eq_self e hy]
  · rintro ⟨x, hx, rfl⟩
    have hline : hyperplaneProjection e x + (inner ℝ e x / inner ℝ e e) • e ∈
        P.carrier := by
      simpa only [hyperplaneProjection_apply, sub_add_cancel] using hx
    have h := (P.mem_line_iff he (hyperplaneProjection e x) _).mp hline
    exact ⟨inner_hyperplaneProjection he x, h.1, h.2.1.trans h.2.2⟩

theorem isCompact_projectedBase {e : Euc d} (he : e ≠ 0) :
    IsCompact (P.projectedBase e he) := by
  rw [P.projectedBase_eq_image he]
  exact P.compact.image (hyperplaneProjection e).continuous

theorem projectedBase_nonempty {e : Euc d} (he : e ≠ 0) :
    (P.projectedBase e he).Nonempty := by
  rw [P.projectedBase_eq_image he]
  exact (P.interior_nonempty.mono interior_subset).image _

theorem upperEndpoint_mem_frontier {e : Euc d} (he : e ≠ 0) {y : Euc d}
    (hy : y ∈ P.projectedBase e he) : P.upperEndpoint e he y ∈ frontier P.carrier :=
  P.upperFiber_mem_frontier he y hy.2.1 hy.2.2

theorem lowerEndpoint_mem_frontier {e : Euc d} (he : e ≠ 0) {y : Euc d}
    (hy : y ∈ P.projectedBase e he) : P.lowerEndpoint e he y ∈ frontier P.carrier :=
  P.lowerFiber_mem_frontier he y hy.2.1 hy.2.2

theorem project_upperEndpoint {e : Euc d} (he : e ≠ 0) {y : Euc d}
    (hy : y ∈ P.projectedBase e he) :
    hyperplaneProjection e (P.upperEndpoint e he y) = y := by
  rw [upperEndpoint, hyperplaneProjection_add_smul he, hyperplaneProjection_eq_self e hy.1]

theorem project_lowerEndpoint {e : Euc d} (he : e ≠ 0) {y : Euc d}
    (hy : y ∈ P.projectedBase e he) :
    hyperplaneProjection e (P.lowerEndpoint e he y) = y := by
  rw [lowerEndpoint, hyperplaneProjection_add_smul he, hyperplaneProjection_eq_self e hy.1]

end ConvexPolytope
end BouRabeeGwynne
