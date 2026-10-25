module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/RadialBoundary.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.FiberEndpoints
public import Mathlib.Analysis.Convex.Segment

@[expose] public section

namespace BouRabeeGwynne.ConvexPolytope

variable {d : ℕ} (P : ConvexPolytope d)

/-- A ray through any cell point distinct from its anchor reaches an actual
boundary point beyond that cell point. The finite-halfspace upper endpoint
supplies the witness, including rays from anchors outside the cell. -/
theorem exists_frontier_segment {a x : Euc d} (hx : x ∈ P.carrier) (hxa : x ≠ a) :
    ∃ b ∈ frontier P.carrier, x ∈ segment ℝ a b := by
  have he : x - a ≠ 0 := sub_ne_zero.mpr hxa
  have hline : a + (1 : ℝ) • (x - a) ∈ P.carrier := by simpa using hx
  have hb := (P.mem_line_iff he a 1).mp hline
  let u := P.upperFiber (x - a) he a
  have hu : 1 ≤ u := hb.2.2
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  refine ⟨a + u • (x - a),
    P.upperFiber_mem_frontier he a hb.1 (hb.2.1.trans hb.2.2), ?_⟩
  rw [segment_eq_image']
  refine ⟨1 / u, ⟨by positivity, (div_le_one₀ hu0).mpr hu⟩, ?_⟩
  simp only [add_sub_cancel_left, smul_smul, one_div,
    inv_mul_cancel₀ hu0.ne', one_smul, add_sub_cancel]

end BouRabeeGwynne.ConvexPolytope
