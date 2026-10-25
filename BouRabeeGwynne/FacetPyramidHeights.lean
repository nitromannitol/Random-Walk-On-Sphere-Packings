module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/FacetPyramidHeights.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.PyramidSlices
public import BouRabeeGwynne.FacetNormals

@[expose] public section

namespace BouRabeeGwynne

lemma perpendicularSlice_reverse {d : ℕ} (a e : Euc d) (r : ℝ) :
    perpendicularSlice (a + e) (-e) (1 - r) = perpendicularSlice a e r := by
  ext z
  simp only [mem_perpendicularSlice, inner_neg_left, inner_neg_right, neg_neg,
    inner_sub_right, inner_add_right]
  constructor <;> intro h <;> nlinarith

namespace OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

/-- Orthogonality and the strict interior positions put each actual contact at
a unique fractional height strictly between its two marked vertices. -/
theorem exists_facet_height (hd : 1 ≤ d) {v w : T.V} (hvw : T.adj v w) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      T.facet v w ⊆ perpendicularSlice (T.pos v) (T.pos w - T.pos v) r := by
  obtain ⟨z, hz⟩ := hvw.2.1
  let e := T.pos w - T.pos v
  have he : e ≠ 0 := sub_ne_zero.mpr (T.toTilingData.pos_injective.ne hvw.1.symm)
  have hq : 0 < inner ℝ e e := real_inner_self_pos.mpr he
  have hsep := T.facet_normal_separation hd hvw hz
  have hb : 0 < inner ℝ e (z - T.pos v) := by
    have h := hsep.2.2.1
    change inner ℝ e (T.pos v - z) < 0 at h
    simp only [inner_sub_right] at h ⊢
    linarith
  have hupper : inner ℝ e (z - T.pos v) < inner ℝ e e := by
    have h := hsep.2.2.2
    change 0 < inner ℝ e (T.pos w - z) at h
    have hid : inner ℝ e e =
        inner ℝ e (T.pos w - z) + inner ℝ e (z - T.pos v) := by
      change inner ℝ e (T.pos w - T.pos v) = _
      simp only [inner_sub_right]
      ring
    linarith
  let r := inner ℝ e (z - T.pos v) / inner ℝ e e
  refine ⟨r, div_pos hb hq, (div_lt_one hq).mpr hupper, ?_⟩
  intro y hy
  change y ∈ perpendicularSlice (T.pos v) e r
  rw [mem_perpendicularSlice]
  have horth := T.orthogonal hvw hy hz
  change inner ℝ e (y - z) = 0 at horth
  have hheight : inner ℝ e (y - T.pos v) = inner ℝ e (z - T.pos v) := by
    simp only [inner_sub_right] at horth ⊢
    linarith
  change inner ℝ e (y - T.pos v) = r * inner ℝ e e
  dsimp only [r]
  rw [div_mul_cancel₀ _ hq.ne']
  exact hheight

end OrthogonalTiling
end BouRabeeGwynne
