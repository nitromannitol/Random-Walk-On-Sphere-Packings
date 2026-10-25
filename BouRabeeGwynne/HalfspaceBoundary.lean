module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/HalfspaceBoundary.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.PaperObjects

@[expose] public section

namespace BouRabeeGwynne.ConvexPolytope

variable {d : ℕ} (P : ConvexPolytope d)

lemma mem_carrier_iff {x : Euc d} :
    x ∈ P.carrier ↔ ∀ p ∈ P.halfspaces, inner ℝ p.1 x ≤ p.2 := by
  rw [P.halfspace_rep]
  rfl

/-- A zero normal imposes only a true scalar inequality, since the polytope is
nonempty. Such a constraint must not be mistaken for a supporting facet. -/
lemma zero_normal_bound {p : Euc d × ℝ} (hp : p ∈ P.halfspaces) (hz : p.1 = 0) :
    0 ≤ p.2 := by
  obtain ⟨x, hx⟩ := P.interior_nonempty
  have h := P.mem_carrier_iff.mp (interior_subset hx) p hp
  simpa only [hz, inner_zero_left] using h

/-- Every genuine supporting inequality is strict at every interior point. -/
lemma inner_lt_of_mem_interior {p : Euc d × ℝ} (hp : p ∈ P.halfspaces)
    (hn : p.1 ≠ 0) {x : Euc d} (hx : x ∈ interior P.carrier) :
    inner ℝ p.1 x < p.2 := by
  let f : Euc d →L[ℝ] ℝ := innerSL ℝ p.1
  have hf : f ≠ 0 := by
    intro hf
    have hz := congrArg (fun g : Euc d →L[ℝ] ℝ => g p.1) hf
    change inner ℝ p.1 p.1 = 0 at hz
    exact (real_inner_self_pos.mpr hn).ne' hz
  have hsub : f '' interior P.carrier ⊆ Set.Iic p.2 := by
    rintro y ⟨z, hz, rfl⟩
    exact P.mem_carrier_iff.mp (interior_subset hz) p hp
  have hi := interior_maximal hsub (f.isOpenMap_of_ne_zero hf _ isOpen_interior)
  have h := hi (Set.mem_image_of_mem f hx)
  simpa only [interior_Iic, Set.mem_Iio, f, innerSL_apply_apply] using h

/-- The interior is characterized by strict nonzero supporting inequalities,
without assuming that the supplied halfspace representation is irredundant. -/
theorem mem_interior_iff {x : Euc d} :
    x ∈ interior P.carrier ↔
      ∀ p ∈ P.halfspaces, p.1 ≠ 0 → inner ℝ p.1 x < p.2 := by
  classical
  constructor
  · intro hx p hp hn
    exact P.inner_lt_of_mem_interior hp hn hx
  · intro hx
    let S : Set (Euc d) := ⋂ p ∈ P.halfspaces,
      {y | p.1 ≠ 0 → inner ℝ p.1 y < p.2}
    have hS : IsOpen S := by
      apply isOpen_biInter_finset
      intro p _
      by_cases hp : p.1 = 0
      · simp [hp]
      · simpa only [Ne, hp, not_false_eq_true, true_implies] using
          (isOpen_lt (continuous_const.inner continuous_id) continuous_const :
            IsOpen {y : Euc d | inner ℝ p.1 y < p.2})
    have hxS : x ∈ S := Set.mem_iInter₂.mpr hx
    have hSP : S ⊆ P.carrier := by
      intro y hy
      apply P.mem_carrier_iff.mpr
      intro p hp
      by_cases hn : p.1 = 0
      · simpa only [hn, inner_zero_left] using P.zero_normal_bound hp hn
      · exact ((Set.mem_iInter₂.mp hy p hp) hn).le
    exact interior_maximal hSP hS hxS

/-- Boundary points are precisely points where a nonzero supporting constraint
is active. Lower-dimensional slices and duplicate constraints remain explicit. -/
theorem mem_frontier_iff {x : Euc d} :
    x ∈ frontier P.carrier ↔ x ∈ P.carrier ∧
      ∃ p ∈ P.halfspaces, p.1 ≠ 0 ∧ inner ℝ p.1 x = p.2 := by
  classical
  constructor
  · intro hx
    have hxP := P.compact.isClosed.frontier_subset hx
    refine ⟨hxP, ?_⟩
    by_contra hno
    apply hx.2
    apply P.mem_interior_iff.mpr
    intro p hp hn
    have hle := P.mem_carrier_iff.mp hxP p hp
    apply lt_of_le_of_ne hle
    intro heq
    exact hno ⟨p, hp, hn, heq⟩
  · rintro ⟨hxP, p, hp, hn, heq⟩
    refine ⟨subset_closure hxP, ?_⟩
    intro hx
    exact (P.inner_lt_of_mem_interior hp hn hx).ne heq

end BouRabeeGwynne.ConvexPolytope
