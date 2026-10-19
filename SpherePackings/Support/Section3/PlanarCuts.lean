-- Built on Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne (commit cf73d6e).
import BouRabeeGwynne.Section3GoodLines

/-!
# Optimal cuts around a point of a line

If a set `Y` has one-dimensional measure at most `ℓ` (in the application `Y` is a set of points
of the line), every parameter `t₀` of a unit line lies between two parameters `a ≤ t₀ ≤ b` of points
of the line outside `Y` with `b - a ≤ ℓ + δ`, for any `δ > 0`: the maximal interval of bad parameters around `t₀` has length at
most `ℓ` (the rectangle construction in the proof of Theorem 3.3, `rw-spheres.tex:1063-1068`).
-/

namespace SpherePackings

open BouRabeeGwynne
open scoped MeasureTheory ENNReal

/-- **Optimal cuts.** -/
theorem exists_unitLine_cuts_around {d : ℕ} {u : Euc d} (hu : ‖u‖ = 1) (Y : Set (Euc d))
    {ℓ δ : ℝ} (hℓ : 0 ≤ ℓ) (hδ : 0 < δ) (hY : μHE[1] Y ≤ ENNReal.ofReal ℓ) (t₀ : ℝ) :
    ∃ a b : ℝ, a ≤ t₀ ∧ t₀ ≤ b ∧ b - a ≤ ℓ + δ ∧ a • u ∉ Y ∧ b • u ∉ Y := by
  -- the good parameters `t` (with `t • u ∉ Y`) on each side of `t₀`
  set G : Set ℝ := {t : ℝ | t • u ∉ Y}
  have hleft : (G ∩ Set.Iic t₀).Nonempty := by
    obtain ⟨t, ht, hgood⟩ := exists_unitLine_parameter_outside_of_bound hu Y hℓ hY
      (a := t₀ - ℓ - 1) (b := t₀) (by linarith)
    exact ⟨t, hgood, ht.2.le⟩
  have hright : (G ∩ Set.Ici t₀).Nonempty := by
    obtain ⟨t, ht, hgood⟩ := exists_unitLine_parameter_outside_of_bound hu Y hℓ hY
      (a := t₀) (b := t₀ + ℓ + 1) (by linarith)
    exact ⟨t, hgood, ht.1.le⟩
  have hleft_bdd : BddAbove (G ∩ Set.Iic t₀) := ⟨t₀, fun _ ht => ht.2⟩
  have hright_bdd : BddBelow (G ∩ Set.Ici t₀) := ⟨t₀, fun _ ht => ht.2⟩
  -- the nearest good parameters to `t₀` on the left and on the right
  set a₀ := sSup (G ∩ Set.Iic t₀)
  set b₀ := sInf (G ∩ Set.Ici t₀)
  have ha₀ : a₀ ≤ t₀ := csSup_le hleft (fun _ ht => ht.2)
  have hb₀ : t₀ ≤ b₀ := le_csInf hright (fun _ ht => ht.2)
  -- no good parameter lies strictly between `a₀` and `b₀`, so the bad gap is at most `ℓ`
  have hgap : b₀ - a₀ ≤ ℓ := by
    by_contra hcon
    obtain ⟨t, ht, hgood⟩ := exists_unitLine_parameter_outside_of_bound hu Y hℓ hY
      (a := a₀) (b := b₀) (not_le.mp hcon)
    rcases le_total t t₀ with h | h
    · have : t ≤ a₀ := le_csSup hleft_bdd (show t ∈ G ∩ Set.Iic t₀ from ⟨hgood, h⟩)
      linarith [ht.1]
    · have : b₀ ≤ t := csInf_le hright_bdd (show t ∈ G ∩ Set.Ici t₀ from ⟨hgood, h⟩)
      linarith [ht.2]
  -- approximate the two extremal parameters by good ones within `δ / 2`
  obtain ⟨a, ha, ha_lt⟩ := exists_lt_of_lt_csSup hleft (show a₀ - δ / 2 < a₀ by linarith)
  obtain ⟨b, hb, hb_lt⟩ := exists_lt_of_csInf_lt hright (show b₀ < b₀ + δ / 2 by linarith)
  exact ⟨a, b, ha.2, hb.2, by linarith, ha.1, hb.1⟩

end SpherePackings
