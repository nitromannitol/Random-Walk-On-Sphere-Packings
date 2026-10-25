module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/ExteriorBallBuffer.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.LipschitzUniformExteriorBalls
public import Mathlib.Topology.MetricSpace.Thickening

@[expose] public section

/-! A smaller concentric part of an exterior ball lies strictly outside a
closed collar of the domain. This supplies a buffer for the stopping comparison. -/

open Set Metric

namespace BouRabeeGwynne

lemma closedBall_subset_compl_cthickening_of_exteriorBall {d : ℕ}
    {U : Set (Euc d)} {c : Euc d} {R δ : ℝ} (hR : 0 < R)
    (hext : closedBall c R ⊆ Uᶜ) (hδ : δ < R / 2) :
    closedBall c (R / 2) ⊆ (cthickening δ U)ᶜ := by
  intro y hy hcollar
  obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.mp
    (cthickening_subset_iUnion_closedBall_of_lt U (half_pos hR) hδ hcollar)
  apply hext (show z ∈ closedBall c R from ?_) hz
  calc
    dist z c ≤ dist z y + dist y c := dist_triangle _ _ _
    _ ≤ R / 2 + R / 2 := add_le_add (by simpa only [mem_closedBall, dist_comm] using hyz) hy
    _ = R := by ring

theorem HasLipschitzBoundary.exists_uniform_buffered_exterior_balls {d : ℕ}
    {U : Set (Euc d)} (hL : HasLipschitzBoundary U)
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) :
    ∃ s > 0, ∃ κ > 0, κ ≤ 1 ∧
      ∀ p ∈ frontier U, ∀ r : ℝ, 0 < r → r < s →
        ∃ c : Euc d, dist c p = r ∧
          ∀ δ : ℝ, δ < κ * r / 2 →
            closedBall c (κ * r / 2) ⊆ (cthickening δ U)ᶜ := by
  obtain ⟨s, hs, κ, hκ, hκone, hballs⟩ :=
    hL.exists_uniform_exterior_balls hU hUb
  refine ⟨s, hs, κ, hκ, hκone, ?_⟩
  intro p hp r hr hrs
  obtain ⟨c, hc, hext⟩ := hballs p hp r hr hrs
  exact ⟨c, hc, fun δ hδ =>
    closedBall_subset_compl_cthickening_of_exteriorBall (mul_pos hκ hr) hext hδ⟩

end BouRabeeGwynne
