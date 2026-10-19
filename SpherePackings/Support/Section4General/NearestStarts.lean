-- Built on Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne (commit cf73d6e).
import SpherePackings.Support.Section4General.AssumptionD
import BouRabeeGwynne.FixedBallCover

/-!
# Nearby starts for the coupling

By (4.1), the chosen vertex `z^n` is uniformly close to `z` on bounded parts of the
`δ`-neighbourhood of `D`.  So for a cover by balls `B_{r/4}(c)`, every `z ∈ U` and its vertex `z^n`
eventually lie in a common ball `B_{r/2}(c)`, at distance at most any prescribed `δ₀`.
-/

open Metric Filter Set
open BouRabeeGwynne

namespace SpherePackings

variable {d : ℕ}

/-- (4.1) on a bounded part of the `δ`-neighbourhood of `D`, uniformly. -/
theorem eventually_near_dist_le (W : ℕ → NearestNeighbourWalk d) (near : ∀ n, Euc d → (W n).V)
    {D : Set (Euc d)} {δ : ℝ} (hAD : AssumptionD W near D δ) {S : Set (Euc d)}
    (hSb : Bornology.IsBounded S) (hSD : S ⊆ cthickening δ D) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n in atTop, ∀ z ∈ S, dist ((near n z : Euc d)) z ≤ η := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨c, hc⟩
  · exact Eventually.of_forall fun n z hz => hz.elim
  obtain ⟨R, hR, hSR⟩ := hSb.subset_ball_lt 0 c
  obtain ⟨-, -, hAD'⟩ := hAD
  obtain ⟨happrox, -⟩ := hAD' R hR c (hSD hc)
  filter_upwards [happrox η hη] with n hn z hz
  exact hn z ⟨ball_subset_closedBall (hSR hz), hSD hz⟩

/-- **Nearby coupling starts.** -/
theorem eventually_near_coupling_starts (W : ℕ → NearestNeighbourWalk d)
    (near : ∀ n, Euc d → (W n).V) {D : Set (Euc d)} {δ : ℝ} (hAD : AssumptionD W near D δ)
    {U : Set (Euc d)} (hUb : Bornology.IsBounded U) (hUD : U ⊆ cthickening δ D)
    (centers : Finset (Euc d)) {r δ₀ : ℝ} (hr : 0 < r) (hδ₀ : 0 < δ₀)
    (hcover : ∀ z ∈ U, ∃ c ∈ centers, z ∈ ball c (r / 4)) :
    ∀ᶠ n in atTop, ∀ z ∈ U, ∃ j : centers,
      ((near n z : (W n).V) : Euc d) ∈ closedBall j.val (r / 2) ∧
      z ∈ closedBall j.val (r / 2) ∧ dist ((near n z : Euc d)) z ≤ δ₀ := by
  filter_upwards [eventually_near_dist_le W near hAD hUb hUD
    (lt_min hδ₀ (by positivity : 0 < r / 4))] with n hn z hz
  obtain ⟨c, hc, hzc⟩ := hcover z hz
  have hnear := hn z hz
  have hx : ((near n z : (W n).V) : Euc d) ∈ ball c (r / 2) :=
    near_cover_point_mem_inner_ball hzc (hnear.trans (min_le_right _ _))
  exact ⟨⟨c, hc⟩, ball_subset_closedBall hx,
    ball_subset_closedBall (ball_subset_ball (by linarith : r / 4 ≤ r / 2) hzc),
    hnear.trans (min_le_left _ _)⟩

end SpherePackings
