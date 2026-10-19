-- Built on Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne (commit cf73d6e).
import SpherePackings.Support.Guards.TilingWalk
import SpherePackings.Support.Guards.LatticeTilings
import SpherePackings.Support.Section4General.AssumptionD
import BouRabeeGwynne.Section3TheoremBPartA
import BouRabeeGwynne.ApproximationGeometry
import BouRabeeGwynne.EuclideanWienerLaw
import SpherePackings.Support.Guards.LipschitzBall

/-!
# Assumption D is satisfiable

The conductance walks on the Voronoi tilings of the lattices `(n+1)⁻¹ ℤ^d` (restricted to the ball
of radius `2`), with nearest vertices, satisfy Assumption D as printed (`AssumptionD`) for the unit
ball and some `δ > 0`: (4.1) is the approximation condition (1.3), and (4.2) is Theorem B(a)
(leobon12) for the convex domains `interior (B_r(x) ∩ B_δ(D))`.  So the hypotheses of Theorem 4.1
and Proposition 4.2 are not vacuous.
-/

open MeasureTheory Metric Filter Set
open BouRabeeGwynne BouRabeeGwynne.OrthogonalTiling

namespace SpherePackings

variable {d : ℕ}

/-- A point of `B_r(x) ∩ B_ρ(0)` in the interior, for `x ∈ closedBall 0 ρ`. -/
private lemma exists_mem_ball_inter_ball {x : Euc d} {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (hx : ‖x‖ ≤ ρ) : ∃ y, y ∈ ball x r ∧ y ∈ ball (0 : Euc d) ρ := by
  set s := r / (2 * (‖x‖ + r)) with hsdef
  have hden : 0 < 2 * (‖x‖ + r) := by positivity
  have hs0 : 0 < s := div_pos hr hden
  have hs1 : s ≤ 1 / 2 := by
    rw [hsdef, div_le_iff₀ hden]
    nlinarith [norm_nonneg x]
  refine ⟨(1 - s) • x, ?_, ?_⟩
  · rw [mem_ball, dist_eq_norm, show (1 - s) • x - x = (-s) • x by module, norm_smul,
      Real.norm_eq_abs, abs_neg, abs_of_pos hs0]
    have : s * ‖x‖ = r * ‖x‖ / (2 * (‖x‖ + r)) := by rw [hsdef]; ring
    rw [this, div_lt_iff₀ hden]
    nlinarith [norm_nonneg x]
  · rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
    rcases (norm_nonneg x).eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero]
      exact hρ
    · have : (1 - s) * ‖x‖ < ‖x‖ := by nlinarith
      linarith

/-- **Assumption D is satisfiable.** -/
theorem exists_walks_assumptionD (hd : 1 ≤ d) :
    ∃ (W : ℕ → NearestNeighbourWalk d) (near : ∀ n, Euc d → (W n).V) (δ : ℝ),
      (∀ n, (W n).IsNearestVertex (near n)) ∧ AssumptionD W near (ball (0 : Euc d) 1) δ := by
  classical
  obtain ⟨G, hcollar, ⟨N⟩, happrox, hII, hfin⟩ := exists_lattice_tilingSequence_finite hd
  have : ∀ n, Countable (G.tiling n).V := fun n => by
    have := hfin n
    infer_instance
  let W : ℕ → NearestNeighbourWalk d := fun n => conductanceWalk (G.tiling n)
  -- nearest vertices in the finite vertex sets
  have hnearest : ∀ n (z : Euc d), ∃ v : (G.tiling n).V,
      ∀ w, dist ((G.tiling n).pos v) z ≤ dist ((G.tiling n).pos w) z := by
    intro n z
    have := hfin n
    have : Nonempty (G.tiling n).V := ⟨N.vertex n 0⟩
    exact Finite.exists_min (fun v : (G.tiling n).V => dist ((G.tiling n).pos v) z)
  choose v₀ hv₀ using hnearest
  let near : ∀ n, Euc d → (W n).V := fun n z => tilingEquiv (G.tiling n) (v₀ n z)
  -- the margin `δ`
  have hball : closedBall (0 : Euc d) 1 ⊆ interior G.domain := by
    have := hcollar
    unfold HasAmbientCollar at this
    rwa [closure_ball (0 : Euc d) one_ne_zero] at this
  obtain ⟨δ₀, hδ₀, hδ₀sub⟩ :=
    (isCompact_closedBall (0 : Euc d) 1).exists_cthickening_subset_open isOpen_interior hball
  set δ := δ₀ / 2 with hδdef
  have hδ : 0 < δ := half_pos hδ₀
  have hK : cthickening δ (ball (0 : Euc d) 1) = closedBall (0 : Euc d) (δ + 1) :=
    cthickening_ball hδ.le one_pos 0
  have hKsub : closedBall (0 : Euc d) (δ + 1) ⊆ interior G.domain := by
    rw [← hK]
    exact (cthickening_mono (by linarith) _).trans
      ((cthickening_subset_of_subset _ ball_subset_closedBall).trans hδ₀sub)
  refine ⟨W, near, δ, fun n z v => ?_, ?_⟩
  · -- nearest vertices
    obtain ⟨a, rfl⟩ := (tilingEquiv (G.tiling n)).surjective v
    exact hv₀ n z a
  refine ⟨⟨isOpen_ball, ⟨0, mem_ball_self one_pos⟩, (convex_ball _ _).isPreconnected⟩, hδ, ?_⟩
  intro r hr x hx
  rw [hK] at hx ⊢
  have hBsub : closedBall x r ∩ closedBall (0 : Euc d) (δ + 1) ⊆ G.domain :=
    fun z hz => interior_subset (hKsub hz.2)
  refine ⟨fun η hη => ?_, fun h hO η hη => ?_⟩
  · -- (4.1)
    filter_upwards [N.eventually_vertex_dist_le (happrox N) hη] with n hn z hz
    exact (hv₀ n z (N.vertex n z)).trans (hn z (hBsub hz))
  · -- (4.2), from Theorem B(a) on the interior of the region
    obtain ⟨O, hOopen, hBO, hhO⟩ := hO
    set B := closedBall x r ∩ closedBall (0 : Euc d) (δ + 1) with hBdef
    set U := interior B with hUdef
    have hBclosed : IsClosed B := isClosed_closedBall.inter isClosed_closedBall
    have hclosU : closure U ⊆ B := closure_minimal interior_subset hBclosed
    have hUdomain : IsDomain U := by
      refine ⟨isOpen_interior, ?_, ((convex_closedBall x r).inter
        (convex_closedBall 0 (δ + 1))).interior.isPreconnected⟩
      obtain ⟨y, hy1, hy2⟩ := exists_mem_ball_inter_ball hr (by linarith)
        (mem_closedBall_zero_iff.mp hx)
      refine ⟨y, ?_⟩
      rw [hUdef, hBdef, interior_inter, interior_closedBall x hr.ne',
        interior_closedBall 0 (by linarith : δ + 1 ≠ 0)]
      exact ⟨hy1, hy2⟩
    have htarget := theoremB_part_a d G N U h hd hUdomain
      (isBounded_closedBall.subset (interior_subset.trans inter_subset_right))
      (show closure U ⊆ interior G.domain from hclosU.trans (fun z hz => hKsub hz.2))
      (happrox N) (Or.inr (Or.inl hII)) ⟨O, hOopen, hclosU.trans hBO, hhO⟩
    filter_upwards [htarget.2 η hη] with n hn
    intro hD hsol z hz
    let T := G.tiling n
    let e := tilingEquiv T
    obtain ⟨a, rfl⟩ := e.surjective z
    have := hfin n
    have hsolT : T.SolvesDirichlet U (fun v => h (T.pos v)) (fun v => hD (e v)) := by
      refine ⟨fun v hv => ⟨Set.toFinite _, ?_⟩, fun w hw => ?_⟩
      · exact discreteLaplacian_eq_zero_of_isHarmonicAt T (Set.toFinite _)
          (hsol.1 (e v) ((conductanceWalk_inner T B v).mpr hv))
      · exact hsol.2 (e w) ((conductanceWalk_boundary T B w).mpr hw)
    exact hn (fun v => hD (e v)) hsolT a ((conductanceWalk_inner T B a).mp hz)

/-- **The hypotheses of Theorem 4.1 are satisfiable**: lattice walks with nearest vertices, Assumption
D for the unit ball, the unit ball as the bounded Lipschitz domain `U ⊆ D`, and a standard Brownian
law. -/
theorem theorem41_hypotheses_satisfiable (hd : 1 ≤ d) :
    ∃ (W : ℕ → NearestNeighbourWalk d) (near : ∀ n, Euc d → (W n).V) (δ : ℝ)
      (μ : Measure (BrownianPath d)),
      (∀ n, (W n).IsNearestVertex (near n)) ∧ AssumptionD W near (ball (0 : Euc d) 1) δ ∧
      IsLipschitzDomain (ball (0 : Euc d) 1) ∧ Bornology.IsBounded (ball (0 : Euc d) 1) ∧
      IsStandardBrownianLaw μ := by
  obtain ⟨W, near, δ, hnear, hAD⟩ := exists_walks_assumptionD hd
  exact ⟨W, near, δ, euclideanWienerLaw d, hnear, hAD, isLipschitzDomain_ball hd, isBounded_ball,
    isStandardBrownianLaw_euclideanWienerLaw d⟩

end SpherePackings
