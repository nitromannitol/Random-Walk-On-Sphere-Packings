-- Built on Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne (commit cf73d6e).
import SpherePackings.General.Walk.WalkSkeletonPrefix
import BouRabeeGwynne.PolygonalVertexExitGeometry
import BouRabeeGwynne.ExcursionOscillation
import BouRabeeGwynne.SelectedExcursionOscillation
import SpherePackings.General.Walk.GoodRange

/-!
# Walk steps from excursion ranges

Every excursion of the walk from a selected ball `B_r(c_j)` stays within `max (2 r) |end - start|`
of its start, and before the clock of stage `n`, every step of the walk is a step inside one of the excursions
`0, …, n`, and both of its endpoints are vertices of that excursion.  So if every excursion stays
within `R` of its start, every step before that clock has length at most `2 R`.  This replaces a
deterministic step bound of the walk, which general nearest-neighbour walks do not have.
-/

open MeasureTheory Set
open scoped unitInterval

namespace SpherePackings.MarkovChain

open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork

variable {d : ℕ}

/-- Every vertex of a clocked excursion, up to its duration, lies on its curve. -/
lemma ClockedWalkExcursion.exists_curve_eq_vertex (e : ClockedWalkExcursion d) {j : ℕ}
    (hj : j ≤ e.1) : ∃ t, ClockedWalkExcursion.curve e t = e.2 j := by
  refine ⟨⟨(j : ℝ) / e.1, div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
    div_le_one_of_le₀ (Nat.cast_le.mpr hj) (Nat.cast_nonneg _)⟩, ?_⟩
  apply polygonalCurve_at_scaled_vertex id e.2 hj
  change (e.1 : ℝ) * ((j : ℝ) / e.1) = j
  rcases Nat.eq_zero_or_pos e.1 with h | h
  · have hj0 : j = 0 := Nat.eq_zero_of_le_zero (h ▸ hj)
    simp [h, hj0]
  · field_simp

/-- A vertex of an excursion in `curveOscillationLe R` is within `R` of its start. -/
lemma ClockedWalkExcursion.dist_vertex_le (e : ClockedWalkExcursion d) {R : ℝ}
    (hR : ClockedWalkExcursion.curve e ∈ curveOscillationLe R) {j : ℕ} (hj : j ≤ e.1) :
    dist (e.2 j) (e.2 0) ≤ R := by
  obtain ⟨t, ht⟩ := ClockedWalkExcursion.exists_curve_eq_vertex e hj
  have h := hR t
  rwa [ht, ClockedWalkExcursion.curve_start] at h

variable {V J : Type*} [MeasurableSpace V] [MeasurableEq V] [Countable J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

/-- **Steps before a stage clock.**  If the excursions `0, …, n` of the walk stay within `R` of
their starts, every step before the clock of stage `n` has length at most `2 R`. -/
theorem actualWalkStage_step_le_of_range (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → V → Option J) (n : ℕ) (ω : ℕ → V)
    (hfinite : (actualWalkStage pos B initial select n ω).1 ≠ ⊤) {R : ℝ}
    (hR : ∀ i ≤ n, ClockedWalkExcursion.curve (actualWalkStage pos B initial select i ω).2.2 ∈
      curveOscillationLe R) :
    ∀ k < (actualWalkStage pos B initial select n ω).1.untopD 0,
      dist (pos (ω (k + 1))) (pos (ω k)) ≤ 2 * R := by
  intro k hk
  let c : ℕ → ℕ := fun i => (actualWalkStage pos B initial select i ω).1.untopD 0
  have hmono : ∀ i j, i ≤ j → j ≤ n → c i ≤ c j := fun i j hij hjn =>
    WithTop.untopD_mono (actualWalkStage_clock_finite_of_le pos B initial select ω hjn hfinite)
      (actualWalkStage_clock_mono pos B initial select ω hij)
  have hex : ∃ i, k < c i := ⟨n, hk⟩
  classical
  set i := Nat.find hex with hi
  have hin : i ≤ n := Nat.find_min' hex hk
  have hki : k < c i := Nat.find_spec hex
  -- the start time of the excursion of stage `i`
  let p : ℕ := Nat.casesOn (motive := fun _ => ℕ) i 0 (fun j => c j)
  have hpk : p ≤ k := by
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · simp only [p, h0]; exact Nat.zero_le k
    · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      have hnot : ¬ k < c j := Nat.find_min hex (by omega)
      simp only [p, hj]
      omega
  have hseg : (actualWalkStage pos B initial select i ω).2.2 = clockedWalkSegment pos ω p (c i) := by
    have h := actualWalkStage_eq_segment_times pos B initial select n ω hfinite
      ⟨i, Nat.lt_succ_of_le hin⟩
    rw [h]
    congr 1
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · simp only [p, h0]; rfl
    · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      simp only [p, hj]
      rfl
  have hRi := hR i hin
  rw [hseg] at hRi
  have h1 := ClockedWalkExcursion.dist_vertex_le _ hRi (j := k + 1 - p)
    (by simp only [clockedWalkSegment]; omega)
  have h0 := ClockedWalkExcursion.dist_vertex_le _ hRi (j := k - p)
    (by simp only [clockedWalkSegment]; omega)
  simp only [clockedWalkSegment] at h1 h0
  rw [Nat.min_eq_left (by omega), Nat.add_sub_cancel' (by omega)] at h1 h0
  calc dist (pos (ω (k + 1))) (pos (ω k))
      ≤ dist (pos (ω (k + 1))) (pos (ω (p + min 0 (c i - p)))) +
          dist (pos (ω k)) (pos (ω (p + min 0 (c i - p)))) := dist_triangle_right _ _ _
    _ ≤ R + R := add_le_add h1 h0
    _ = 2 * R := by ring

/-- **Shape of the actual excursions.**  If every state of `B j` sits in the ball `B_r(c j)`, the
selectors only select balls containing the current position and the walk starts in the initial
ball, then every excursion with a finite clock stays within `max (2 r) |end - start|` of its start. -/
theorem actualWalkStage_shape (pos : V → Euc d) (B : J → Set V) (initial : J)
    (select : ℕ → V → Option J) (c : J → Euc d) {r : ℝ}
    (hBc : ∀ j, ∀ v ∈ B j, pos v ∈ Metric.ball (c j) r)
    (hsel : ∀ i v j, select i v = some j → pos v ∈ Metric.ball (c j) r)
    (ω : ℕ → V) (h0 : pos (ω 0) ∈ Metric.ball (c initial) r) (n : ℕ)
    (hfinite : (actualWalkStage pos B initial select n ω).1 ≠ ⊤) (t : unitInterval) :
    dist (ClockedWalkExcursion.curve (actualWalkStage pos B initial select n ω).2.2 t)
        (ClockedWalkExcursion.curve (actualWalkStage pos B initial select n ω).2.2 0) ≤
      max (2 * r) (dist (ClockedWalkExcursion.curve (actualWalkStage pos B initial select n ω).2.2 1)
        (ClockedWalkExcursion.curve (actualWalkStage pos B initial select n ω).2.2 0)) := by
  cases n with
  | zero => exact curve_ofWalk_shape (hBc initial) ω h0 t
  | succ k =>
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp
      (actualWalkStage_clock_finite_of_le pos B initial select ω (Nat.le_succ k) hfinite)
    let τ := fun ξ => (actualWalkStage pos B initial select k ξ).1
    let choice := walkStageSelector (actualWalkStage pos B initial select k) (select k)
    have hk : τ ω = m := hm.symm
    have hlast : (observedHistory τ ω).2 (observedHistory τ ω).1 = ω m := by
      rw [observedHistory_of_eq hk]
      simp [paddedHistory, Preorder.frestrictLe_apply]
    have hx : (actualWalkStage pos B initial select (k + 1) ω).2.2 =
        (selectedClockedExcursion pos B (choice (observedHistory τ ω), ω m)
          (walkShift m ω)).2 := by
      change (selectedClockedExcursion pos B
        (choice (observedHistory τ ω), (observedHistory τ ω).2 (observedHistory τ ω).1)
        (futureAt τ ω)).2 = _
      rw [hlast, futureAt_of_eq hk]
    rw [hx]
    cases hch : choice (observedHistory τ ω) with
    | none =>
      have hc := clockedConstant_mem_curveOscillationLe (pos (ω m)) (le_refl (0 : ℝ)) t
      exact hc.trans (le_max_of_le_right dist_nonneg)
    | some j =>
      have hsj : select k (ω m) = some j := by
        have h := hch
        simp only [choice, walkStageSelector] at h
        split_ifs at h
        rwa [hlast] at h
      exact curve_ofWalk_shape (hBc j) (walkShift m ω) (by
        simpa [walkShift] using hsel k (ω m) j hsj) t

end SpherePackings.MarkovChain
