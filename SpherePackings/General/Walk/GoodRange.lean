module

-- Built on Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne (commit cf73d6e).
public import BouRabeeGwynne.WalkBrownianGoodEvent
public import BouRabeeGwynne.ExcursionOscillation
public import BouRabeeGwynne.WalkExcursionKernel

@[expose] public section

/-!
# Walk excursion ranges on good pairs

On a chain of good excursion pairs (each walk excursion ends within `a` of the corresponding
Brownian one), a walk excursion that stays within `R₀` of its start except for its final segment
has range at most `max R₀ (2 a + S)`, where `S` bounds the Brownian ranges.  This replaces a
deterministic step bound for walks whose steps can be long.  Nothing here depends on the paper.
-/

open BouRabeeGwynne

namespace SpherePackings.MarkovChain

variable {d : ℕ}

/-- On a good pair, the walk endpoint is within `a` of the Brownian endpoint. -/
lemma dist_endPoint_le_of_goodExcursionPair {V ι : Type*} (pos : V → Euc d)
    (E : ι → Set (Euc d)) {a : ℝ} (hdiam : ∀ k, ∀ x ∈ E k, ∀ y ∈ E k, dist x y ≤ a)
    {p : (Bool × ClockedWalkExcursion d) × (Bool × C(unitInterval, Euc d))}
    (hp : p ∈ goodExcursionPair pos E a) :
    dist (ClockedWalkExcursion.endPoint p.1.2) (p.2.2 1) ≤ a := by
  unfold goodExcursionPair at hp
  rcases hp with ⟨k, hw, hb⟩ | ⟨-, -, -, h⟩
  · unfold walkEndpointCell activeEndpointCell at hw
    unfold activeEndpointCell at hb
    exact hdiam k _ hw.2.1 _ hb.2
  · exact h

/-- **Walk ranges on good pairs.** -/
theorem walk_range_of_goodExcursionPairs {V : Type*} (pos : V → Euc d) {K : ℕ}
    (m : ℕ → ℕ) (E : ∀ i, Fin (m i) → Set (Euc d)) {a S R₀ : ℝ}
    (hdiam : ∀ i ≤ K, ∀ k, ∀ x ∈ E i k, ∀ y ∈ E i k, dist x y ≤ a)
    (w : ℕ → Bool × ClockedWalkExcursion d) (b : ℕ → Bool × C(unitInterval, Euc d))
    (hw : (fun i => ClockedWalkExcursion.curve (w i).2) ∈
      ExcursionTrajectory.compatiblePaths K d)
    (hb : (fun i => (b i).2) ∈ ExcursionTrajectory.compatiblePaths K d)
    (hgood : ∀ i ≤ K, (w i, b i) ∈ goodExcursionPair pos (E i) a)
    (hstart : dist (ClockedWalkExcursion.start (w 0).2) ((b 0).2 0) ≤ a)
    (hbrange : ∀ i ≤ K, (b i).2 ∈ curveOscillationLe S)
    (hshape : ∀ i ≤ K, ∀ t, dist (ClockedWalkExcursion.curve (w i).2 t)
      (ClockedWalkExcursion.curve (w i).2 0) ≤
        max R₀ (dist (ClockedWalkExcursion.curve (w i).2 1)
          (ClockedWalkExcursion.curve (w i).2 0))) :
    ∀ i ≤ K, ClockedWalkExcursion.curve (w i).2 ∈ curveOscillationLe (max R₀ (2 * a + S)) := by
  -- walk and Brownian endpoints, and starts, are within `a`
  have hend : ∀ i ≤ K, dist (ClockedWalkExcursion.endPoint (w i).2) ((b i).2 1) ≤ a :=
    fun i hi => dist_endPoint_le_of_goodExcursionPair (p := (w i, b i)) pos (E i) (hdiam i hi)
      (hgood i hi)
  have hst : ∀ i ≤ K, dist (ClockedWalkExcursion.start (w i).2) ((b i).2 0) ≤ a := by
    intro i hi
    cases i with
    | zero => exact hstart
    | succ i =>
      have hi' : i < K := Nat.lt_of_succ_le hi
      have hwc := hw ⟨i, Nat.lt_succ_of_lt hi'⟩ ⟨i + 1, Nat.succ_lt_succ hi'⟩ rfl
      have hbc := hb ⟨i, Nat.lt_succ_of_lt hi'⟩ ⟨i + 1, Nat.succ_lt_succ hi'⟩ rfl
      simp only at hwc hbc
      rw [← ClockedWalkExcursion.curve_start, ← hwc, ← hbc, ClockedWalkExcursion.curve_endPoint]
      exact hend i hi'.le
  intro i hi t
  have hb1 := hbrange i hi 1
  have hse : dist (ClockedWalkExcursion.curve (w i).2 1) (ClockedWalkExcursion.curve (w i).2 0) ≤
      2 * a + S := by
    rw [ClockedWalkExcursion.curve_endPoint, ClockedWalkExcursion.curve_start]
    calc dist (ClockedWalkExcursion.endPoint (w i).2) (ClockedWalkExcursion.start (w i).2)
        ≤ dist (ClockedWalkExcursion.endPoint (w i).2) ((b i).2 1) +
            dist ((b i).2 1) ((b i).2 0) +
            dist ((b i).2 0) (ClockedWalkExcursion.start (w i).2) := dist_triangle4 _ _ _ _
      _ ≤ a + S + a := by
          gcongr
          · exact hend i hi
          · rw [dist_comm]; exact hst i hi
      _ = 2 * a + S := by ring
  exact (hshape i hi t).trans (max_le_max le_rfl hse)

/-- **Shape of a walk excursion in a ball.**  If every state of `B` sits in the ball `B_r(c)` and
the path starts in that ball, the excursion recorded up to the exit from `B` stays within
`max (2 r) |end - start|` of its start: every vertex before the exit is in the ball, and the
polygonal curve lies in the convex hull of its vertices. -/
theorem curve_ofWalk_shape {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V] {pos : V → Euc d} {B : Set V} {c : Euc d} {r : ℝ}
    (hB : ∀ v ∈ B, pos v ∈ Metric.ball c r) (ω : ℕ → V) (h0 : pos (ω 0) ∈ Metric.ball c r)
    (t : unitInterval) :
    dist (ClockedWalkExcursion.curve (ClockedWalkExcursion.ofWalk pos B ω) t)
        (ClockedWalkExcursion.curve (ClockedWalkExcursion.ofWalk pos B ω) 0) ≤
      max (2 * r) (dist (ClockedWalkExcursion.curve (ClockedWalkExcursion.ofWalk pos B ω) 1)
        (ClockedWalkExcursion.curve (ClockedWalkExcursion.ofWalk pos B ω) 0)) := by
  set e := ClockedWalkExcursion.ofWalk pos B ω with he
  set m := (FiniteConductanceNetwork.exitTime B ω).untopD 0
  have hstart : ClockedWalkExcursion.curve e 0 = pos (ω 0) := by
    rw [ClockedWalkExcursion.curve_start, he, ClockedWalkExcursion.start_ofWalk]
  have hend : ClockedWalkExcursion.curve e 1 = pos (ω m) := by
    rw [ClockedWalkExcursion.curve_endPoint]
    simp [ClockedWalkExcursion.endPoint, e, ClockedWalkExcursion.ofWalk, m]
  set R := max (2 * r) (dist (pos (ω m)) (pos (ω 0)))
  have hvert : ∀ k, (e.2 k) ∈ Metric.closedBall (pos (ω 0)) R := by
    intro k
    simp only [e, ClockedWalkExcursion.ofWalk, Metric.mem_closedBall]
    by_cases hk : min k m < m
    · have hlt : ((min k m : ℕ) : WithTop ℕ) < FiniteConductanceNetwork.exitTime B ω := by
        rcases eq_or_ne (FiniteConductanceNetwork.exitTime B ω) ⊤ with htop | htop
        · rw [htop]; exact WithTop.coe_lt_top _
        · obtain ⟨M, hM⟩ := WithTop.ne_top_iff_exists.mp htop
          have hmM : m = M := by simp only [m, ← hM, WithTop.untopD_coe]
          rw [← hM]
          exact WithTop.coe_lt_coe.mpr (hmM ▸ hk)
      have hin := hB _ (FiniteConductanceNetwork.mem_of_lt_exitTime hlt)
      have h1 : dist (pos (ω (min k m))) (pos (ω 0)) < 2 * r := by
        calc dist (pos (ω (min k m))) (pos (ω 0))
            ≤ dist (pos (ω (min k m))) c + dist c (pos (ω 0)) := dist_triangle _ _ _
          _ < r + r := add_lt_add (Metric.mem_ball.mp hin) (by rw [dist_comm]; exact h0)
          _ = 2 * r := by ring
      exact h1.le.trans (le_max_left _ _)
    · have hkm : min k m = m := le_antisymm (min_le_right _ _) (not_lt.mp hk)
      rw [hkm]
      exact le_max_right _ _
  have hcurve := BouRabeeGwynne.polygonalCurve_mem_of_convex (V := ℕ) e.2 id
    (convex_closedBall (pos (ω 0)) R) hvert e.1 t
  rw [hstart, hend]
  exact Metric.mem_closedBall.mp hcurve

end SpherePackings.MarkovChain
