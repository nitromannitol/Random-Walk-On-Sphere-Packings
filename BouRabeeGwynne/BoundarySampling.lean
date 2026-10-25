module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/BoundarySampling.lean` at commit cf73d6e); unchanged apart from this header.
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Analysis.Normed.Module.RCLike.Real

@[expose] public section

open scoped Topology

namespace BouRabeeGwynne

section ProperMetric

variable {E : Type*} [MetricSpace E] [ProperSpace E]

/-- A genuine nearest point of the closure, used for the repaired boundary data in B(b).
The existence theorem is supplied by properness; no choice of a point in the original
tiling cell is required. -/
noncomputable def nearestClosurePoint (U : Set E) (hne : U.Nonempty) (x : E) : E :=
  Classical.choose (Metric.exists_mem_closure_infDist_eq_dist hne x)

theorem nearestClosurePoint_mem_closure (U : Set E) (hne : U.Nonempty) (x : E) :
    nearestClosurePoint U hne x ∈ closure U :=
  (Classical.choose_spec (Metric.exists_mem_closure_infDist_eq_dist hne x)).1

theorem nearestClosurePoint_dist_eq_infDist (U : Set E) (hne : U.Nonempty) (x : E) :
    dist x (nearestClosurePoint U hne x) = Metric.infDist x U :=
  (Classical.choose_spec (Metric.exists_mem_closure_infDist_eq_dist hne x)).2.symm

theorem nearestClosurePoint_dist_le (U : Set E) (hne : U.Nonempty) (x : E)
    {y : E} (hy : y ∈ closure U) :
    dist x (nearestClosurePoint U hne x) ≤ dist x y := by
  rw [nearestClosurePoint_dist_eq_infDist, ← Metric.infDist_closure]
  exact Metric.infDist_le_dist_of_mem hy

theorem nearestClosurePoint_dist_le_of_mem (U : Set E) (hne : U.Nonempty) (x : E)
    {y : E} (hy : y ∈ U) :
    dist x (nearestClosurePoint U hne x) ≤ dist x y :=
  nearestClosurePoint_dist_le U hne x (subset_closure hy)

@[simp] theorem nearestClosurePoint_eq_self (U : Set E) (hne : U.Nonempty)
    {x : E} (hx : x ∈ closure U) : nearestClosurePoint U hne x = x := by
  apply (dist_eq_zero.mp ?_).symm
  rw [nearestClosurePoint_dist_eq_infDist, ← Metric.infDist_closure]
  exact Metric.infDist_zero_of_mem hx

/-- Continuum data sampled at an actual nearest point of the closure. -/
noncomputable def projectedBoundaryValue (U : Set E) (hne : U.Nonempty)
    (hC : E → ℝ) (x : E) : ℝ :=
  hC (nearestClosurePoint U hne x)

theorem projectedBoundaryValue_congr (U : Set E) (hne : U.Nonempty)
    {hC gC : E → ℝ} (h : Set.EqOn hC gC (closure U)) :
    projectedBoundaryValue U hne hC = projectedBoundaryValue U hne gC := by
  funext x
  exact h (nearestClosurePoint_mem_closure U hne x)

@[simp] theorem projectedBoundaryValue_eq_of_mem_closure (U : Set E) (hne : U.Nonempty)
    (hC : E → ℝ) {x : E} (hx : x ∈ closure U) :
    projectedBoundaryValue U hne hC x = hC x := by
  simp only [projectedBoundaryValue, nearestClosurePoint_eq_self U hne hx]

omit [ProperSpace E] in
/-- Two samples close to the same point are close to each other. -/
theorem sample_points_dist_le_twice {x p q : E} {r : ℝ}
    (hp : dist x p ≤ r) (hq : dist x q ≤ r) : dist p q ≤ 2 * r := by
  calc
    dist p q ≤ dist p x + dist x q := dist_triangle p x q
    _ ≤ r + r := add_le_add (by simpa only [dist_comm] using hp) hq
    _ = 2 * r := (two_mul r).symm

/-- Continuous data on a bounded closure cannot distinguish two closure samples
that are uniformly close to the same point. This is a data estimate, not continuity
of a nearest-point selector. -/
theorem closure_samples_uniform_control {U : Set E} {hC : E → ℝ}
    (hU : Bornology.IsBounded U) (hh : ContinuousOn hC (closure U)) :
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ x p q : E, p ∈ closure U → q ∈ closure U →
        dist x p ≤ δ → dist x q ≤ δ → |hC p - hC q| ≤ η := by
  intro η hη
  have huc := hU.isCompact_closure.uniformContinuousOn_of_continuous hh
  obtain ⟨δ, hδ, hcontrol⟩ := Metric.uniformContinuousOn_iff_le.mp huc η hη
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  intro x p q hp hq hxp hxq
  have hpq : dist p q ≤ δ := by
    calc
      dist p q ≤ dist p x + dist x q := dist_triangle p x q
      _ ≤ δ / 2 + δ / 2 :=
        add_le_add (by simpa only [dist_comm] using hxp) hxq
      _ = δ := add_halves δ
  simpa only [Real.dist_eq] using hcontrol p hp q hq hpq

/-- The prescribed data approach the data at any nearby point of the closure,
uniformly in the exterior sampling location. -/
theorem projectedBoundaryValue_uniform_control (U : Set E) (hne : U.Nonempty)
    (hC : E → ℝ) (hU : Bornology.IsBounded U) (hh : ContinuousOn hC (closure U)) :
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ x y : E, y ∈ closure U → dist x y ≤ δ →
        |projectedBoundaryValue U hne hC x - hC y| ≤ η := by
  intro η hη
  obtain ⟨δ, hδ, hcontrol⟩ := closure_samples_uniform_control hU hh η hη
  refine ⟨δ, hδ, ?_⟩
  intro x y hy hxy
  exact hcontrol x (nearestClosurePoint U hne x) y
    (nearestClosurePoint_mem_closure U hne x) hy
    ((nearestClosurePoint_dist_le U hne x hy).trans hxy) hxy

end ProperMetric

section RealNormed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- A nearest point of the closure lies on the frontier when the original point
is outside the interior. The set need not be convex. -/
theorem nearestClosurePoint_mem_frontier (U : Set E) (hne : U.Nonempty)
    {x : E} (hx : x ∉ interior U) : nearestClosurePoint U hne x ∈ frontier U := by
  let p := nearestClosurePoint U hne x
  change p ∈ frontier U
  refine ⟨nearestClosurePoint_mem_closure U hne x, ?_⟩
  intro hp
  have hxp : x ≠ p := by
    intro heq
    exact hx (heq.symm ▸ hp)
  have hr : dist x p ≠ 0 := (dist_pos.mpr hxp).ne'
  have hball : Metric.ball x (dist x p) ⊆ (interior U)ᶜ := by
    intro z hz hzU
    have hmin : dist x p ≤ dist x z :=
      nearestClosurePoint_dist_le_of_mem U hne x (interior_subset hzU)
    exact (not_lt_of_ge hmin) (by simpa only [Metric.mem_ball, dist_comm] using hz)
  have hpball : p ∈ closure (Metric.ball x (dist x p)) := by
    rw [closure_ball x hr]
    exact Metric.mem_closedBall.mpr (le_of_eq (dist_comm p x))
  exact (closure_minimal hball isOpen_interior.isClosed_compl) hpball hp

theorem nearestClosurePoint_mem_frontier_of_notMem (U : Set E) (hne : U.Nonempty)
    {x : E} (hx : x ∉ U) : nearestClosurePoint U hne x ∈ frontier U :=
  nearestClosurePoint_mem_frontier U hne (fun hxU => hx (interior_subset hxU))

end RealNormed

end BouRabeeGwynne
