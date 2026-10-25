module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/Section3CompactCollar.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.Harmonic
public import BouRabeeGwynne.EventualLocalRegion
public import Mathlib.Analysis.Normed.Group.Bounded

@[expose] public section

/-! A single compact harmonic collar supplies all Section 3 analytic constants. -/

open scoped Classical Topology ENNReal

namespace BouRabeeGwynne

/-- Boundedness and the approved fixed-neighborhood hypothesis give a genuine
compact collar, one Hessian bound and one continuity modulus. These quantities
are chosen before the tiling index. -/
theorem HarmonicNearClosure.exists_compact_collar {d : ℕ}
    {h : Euc d → ℝ} {U D : Set (Euc d)} (hh : HarmonicNearClosure h U)
    (hU : Bornology.IsBounded U) (hUD : HasAmbientCollar U D) :
    ∃ (Q W : Set (Euc d)) (ρ M : ℝ),
      0 < ρ ∧ 1 ≤ M ∧ IsCompact Q ∧ IsOpen W ∧ IsHarmonicOn h W ∧
      closure U ⊆ interior Q ∧ Q ⊆ W ∧ Q ⊆ interior D ∧
      Metric.cthickening ρ (closure U) ⊆ Q ∧
      UniformContinuousOn h Q ∧
      (∀ x ∈ Q, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M) := by
  obtain ⟨W, hW, hUW, hhW⟩ := hh
  obtain ⟨ρ, hρ, hρQ⟩ := hU.isCompact_closure.exists_cthickening_subset_open
    (hW.inter isOpen_interior) (fun x hx => ⟨hUW hx, hUD hx⟩)
  let Q := Metric.cthickening ρ (closure U)
  have hQc : IsCompact Q := hU.isCompact_closure.cthickening
  have hQW : Q ⊆ W := fun x hx => (hρQ hx).1
  have hQD : Q ⊆ interior D := fun x hx => (hρQ hx).2
  have hfirst : ContDiffOn ℝ 1 (fderiv ℝ h) W :=
    hhW.contDiffOn.fderiv_of_isOpen hW (by norm_num)
  have hsecond : ContinuousOn (fderiv ℝ (fderiv ℝ h)) Q :=
    (hfirst.continuousOn_fderiv_of_isOpen hW (by norm_num)).mono hQW
  obtain ⟨M, hM⟩ := hQc.exists_bound_of_continuousOn
    (f := fderiv ℝ (fderiv ℝ h)) hsecond
  refine ⟨Q, W, ρ, max M 1, hρ, le_max_right _ _, hQc, hW, hhW, ?_,
    hQW, hQD, Set.Subset.rfl, ?_, ?_⟩
  · exact (Metric.self_subset_thickening hρ (closure U)).trans
      (Metric.thickening_subset_interior_cthickening ρ (closure U))
  · exact hQc.uniformContinuousOn_of_continuous (hhW.contDiffOn.continuousOn.mono hQW)
  · intro x hx
    exact (hM x hx).trans (le_max_left _ _)

namespace OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

/-- An entire radius-two-mesh ball at any closed-region vertex lies in the
four-mesh continuum collar. This includes exterior graph-boundary vertices. -/
theorem closedVertex_ball_subset_cthickening {U : Set (Euc d)}
    (hmesh : T.mesh ≠ ∞) {v : T.V} (hv : v ∈ T.closedVertices U) :
    Metric.closedBall (T.pos v) (2 * T.mesh.toReal) ⊆
      Metric.cthickening (4 * T.mesh.toReal) (closure U) := by
  have hp := T.closedVertices_pos_mem_cthickening hv hmesh
  have hnonneg : 0 ≤ 2 * T.mesh.toReal := mul_nonneg zero_le_two ENNReal.toReal_nonneg
  have hsub := (Metric.closedBall_subset_cthickening hp (2 * T.mesh.toReal)).trans
    (Metric.cthickening_cthickening_subset hnonneg hnonneg (closure U))
  have hr : 2 * T.mesh.toReal + 2 * T.mesh.toReal = 4 * T.mesh.toReal := by ring
  simpa only [hr] using hsub

end OrthogonalTiling

namespace NearestVertexData

variable {d : ℕ} {G : TilingSequence d} (N : NearestVertexData G)

/-- The actual approximation condition eventually puts all closed-region
cells and all balls needed by the surface Taylor estimate in the fixed Q. -/
theorem eventually_closedRegion_in_compact_collar (h : N.ApproximationCondition)
    {U Q : Set (Euc d)} {ρ : ℝ} (hρ : 0 < ρ)
    (hQ : Metric.cthickening ρ (closure U) ⊆ Q) :
    ∀ᶠ n in Filter.atTop, (G.tiling n).mesh ≠ ∞ ∧
      ∀ v ∈ (G.tiling n).closedVertices U,
        ((G.tiling n).cell v).carrier ⊆ Q ∧
        Metric.closedBall ((G.tiling n).pos v) (2 * (G.tiling n).mesh.toReal) ⊆ Q := by
  filter_upwards [N.eventually_mesh_finite_le h (div_pos hρ (by norm_num : (0 : ℝ) < 4))]
    with n hn
  refine ⟨hn.1, ?_⟩
  intro v hv
  have hball : Metric.closedBall ((G.tiling n).pos v)
      (2 * (G.tiling n).mesh.toReal) ⊆ Q :=
    ((G.tiling n).closedVertex_ball_subset_cthickening hn.1 hv).trans
      ((Metric.cthickening_mono (by linarith : 4 * (G.tiling n).mesh.toReal ≤ ρ)
        (closure U)).trans hQ)
  refine ⟨?_, hball⟩
  intro x hx
  apply hball
  apply Metric.mem_closedBall.mpr
  have hdist := (G.tiling n).toTilingData.dist_pos_le_mesh hx hn.1
  have hε : 0 ≤ (G.tiling n).mesh.toReal := ENNReal.toReal_nonneg
  linarith

end NearestVertexData
end BouRabeeGwynne
