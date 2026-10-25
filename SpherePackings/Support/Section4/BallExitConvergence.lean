module

-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne (file
-- `BouRabeeGwynne/Section4BallExitConvergence.lean` at commit cf73d6e): the declarations of that
-- file that use the regularity hypothesis `PaperRegularity G`, with the hypothesis replaced by the
-- localized Assumption D `TilingAssumptionD G` and deprecated names updated; the other declarations
-- are imported. The call of the collar estimate passes the ball equation `rfl`.
public import BouRabeeGwynne.Section4BallExitConvergence
public import SpherePackings.Support.Section4.HarmonicMeasure

@[expose] public section

/-! Section 4 of rw-spheres.tex under the localized Assumption D: the declarations of
leobon12's `BouRabeeGwynne.Section4BallExitConvergence` that use the regularity hypothesis. -/

open MeasureTheory ProbabilityTheory
open scoped Topology Classical

-- The copied proofs keep leobon12's `letI` style.
set_option linter.style.haveILetI false

namespace SpherePackings.AssumptionD

open BouRabeeGwynne

/-- Every continuous spatial test of the actual conductance-walk exit measure
converges uniformly over all interior starting vertices to its actual Brownian
ball-exit expectation. The ball and its ambient collar are fixed. -/
theorem eventually_ball_exit_test_error {d : ℕ} (hd : 1 ≤ d)
    (G : TilingSequence d) (N : NearestVertexData G) (c : Euc d) {r : ℝ} (hr : 0 < r)
    (hUD : HasAmbientCollar (Metric.ball c r) G.domain)
    (happrox : N.ApproximationCondition) (hAD : TilingAssumptionD G)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (f : Euc d → ℝ) (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop, ∃ hfin : ((G.tiling n).closedVertices (Metric.ball c r)).Finite,
      letI : Fintype ((G.tiling n).closedVertices (Metric.ball c r)) := hfin.fintype
      letI : MeasurableSpace ((G.tiling n).closedVertices (Metric.ball c r)) := ⊤
      ∃ ha : ((G.tiling n).finiteNetwork
          ((G.tiling n).closedVertices (Metric.ball c r))).BoundaryAccessible
          ((G.tiling n).finiteInterior (Metric.ball c r)),
        ∀ v : (G.tiling n).closedVertices (Metric.ball c r),
          v ∈ (G.tiling n).finiteInterior (Metric.ball c r) →
          |(∫ x, f x ∂(G.tiling n).spatialHarmonicMeasure (Metric.ball c r) ha v) -
            ∫ x, f x ∂(brownianSpatialHarmonicMeasure (Metric.ball c r) Metric.isOpen_ball
              μ hμ ((G.tiling n).pos v) : Measure (Euc d))| ≤ ε := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hthird : 0 < ε / 3 := div_pos hε (by norm_num)
  obtain ⟨P, hP, δ, hδ, hclose⟩ :=
    exists_harmonic_polynomial_near_sphere_collar hd c hr f hf hthird
  have hcont : Continuous (polynomialEval P) := (contDiff_polynomialEval P (n := 0)).continuous
  have hh : HarmonicNearClosure (polynomialEval P) (Metric.ball c r) :=
    ⟨Set.univ, isOpen_univ, Set.subset_univ _,
      isHarmonicOn_polynomialEval_of_laplacian_eq_zero P hP Set.univ⟩
  have hDomain : IsDomain (Metric.ball c r) :=
    ⟨Metric.isOpen_ball, ⟨c, Metric.mem_ball_self hr⟩, (convex_ball c r).isPreconnected⟩
  have hnear : ∀ x ∈ Metric.cthickening δ (frontier (Metric.ball c r)),
      |f x - polynomialEval P x| ≤ ε / 3 := by
    intro x hx
    have hx' : x ∈ Metric.cthickening δ (Metric.sphere c r) :=
      Metric.cthickening_subset_of_subset δ Metric.frontier_ball_subset_sphere hx
    simpa only [abs_sub_comm] using (hclose x hx').le
  have hboundary : ∀ x ∈ frontier (Metric.ball c r),
      |f x - polynomialEval P x| ≤ ε / 3 := by
    intro x hx
    exact hnear x (Metric.mem_cthickening_of_dist_le x x δ _ hx (by simpa using hδ.le))
  filter_upwards [eventually_spatialHarmonicMeasure_collar_error hd G N hr (Metric.ball c r) rfl
    f (polynomialEval P) hDomain Metric.isBounded_ball hUD happrox hAD hh hf hcont
    hδ hthird hnear] with n hn
  obtain ⟨hfin, hdata⟩ := hn
  let T := G.tiling n
  letI : Fintype (T.closedVertices (Metric.ball c r)) := hfin.fintype
  letI : MeasurableSpace (T.closedVertices (Metric.ball c r)) := ⊤
  obtain ⟨ha, herr⟩ := hdata
  refine ⟨hfin, ha, ?_⟩
  intro v hv
  have hbrown := abs_integral_brownianSpatialHarmonicMeasure_sub_le hd hμ
    Metric.isOpen_ball Metric.isBounded_ball hf hcont hh hboundary hv
  calc
    _ ≤ |(∫ x, f x ∂T.spatialHarmonicMeasure (Metric.ball c r) ha v) -
          polynomialEval P (T.pos v)| +
        |polynomialEval P (T.pos v) -
          ∫ x, f x ∂(brownianSpatialHarmonicMeasure (Metric.ball c r) Metric.isOpen_ball
            μ hμ (T.pos v) : Measure (Euc d))| := abs_sub_le _ _ _
    _ ≤ (ε / 3 + ε / 3) + ε / 3 :=
      add_le_add (herr v hv) (by simpa only [abs_sub_comm] using hbrown)
    _ = ε := by ring

end SpherePackings.AssumptionD
