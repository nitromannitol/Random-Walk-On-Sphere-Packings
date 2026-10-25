module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/Section4BallHarmonicMeasure.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.Section3TheoremBPartA
public import BouRabeeGwynne.HarmonicMeasureBridge

@[expose] public section

/-! Actual spatial exit measures and the ball-exit comparison used in Section 4. -/

open MeasureTheory ProbabilityTheory
open scoped Classical Topology ENNReal

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d) (U : Set (Euc d))
variable [Fintype (T.closedVertices U)] [MeasurableSpace (T.closedVertices U)]
variable [MeasurableSingletonClass (T.closedVertices U)]

/-- The exit measure of the actual finite conductance walk, in Euclidean space. -/
noncomputable def spatialHarmonicMeasure
    (ha : (T.finiteNetwork (T.closedVertices U)).BoundaryAccessible (T.finiteInterior U))
    (v : T.closedVertices U) : Measure (Euc d) :=
  ((T.finiteNetwork (T.closedVertices U)).discreteHarmonicMeasure (T.finiteInterior U)
    ((T.finiteNetwork (T.closedVertices U)).totalConductance_pos_of_boundaryAccessible
      (T.finiteInterior U) ha) v).map (fun w : T.closedVertices U => T.pos w)

instance spatialHarmonicMeasure_isProbabilityMeasure
    (ha : (T.finiteNetwork (T.closedVertices U)).BoundaryAccessible (T.finiteInterior U))
    (v : T.closedVertices U) : IsProbabilityMeasure (T.spatialHarmonicMeasure U ha v) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_of_finite
    (fun w : T.closedVertices U => T.pos w)).aemeasurable).mpr inferInstance

/-- The expected continuum boundary data equal the value of the genuine
ambient discrete Dirichlet solution at the starting vertex. -/
theorem integral_spatialHarmonicMeasure
    (ha : (T.finiteNetwork (T.closedVertices U)).BoundaryAccessible (T.finiteInterior U))
    {h : Euc d → ℝ} (hh : Continuous h) (v : T.closedVertices U) :
    (∫ x, h x ∂T.spatialHarmonicMeasure U ha v) =
      T.dirichletSolution U ha (fun w => h (T.pos w)) v := by
  rw [spatialHarmonicMeasure,
    integral_map (measurable_of_finite (fun w : T.closedVertices U => T.pos w)).aemeasurable
      hh.aestronglyMeasurable,
    T.dirichletSolution_apply_closed]
  exact (T.finiteNetwork (T.closedVertices U)).integral_discreteHarmonicMeasure_of_solvesDirichlet
    (T.finiteInterior U) _ ha
    ((T.finiteNetwork (T.closedVertices U)).dirichletSolution_spec
      (T.finiteInterior U) ha (fun w => h (T.pos w))) v

/-- Boundary approximation and the actual Dirichlet error control the exit
expectation, uniformly in the starting vertex. -/
theorem abs_integral_spatialHarmonicMeasure_sub_le
    (ha : (T.finiteNetwork (T.closedVertices U)).BoundaryAccessible (T.finiteInterior U))
    {f h : Euc d → ℝ} (hf : Continuous f) {η : ℝ}
    (hboundary : ∀ w ∈ T.boundaryVertices U, |f (T.pos w) - h (T.pos w)| ≤ η)
    (v : T.closedVertices U) (target : ℝ) :
    |(∫ x, f x ∂T.spatialHarmonicMeasure U ha v) - target| ≤
      η + |T.dirichletSolution U ha (fun w => h (T.pos w)) v - target| := by
  rw [spatialHarmonicMeasure,
    integral_map (measurable_of_finite (fun w : T.closedVertices U => T.pos w)).aemeasurable
      hf.aestronglyMeasurable,
    T.dirichletSolution_apply_closed]
  exact (T.finiteNetwork (T.closedVertices U)).abs_integral_discreteHarmonicMeasure_sub_le
    (T.finiteInterior U) _ ha
    ((T.finiteNetwork (T.closedVertices U)).dirichletSolution_spec
      (T.finiteInterior U) ha (fun w => h (T.pos w)))
    (fun w hw => hboundary w ((T.closedVertex_not_interior_iff U w).mp hw)) v target

end BouRabeeGwynne.OrthogonalTiling

namespace BouRabeeGwynne

/-- Proved Theorem B(a) gives a uniform bound for the actual exit expectation
of a continuous function harmonic near the closure. Finiteness and access to
the graph boundary are derived from the geometric approximation assumptions. -/
theorem eventually_spatialHarmonicMeasure_harmonic_error {d : ℕ} (hd : 1 ≤ d)
    (G : TilingSequence d) (N : NearestVertexData G)
    (U : Set (Euc d)) (h : Euc d → ℝ)
    (hDomain : IsDomain U) (hUb : Bornology.IsBounded U)
    (hUD : HasAmbientCollar U G.domain) (happrox : N.ApproximationCondition)
    (hreg : PaperRegularity G) (hh : HarmonicNearClosure h U) (hcont : Continuous h)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n in Filter.atTop, ∃ hfin : ((G.tiling n).closedVertices U).Finite,
      letI : Fintype ((G.tiling n).closedVertices U) := hfin.fintype
      letI : MeasurableSpace ((G.tiling n).closedVertices U) := ⊤
      ∃ ha : ((G.tiling n).finiteNetwork ((G.tiling n).closedVertices U)).BoundaryAccessible
          ((G.tiling n).finiteInterior U),
        ∀ v : (G.tiling n).closedVertices U, v ∈ (G.tiling n).finiteInterior U →
          |(∫ x, h x ∂(G.tiling n).spatialHarmonicMeasure U ha v) -
              h ((G.tiling n).pos v)| ≤ η := by
  have hB := theoremB_part_a d G N U h hd hDomain hUb hUD happrox hreg hh
  obtain ⟨e, he, _⟩ := exists_unit_euc hd
  filter_upwards [hB.1, hB.2 η hη,
    N.eventually_interior_cells_subset_domain happrox hUb hUD] with n hfin herror hcells
  let T := G.tiling n
  let R := T.closedVertices U
  let A := T.finiteInterior U
  refine ⟨hfin.1, ?_⟩
  letI : Fintype R := hfin.1.fintype
  letI : MeasurableSpace R := ⊤
  have hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R := by
    intro v hv w hvw
    exact T.neighbor_mem_closedVertices hv hvw
  have hcellD : ∀ v ∈ A, (T.cell v).carrier ⊆ interior T.domain := by
    intro v hv
    simpa only [T, G.common_domain n] using hcells v hv
  have ha := T.finiteNetwork_boundaryAccessible_of_cell_interior hd e he R A
    hneighbors hcellD
  refine ⟨ha, ?_⟩
  intro v hv
  rw [T.integral_spatialHarmonicMeasure U ha hcont v]
  exact herror (T.dirichletSolution U ha (fun w => h (T.pos w)))
    (T.dirichletSolution_spec U ha (fun w => h (T.pos w))) v hv

end BouRabeeGwynne

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

/-- Every external graph-boundary sample is within two meshes of the actual
continuum boundary. This uses nearest points of the whole closure. -/
lemma boundary_pos_mem_cthickening_frontier {U : Set (Euc d)} (hne : U.Nonempty)
    (hmesh : T.mesh ≠ ∞) {δ : ℝ} (hδ : 2 * T.mesh.toReal ≤ δ)
    {w : T.V} (hw : w ∈ T.boundaryVertices U) :
    T.pos w ∈ Metric.cthickening δ (frontier U) :=
  Metric.mem_cthickening_of_dist_le (T.pos w) (nearestClosurePoint U hne (T.pos w))
    δ (frontier U) (T.boundary_projection_mem_frontier hne hw)
    ((T.boundary_projection_dist_le hne hw hmesh).trans hδ)

/-- The actual closed graph region of a ball has only a two-mesh overshoot. -/
lemma closedVertices_pos_mem_enlarged_ball {c : Euc d} {r : ℝ}
    (hmesh : T.mesh ≠ ∞) {w : T.V} (hw : w ∈ T.closedVertices (Metric.ball c r)) :
    T.pos w ∈ Metric.closedBall c (r + 2 * T.mesh.toReal) := by
  change dist (T.pos w) c ≤ r + 2 * T.mesh.toReal
  rcases hw with hw | hw
  · exact (Metric.mem_ball.mp hw).le.trans
      (le_add_of_nonneg_right (mul_nonneg zero_le_two ENNReal.toReal_nonneg))
  · obtain ⟨v, hv, hdist⟩ := T.boundaryVertices_near_interior hw hmesh
    calc
      _ ≤ dist (T.pos w) (T.pos v) + dist (T.pos v) c := dist_triangle _ _ _
      _ ≤ 2 * T.mesh.toReal + r := add_le_add hdist (Metric.mem_ball.mp hv).le
      _ = _ := add_comm _ _

/-- Each polygonal segment joining two closed-region vertices stays in the
same enlarged ball, with no additional cell-shape assumption. -/
lemma closedVertices_segment_subset_enlarged_ball {c : Euc d} {r : ℝ}
    (hmesh : T.mesh ≠ ∞) {v w : T.V}
    (hv : v ∈ T.closedVertices (Metric.ball c r))
    (hw : w ∈ T.closedVertices (Metric.ball c r)) :
    segment ℝ (T.pos v) (T.pos w) ⊆ Metric.closedBall c (r + 2 * T.mesh.toReal) :=
  (convex_closedBall c _).segment_subset
    (T.closedVertices_pos_mem_enlarged_ball hmesh hv)
    (T.closedVertices_pos_mem_enlarged_ball hmesh hw)

end BouRabeeGwynne.OrthogonalTiling

namespace BouRabeeGwynne

/-- A uniform error on a compact set carrying a probability measure controls
the difference of the actual expectations of continuous functions. -/
theorem abs_integral_sub_integral_le_of_ae_mem_compact {d : ℕ}
    {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {S : Set (Euc d)}
    (hS : IsCompact S) (hμS : ∀ᵐ x ∂μ, x ∈ S)
    {f h : Euc d → ℝ} (hf : Continuous f) (hh : Continuous h)
    {η : ℝ} (hbound : ∀ x ∈ S, |f x - h x| ≤ η) :
    |(∫ x, f x ∂μ) - ∫ x, h x ∂μ| ≤ η := by
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨D, hD⟩ := hS.exists_bound_of_continuousOn hh.continuousOn
  have hfi : Integrable f μ := (integrable_const C).mono' hf.aestronglyMeasurable
    (hμS.mono fun x hx => hC x hx)
  have hhi : Integrable h μ := (integrable_const D).mono' hh.aestronglyMeasurable
    (hμS.mono fun x hx => hD x hx)
  rw [← integral_sub hfi hhi]
  have hnorm : ∀ᵐ x ∂μ, ‖f x - h x‖ ≤ η := by
    filter_upwards [hμS] with x hx
    exact (Real.norm_eq_abs _).symm ▸ hbound x hx
  simpa using norm_integral_le_of_norm_le_const hnorm

/-- A continuum boundary-collar approximation transfers the proved harmonic
test estimate to an actual continuous test of the discrete exit measure.
The two-mesh overshoot is derived from the original tiling geometry. -/
theorem eventually_spatialHarmonicMeasure_collar_error {d : ℕ} (hd : 1 ≤ d)
    (G : TilingSequence d) (N : NearestVertexData G)
    (U : Set (Euc d)) (f h : Euc d → ℝ)
    (hDomain : IsDomain U) (hUb : Bornology.IsBounded U)
    (hUD : HasAmbientCollar U G.domain) (happrox : N.ApproximationCondition)
    (hreg : PaperRegularity G) (hh : HarmonicNearClosure h U)
    (hf : Continuous f) (hcont : Continuous h)
    {δ η ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ)
    (hnear : ∀ x ∈ Metric.cthickening δ (frontier U), |f x - h x| ≤ η) :
    ∀ᶠ n in Filter.atTop, ∃ hfin : ((G.tiling n).closedVertices U).Finite,
      letI : Fintype ((G.tiling n).closedVertices U) := hfin.fintype
      letI : MeasurableSpace ((G.tiling n).closedVertices U) := ⊤
      ∃ ha : ((G.tiling n).finiteNetwork ((G.tiling n).closedVertices U)).BoundaryAccessible
          ((G.tiling n).finiteInterior U),
        ∀ v : (G.tiling n).closedVertices U, v ∈ (G.tiling n).finiteInterior U →
          |(∫ x, f x ∂(G.tiling n).spatialHarmonicMeasure U ha v) -
              h ((G.tiling n).pos v)| ≤ η + ρ := by
  filter_upwards [eventually_spatialHarmonicMeasure_harmonic_error hd G N U h
    hDomain hUb hUD happrox hreg hh hcont hρ,
    N.eventually_mesh_finite_le happrox (half_pos hδ)] with n hn hmesh
  obtain ⟨hfin, hmeasure⟩ := hn
  let T := G.tiling n
  letI : Fintype (T.closedVertices U) := hfin.fintype
  letI : MeasurableSpace (T.closedVertices U) := ⊤
  obtain ⟨ha, herr⟩ := hmeasure
  refine ⟨hfin, ha, ?_⟩
  intro v hv
  have hboundary : ∀ w ∈ T.boundaryVertices U, |f (T.pos w) - h (T.pos w)| ≤ η := by
    intro w hw
    apply hnear
    exact T.boundary_pos_mem_cthickening_frontier hDomain.2.1 hmesh.1
      (by linarith [hmesh.2]) hw
  have herror := herr v hv
  rw [T.integral_spatialHarmonicMeasure U ha hcont v] at herror
  exact (T.abs_integral_spatialHarmonicMeasure_sub_le U ha hf hboundary v (h (T.pos v))).trans
    (add_le_add (le_refl η) herror)

end BouRabeeGwynne
