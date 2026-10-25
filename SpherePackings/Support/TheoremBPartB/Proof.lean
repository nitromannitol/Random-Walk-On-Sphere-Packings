module

public import SpherePackings.Support.TheoremBPartB.BrownianContinuousExit
public import SpherePackings.Support.LevyProkhorovIntegral
public import BouRabeeGwynne.TheoremBStatement
public import BouRabeeGwynne.TheoremAProcessLaws
public import BouRabeeGwynne.UniformStoppedWalkConvergence
public import BouRabeeGwynne.Section3WellPosed
public import BouRabeeGwynne.Section3CaseIITarget
public import BouRabeeGwynne.HarmonicMeasureBridge
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

@[expose] public section

/-!
# Theorem B(b)

The convergence of the Dirichlet problem for boundary data that are only continuous on the closure
of a Lipschitz domain (`rw-spheres.tex:297-321`, hypothesis (b)).  The statement is leobon12's
`BouRabeeGwynne.TheoremBPartBStatement`.

The paper's proof (`rw-spheres.tex:1494-1496`) is "immediate from Theorem 4.1 and the fact that the
solution of the Dirichlet problem can be expressed in terms of the random walk".  We follow it with
Theorem A in place of Theorem 4.1:

* the discrete solution at an interior vertex `v` is the mean of the boundary data under the
  discrete harmonic measure from `v`, which is the endpoint law of the stopped walk;
* the boundary data are within a small error of a fixed bounded uniformly continuous extension `H`
  of `h_C` evaluated at the exit vertex, since the sample point is within two meshes of it;
* by Theorem A the stopped walk and Brownian laws are close in Lévy–Prokhorov distance, uniformly in
  the starting point, so the means of `H` at their endpoints are close;
* the mean of `H` at the Brownian exit point is `h_C(v)`
  (`integral_stoppedBrownian_endPoint_of_continuousOn`).
-/

open MeasureTheory Filter Metric Set
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace SpherePackings

open BouRabeeGwynne

variable {d : ℕ}

/-- A nearest point of `closure U` to a point outside the open set `U` lies on its frontier. -/
lemma mem_frontier_of_isNearest {U : Set (Euc d)} (hU : IsOpen U) {x p : Euc d} (hx : x ∉ U)
    (hp : p ∈ closure U) (hnear : ∀ y ∈ closure U, dist x p ≤ dist x y) : p ∈ frontier U := by
  refine ⟨hp, fun hpi => ?_⟩
  rw [hU.interior_eq] at hpi
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU p hpi
  have hxp : 0 < dist x p := dist_pos.mpr fun h => hx (h ▸ hpi)
  set t : ℝ := min (1 / 2) (r / (2 * dist x p)) with ht
  have ht0 : 0 < t := lt_min (by norm_num) (by positivity)
  have ht1 : t ≤ 1 / 2 := min_le_left _ _
  let q : Euc d := p + t • (x - p)
  have hpq : dist q p = t * dist x p := by
    simp only [q, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht0]
  have hqU : q ∈ U := by
    apply hball
    rw [mem_ball, hpq]
    calc t * dist x p ≤ r / (2 * dist x p) * dist x p :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) dist_nonneg
      _ = r / 2 := by field_simp
      _ < r := half_lt_self hr
  have hxq : dist x q = (1 - t) * dist x p := by
    have : x - q = (1 - t) • (x - p) := by
      simp only [q, sub_smul, one_smul, smul_sub]
      abel
    rw [dist_eq_norm, this, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), ← dist_eq_norm]
  have := hnear q (subset_closure hqU)
  rw [hxq] at this
  nlinarith

/-- A continuous function on the compact `closure U` has a bounded, uniformly continuous extension
to all of `ℝ^d`. -/
lemma exists_uniformContinuous_extension {U : Set (Euc d)} (hUb : Bornology.IsBounded U)
    {h : Euc d → ℝ} (hc : ContinuousOn h (closure U)) :
    ∃ H : Euc d →ᵇ ℝ, (∀ x ∈ closure U, H x = h x) ∧ UniformContinuous H := by
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq isClosed_closure
    (⟨fun x : closure U => h x, continuousOn_iff_continuous_domRestrict.mp hc⟩ :
      C(closure U, ℝ))
  have hGeq : ∀ x ∈ closure U, G x = h x := fun x hx =>
    congrArg (fun f : C(closure U, ℝ) => f ⟨x, hx⟩) hG
  obtain ⟨φ, hφ1, -, hφc, -⟩ := exists_continuous_one_zero_of_isCompact hUb.isCompact_closure
    isClosed_empty (disjoint_empty _)
  have hcont : Continuous fun x => G x * φ x := G.continuous.mul φ.continuous
  have hsupp : HasCompactSupport fun x => G x * φ x := hφc.mul_left
  refine ⟨_root_.ofCompactSupport _ hcont hsupp, fun x hx => ?_,
    hsupp.uniformContinuous_of_continuous hcont⟩
  change G x * φ x = h x
  rw [hφ1 hx, Pi.one_apply, mul_one, hGeq x hx]

/-- The nearest vertex of a vertex position is that vertex. -/
lemma NearestVertexData.vertex_pos_eq {G : TilingSequence d} (N : NearestVertexData G) {n : ℕ}
    {v : (G.tiling n).V} (hv : (G.tiling n).pos v ∈ G.domain) :
    N.vertex n ((G.tiling n).pos v) = v := by
  have h := N.isNearest n _ hv v
  rw [dist_self] at h
  have h0 : dist ((G.tiling n).pos v) ((G.tiling n).pos (N.vertex n ((G.tiling n).pos v))) = 0 :=
    le_antisymm h dist_nonneg
  exact ((G.tiling n).toTilingData.pos_injective (dist_eq_zero.mp h0)).symm

/-- **Theorem B(b)**: convergence of the discrete Dirichlet problem with continuous boundary data
on a Lipschitz domain. -/
theorem theoremB_part_b : TheoremBPartBStatement := by
  intro d G N U hC hd hU hUb hUD happrox hreg hharm hcont
  have hUopen : IsOpen U := hU.isDomain.1
  have hUne : U.Nonempty := hU.isDomain.2.1
  refine ⟨⟨NearestClosureBoundaryChoices.ofNonempty G U hUne⟩, fun S => ⟨?_, ?_, ?_⟩⟩
  · -- Every sample point lies on the frontier.
    intro n v
    exact mem_frontier_of_isNearest hUopen v.2.1 (S.mem_closure n v) (S.isNearest n v)
  · -- The sample points are within two meshes.
    filter_upwards [N.eventually_mesh_finite_le happrox one_pos] with n hn v
    obtain ⟨w, hwU, hdist⟩ := (G.tiling n).boundaryVertices_near_interior v.2 hn.1
    exact (S.isNearest n v _ (subset_closure hwU)).trans hdist
  obtain ⟨e, he, -⟩ := exists_unit_euc hd
  refine ⟨N.eventually_uniqueDirichletExtension hd e he happrox hUb hUD (S.boundaryData hC), ?_⟩
  intro η hη
  -- The continuum ingredients.
  obtain ⟨H, hHeq, hHuc⟩ := exists_uniformContinuous_extension hUb hcont
  obtain ⟨ε₀, hε₀, hosc⟩ := Metric.uniformContinuous_iff.mp hHuc (η / 4) (by positivity)
  set ε : ℝ := min ε₀ (η / (8 * (‖H‖ + 1))) with hεdef
  have hε : 0 < ε := lt_min hε₀ (by positivity)
  have hεε₀ : ε ≤ ε₀ := min_le_left _ _
  have hεH : 2 * ε * ‖H‖ ≤ η / 4 := by
    have h1 : ε ≤ η / (8 * (‖H‖ + 1)) := min_le_right _ _
    have h2 : 2 * ε * ‖H‖ ≤ 2 * (η / (8 * (‖H‖ + 1))) * ‖H‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    have h3 : 2 * (η / (8 * (‖H‖ + 1))) * ‖H‖ ≤ η / 4 := by
      rw [show 2 * (η / (8 * (‖H‖ + 1))) * ‖H‖ = η / 4 * (‖H‖ / (‖H‖ + 1)) by
        field_simp; ring]
      exact mul_le_of_le_one_right (by positivity)
        ((div_le_one (by positivity)).mpr (by linarith))
    linarith
  obtain ⟨μ, hμ, -⟩ := exists_standardBrownianLaw_with_stopped_laws hd hUopen hUb
  have : IsProbabilityMeasure μ := hμ.1
  obtain ⟨walkLaw, hwalk⟩ := N.exists_eventually_stoppedWalkLaws hd U hUb hUD happrox
  filter_upwards [hwalk, N.eventually_stoppedWalkLaw_levyProkhorov_le hd hUopen
      hU.hasLipschitzBoundary hUb hUD happrox hreg hμ (half_pos hε),
      N.eventually_closedVertices_finite happrox hUb hUD,
      N.eventually_interior_cells_subset_domain happrox hUb hUD,
      N.eventually_mesh_finite_le happrox (by positivity : 0 < ε₀ / 4)] with n hwn hLP hfin hcells hmesh
  intro hD hsol v hv
  let _ : Fintype ((G.tiling n).closedVertices U) := hfin.fintype
  let _ : MeasurableSpace ((G.tiling n).closedVertices U) := ⊤
  -- The finite network and its harmonic measure.
  have hneighbors : ∀ w ∈ (G.tiling n).finiteInterior U, ∀ u, (G.tiling n).adj w u → u ∈ (G.tiling n).closedVertices U :=
    fun w hw u hwu => (G.tiling n).neighbor_mem_closedVertices hw hwu
  have hcellD : ∀ w ∈ (G.tiling n).finiteInterior U, ((G.tiling n).cell w).carrier ⊆ interior (G.tiling n).domain := by
    intro w hw
    simpa only [G.common_domain n] using hcells w hw
  have haccess := (G.tiling n).finiteNetwork_boundaryAccessible_of_cell_interior hd e he
    ((G.tiling n).closedVertices U) ((G.tiling n).finiteInterior U) hneighbors hcellD
  set Net := (G.tiling n).finiteNetwork ((G.tiling n).closedVertices U)
  set A := (G.tiling n).finiteInterior U
  have hA : ∀ w ∈ A, 0 < Net.totalConductance w := Net.totalConductance_pos_of_boundaryAccessible
    A haccess
  let vS : (G.tiling n).closedVertices U := ⟨v, Or.inl hv⟩
  set HM := Net.discreteHarmonicMeasure A hA vS
  -- The discrete solution is the boundary mean.
  let g : (G.tiling n).closedVertices U → ℝ := fun w => S.boundaryData hC n w
  have hrepr : (∫ w, g w ∂HM) = hD v :=
    Net.integral_discreteHarmonicMeasure_of_solvesDirichlet A hA haccess
      ((G.tiling n).solvesDirichlet_restrict hsol) vS
  -- The walk law from `v` and its endpoint law.
  have hvD : (G.tiling n).pos v ∈ G.domain := hUD.subset hv
  have hν : IsStoppedTilingWalkLaw (G.tiling n) U v (walkLaw n ((G.tiling n).pos v)) := by
    have := hwn ((G.tiling n).pos v)
    rwa [NearestVertexData.vertex_pos_eq N hvD] at this
  have hνeq := (G.tiling n).isStoppedTilingWalkLaw_eq_ambient U ((G.tiling n).closedVertices U) subset_rfl A
    (fun _ h => h) hA vS hν
  have hend : (walkLaw n ((G.tiling n).pos v)).map CurveSpace.endPoint = HM.map fun w : (G.tiling n).closedVertices U => (G.tiling n).pos w := by
    rw [hνeq]
    exact Net.stoppedPolygonalCurve_map_endPoint (fun w : (G.tiling n).closedVertices U => (G.tiling n).pos w) A hA vS
  have hνprob : IsProbabilityMeasure (walkLaw n ((G.tiling n).pos v)) := by
    obtain ⟨R, hR, h⟩ := hν
    let _ : MeasurableSpace R := ⊤
    obtain ⟨-, -, -, -, -, hprob, -⟩ := h
    exact hprob
  -- Step 1: boundary data versus `H` at the exit vertex.
  have hstep1 : |(∫ w, g w ∂HM) - ∫ w, H ((G.tiling n).pos w) ∂HM| ≤ η / 4 := by
    have hae : ∀ᵐ w ∂HM, w ∉ A := by
      have hfinite := Net.trajectoryLaw_ae_finiteExit A hA haccess vS
      exact (ae_map_iff (FiniteConductanceNetwork.measurable_exitVertex A).aemeasurable
        (MeasurableSet.of_discrete)).mpr (hfinite.mono fun ω hω =>
          FiniteConductanceNetwork.exitVertex_not_mem hω)
    have hbound : ∀ᵐ w ∂HM, ‖g w - H ((G.tiling n).pos w)‖ ≤ η / 4 := by
      filter_upwards [hae] with w hw
      have hwb : (w : (G.tiling n).V) ∈ (G.tiling n).boundaryVertices U := ((G.tiling n).closedVertex_not_interior_iff U w).mp hw
      have hg : g w = hC (S.point n ⟨w, hwb⟩) :=
        S.boundaryData_apply_boundary hC n ⟨w, hwb⟩
      rw [hg, ← hHeq _ (S.mem_closure n ⟨w, hwb⟩), Real.norm_eq_abs, abs_sub_comm]
      obtain ⟨u, huU, hdist⟩ := (G.tiling n).boundaryVertices_near_interior hwb hmesh.1
      have hd' : dist ((G.tiling n).pos w) (S.point n ⟨w, hwb⟩) < ε₀ := by
        calc _ ≤ dist ((G.tiling n).pos w) ((G.tiling n).pos u) := S.isNearest n ⟨w, hwb⟩ _ (subset_closure huU)
          _ ≤ 2 * (G.tiling n).mesh.toReal := hdist
          _ < ε₀ := by linarith [hmesh.2]
      exact (Real.dist_eq _ _ ▸ hosc hd').le
    have hint := norm_integral_le_of_norm_le_const hbound
    rw [probReal_univ, mul_one] at hint
    rw [← integral_sub (Integrable.of_finite) (Integrable.of_finite)]
    exact hint
  -- Step 2: Theorem A compares the endpoint means of `H`.
  have hstep2 : |(∫ w, H ((G.tiling n).pos w) ∂HM) -
      ∫ x, H x ∂((stoppedBrownianLaw U ((G.tiling n).pos v) μ).map CurveSpace.endPoint)| ≤ η / 2 := by
    have hmap : (∫ w, H ((G.tiling n).pos w) ∂HM) =
        ∫ x, H x ∂((walkLaw n ((G.tiling n).pos v)).map CurveSpace.endPoint) := by
      rw [hend, integral_map (measurable_of_finite _).aemeasurable
        H.continuous.aestronglyMeasurable]
    rw [hmap]
    have hBMprob : IsProbabilityMeasure (stoppedBrownianLaw U ((G.tiling n).pos v) μ) :=
      stoppedBrownianLaw_isProbabilityMeasure hUopen _ μ
    have hlp : levyProkhorovEDist ((walkLaw n ((G.tiling n).pos v)).map CurveSpace.endPoint)
        ((stoppedBrownianLaw U ((G.tiling n).pos v) μ).map CurveSpace.endPoint) < ENNReal.ofReal ε := by
      refine (levyProkhorovEDist_endpoint_map_le _ _).trans_lt
        ((hLP ((G.tiling n).pos v) hv _ (hwn ((G.tiling n).pos v))).trans_lt ?_)
      exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr (half_lt_self hε)
    have := abs_integral_sub_integral_le_of_levyProkhorovEDist_lt _ _ hε hlp H
      (fun x y hxy => (Real.dist_eq _ _ ▸ hosc (hxy.trans_le hεε₀)).le)
    linarith
  -- Step 3: the Brownian mean of `H` is `h_C(v)`.
  have hstep3 : (∫ x, H x ∂((stoppedBrownianLaw U ((G.tiling n).pos v) μ).map CurveSpace.endPoint)) =
      hC ((G.tiling n).pos v) := by
    rw [← integral_stoppedBrownian_endPoint_of_continuousOn hd hμ hUopen hUb hharm hcont hv]
    apply integral_congr_ae
    filter_upwards [standardBrownianLaw_stopped_endPoint_ae_mem_frontier hd hμ hUopen hUb hv]
      with x hx
    exact hHeq x (frontier_subset_closure hx)
  rw [← hrepr, ← hstep3]
  calc |(∫ w, g w ∂HM) - ∫ x, H x ∂((stoppedBrownianLaw U ((G.tiling n).pos v) μ).map CurveSpace.endPoint)|
      ≤ |(∫ w, g w ∂HM) - ∫ w, H ((G.tiling n).pos w) ∂HM| + |(∫ w, H ((G.tiling n).pos w) ∂HM) -
          ∫ x, H x ∂((stoppedBrownianLaw U ((G.tiling n).pos v) μ).map CurveSpace.endPoint)| :=
        abs_sub_le _ _ _
    _ ≤ η / 4 + η / 2 := add_le_add hstep1 hstep2
    _ ≤ η := by linarith

/-- **Theorem B** (`theorem:convergence-of-the-dirichlet-problem`), both branches. -/
theorem theoremB : TheoremBStatement := ⟨theoremB_part_a, theoremB_part_b⟩

end SpherePackings
