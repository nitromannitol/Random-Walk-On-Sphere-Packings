module

-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne (file
-- `BouRabeeGwynne/Section4BallHarmonicMeasure.lean` at commit cf73d6e): the declarations of that
-- file that use the regularity hypothesis `PaperRegularity G`, with the hypothesis replaced by the
-- localized Assumption D `TilingAssumptionD G` and deprecated names updated; the other declarations
-- are imported. The two theorems are stated for a ball `U = Metric.ball c r`, the case Assumption D
-- covers.
public import BouRabeeGwynne.Section4BallHarmonicMeasure
public import SpherePackings.Support.Section4.AssumptionD

@[expose] public section

/-! Section 4 of rw-spheres.tex under the localized Assumption D: the declarations of
leobon12's `BouRabeeGwynne.Section4BallHarmonicMeasure` that use the regularity hypothesis. -/

open MeasureTheory ProbabilityTheory
open scoped Classical Topology ENNReal

-- The copied proofs keep leobon12's `letI` style.
set_option linter.style.haveILetI false

namespace SpherePackings.AssumptionD

open BouRabeeGwynne

/-- Assumption D gives, on a ball, a uniform bound for the actual exit expectation
of a continuous function harmonic near the closure. Finiteness and access to
the graph boundary are derived from the geometric approximation assumptions. -/
theorem eventually_spatialHarmonicMeasure_harmonic_error {d : ℕ} (hd : 1 ≤ d)
    (G : TilingSequence d) (N : NearestVertexData G)
    {c : Euc d} {r : ℝ} (hr : 0 < r) (U : Set (Euc d)) (hUball : U = Metric.ball c r)
    (h : Euc d → ℝ) (hDomain : IsDomain U) (hUb : Bornology.IsBounded U)
    (hUD : HasAmbientCollar U G.domain) (happrox : N.ApproximationCondition)
    (hAD : TilingAssumptionD G) (hh : HarmonicNearClosure h U) (hcont : Continuous h)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n in Filter.atTop, ∃ hfin : ((G.tiling n).closedVertices U).Finite,
      letI : Fintype ((G.tiling n).closedVertices U) := hfin.fintype
      letI : MeasurableSpace ((G.tiling n).closedVertices U) := ⊤
      ∃ ha : ((G.tiling n).finiteNetwork ((G.tiling n).closedVertices U)).BoundaryAccessible
          ((G.tiling n).finiteInterior U),
        ∀ v : (G.tiling n).closedVertices U, v ∈ (G.tiling n).finiteInterior U →
          |(∫ x, h x ∂(G.tiling n).spatialHarmonicMeasure U ha v) -
              h ((G.tiling n).pos v)| ≤ η := by
  have hB : DirichletApproximationTarget G U h (fun n v => h ((G.tiling n).pos v)) := by
    subst hUball
    exact hAD c r h hr hUD hh
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

/-- A continuum boundary-collar approximation transfers the proved harmonic
test estimate to an actual continuous test of the discrete exit measure.
The two-mesh overshoot is derived from the original tiling geometry. -/
theorem eventually_spatialHarmonicMeasure_collar_error {d : ℕ} (hd : 1 ≤ d)
    (G : TilingSequence d) (N : NearestVertexData G)
    {c : Euc d} {r : ℝ} (hr : 0 < r) (U : Set (Euc d)) (hUball : U = Metric.ball c r)
    (f h : Euc d → ℝ)
    (hDomain : IsDomain U) (hUb : Bornology.IsBounded U)
    (hUD : HasAmbientCollar U G.domain) (happrox : N.ApproximationCondition)
    (hAD : TilingAssumptionD G) (hh : HarmonicNearClosure h U)
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
  filter_upwards [eventually_spatialHarmonicMeasure_harmonic_error hd G N hr U hUball h
    hDomain hUb hUD happrox hAD hh hcont hρ,
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

end SpherePackings.AssumptionD
