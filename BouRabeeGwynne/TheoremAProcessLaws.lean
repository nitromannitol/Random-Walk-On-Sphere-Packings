-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/TheoremAProcessLaws.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.EuclideanWienerLaw
import BouRabeeGwynne.BrownianFiniteExit
import BouRabeeGwynne.StoppedBrownianMeasurable
import BouRabeeGwynne.StoppedTilingWalkLaw
import BouRabeeGwynne.Section3WellPosed
import BouRabeeGwynne.CoordinateHyperplane

/-! Construction and well-definedness of the actual process laws in Theorem A.
The uniform walk-to-Brownian convergence is a separate remaining conclusion. -/

open scoped Classical ENNReal Topology
open MeasureTheory

namespace BouRabeeGwynne

theorem exists_standardBrownianLaw_with_stopped_laws {d : ℕ} (hd : 1 ≤ d)
    {U : Set (Euc d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U) :
    ∃ μ : Measure (BrownianPath d), IsStandardBrownianLaw μ ∧
      ∀ z ∈ U, AEMeasurable (stoppedBrownianCurve U z) μ ∧
        (∀ᵐ ω ∂μ, continuousExitTime U z ω ≠ ∞) ∧
        IsProbabilityMeasure (stoppedBrownianLaw U z μ) := by
  have hμ := isStandardBrownianLaw_euclideanWienerLaw d
  letI : IsProbabilityMeasure (euclideanWienerLaw d) := hμ.1
  refine ⟨euclideanWienerLaw d, hμ, ?_⟩
  intro z _
  exact ⟨(measurable_stoppedBrownianCurve hU z).aemeasurable,
    standardBrownianLaw_ae_finiteExit hd hμ hUb z,
    stoppedBrownianLaw_isProbabilityMeasure hU z (euclideanWienerLaw d)⟩

/-- The approximation and ambient collar suffice for eventual construction of
the actual stopped conductance walks, including nearest vertices outside U. -/
theorem NearestVertexData.exists_eventually_stoppedWalkLaws {d : ℕ} (hd : 1 ≤ d)
    {G : TilingSequence d} (N : NearestVertexData G) (U : Set (Euc d))
    (hUb : Bornology.IsBounded U) (hUD : HasAmbientCollar U G.domain)
    (happrox : N.ApproximationCondition) :
    ∃ walkLaw : ℕ → Euc d → Measure (CurveSpace d),
      ∀ᶠ n in Filter.atTop, ∀ z : Euc d,
        IsStoppedTilingWalkLaw (G.tiling n) U (N.vertex n z) (walkLaw n z) := by
  obtain ⟨e, he⟩ : ∃ e : Euc d, e ≠ 0 := by
    cases d with
    | zero => omega
    | succ n => exact ⟨coordinateAxis (0 : Fin (n + 1)), coordinateAxis_ne_zero 0⟩
  have hevent : ∀ᶠ n in Filter.atTop, ∀ z : Euc d,
      ∃ μ, IsStoppedTilingWalkLaw (G.tiling n) U (N.vertex n z) μ := by
    filter_upwards [N.eventually_closedVertices_finite happrox hUb hUD,
      N.eventually_interior_cells_subset_domain happrox hUb hUD] with n hfin hcells
    letI : Fintype ((G.tiling n).closedVertices U) := hfin.fintype
    have hneighbors : ∀ v ∈ (G.tiling n).finiteInterior U, ∀ w,
        (G.tiling n).adj v w → w ∈ (G.tiling n).closedVertices U := by
      intro v hv w hvw
      exact (G.tiling n).neighbor_mem_closedVertices hv hvw
    have hcellD : ∀ v ∈ (G.tiling n).finiteInterior U,
        ((G.tiling n).cell v).carrier ⊆ interior (G.tiling n).domain := by
      intro v hv
      simpa only [G.common_domain n] using hcells v hv
    have ha := (G.tiling n).finiteNetwork_boundaryAccessible_of_cell_interior
      hd e he ((G.tiling n).closedVertices U) ((G.tiling n).finiteInterior U)
      hneighbors hcellD
    intro z
    exact (G.tiling n).exists_isStoppedTilingWalkLaw U ha (N.vertex n z)
  let walkLaw : ℕ → Euc d → Measure (CurveSpace d) := fun n z =>
    if h : ∃ μ, IsStoppedTilingWalkLaw (G.tiling n) U (N.vertex n z) μ then
      Classical.choose h else 0
  refine ⟨walkLaw, ?_⟩
  filter_upwards [hevent] with n hn
  intro z
  simpa only [walkLaw, dif_pos (hn z)] using Classical.choose_spec (hn z)

end BouRabeeGwynne
