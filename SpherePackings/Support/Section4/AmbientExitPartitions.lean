-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne (file
-- `BouRabeeGwynne/AmbientExitPartitions.lean` at commit cf73d6e): the declarations of that file
-- that use the regularity hypothesis `PaperRegularity G`, with the hypothesis replaced by the
-- localized Assumption D `TilingAssumptionD G` and deprecated names updated; the other declarations
-- are imported.
import BouRabeeGwynne.AmbientExitPartitions
import SpherePackings.Support.Section4.BackwardExitPartitions

/-! Section 4 of rw-spheres.tex under the localized Assumption D: the declarations of
leobon12's `BouRabeeGwynne.AmbientExitPartitions` that use the regularity hypothesis. -/

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped Classical Topology

-- The copied proofs keep leobon12's `letI` style.
set_option linter.style.haveILetI false

namespace SpherePackings.AssumptionD

open BouRabeeGwynne

private theorem eventually_ambient_finite_accessible {d : ℕ} (hd : 1 ≤ d)
    (G : TilingSequence d) (N : NearestVertexData G) (happrox : N.ApproximationCondition)
    {W : Set (Euc d)} (hW : Bornology.IsBounded W) (hWD : HasAmbientCollar W G.domain) :
    ∀ᶠ n in atTop, (G.tiling n).HasFiniteAccessibleRegion W := by
  obtain ⟨e, he, _⟩ := exists_unit_euc hd
  filter_upwards [N.eventually_closedVertices_finite happrox hW hWD,
    N.eventually_interior_cells_subset_domain happrox hW hWD] with n hfin hcells
  refine ⟨hfin, ?_⟩
  letI : Fintype ((G.tiling n).closedVertices W) := hfin.fintype
  apply (G.tiling n).finiteNetwork_boundaryAccessible_of_cell_interior hd e he
    ((G.tiling n).closedVertices W) ((G.tiling n).finiteInterior W)
  · intro v hv w hvw
    exact (G.tiling n).neighbor_mem_closedVertices hv hvw
  · intro v hv
    simpa only [G.common_domain n] using hcells v hv

/-- Backwards-chosen continuity cells compare exits on one actual finite
ambient network with the Brownian ball exits, simultaneously over all stages,
balls and nearby inner starting points. -/
theorem exists_backward_ambient_exit_partitions {d : ℕ} (hd : 1 ≤ d)
    {J : Type*} [Fintype J] (G : TilingSequence d) (N : NearestVertexData G)
    (c : J → Euc d) {r : ℝ} (hr : 0 < r)
    (W : Set (Euc d)) (hW : Bornology.IsBounded W) (hWD : HasAmbientCollar W G.domain)
    (hBW : ∀ j, ball (c j) r ⊆ W)
    (happrox : N.ApproximationCondition) (hAD : TilingAssumptionD G)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {Q : Set (Euc d)} (hQ : IsCompact Q) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (L : ℕ) :
    ∃ (m : Fin (L + 1) → ℕ) (E : ∀ i, Fin (m i) → Set (Euc d))
      (δ : Fin (L + 1) → ℝ),
      (∀ i, 0 < δ i) ∧
      (∀ i, Pairwise (fun k l => Disjoint (E i k) (E i l))) ∧
      (∀ i, Q ⊆ ⋃ k, E i k) ∧
      (∀ i k, MeasurableSet (E i k)) ∧
      (∀ i k, Bornology.IsBounded (E i k)) ∧
      (∀ i k, ∀ x ∈ E i k, ∀ y ∈ E i k, dist x y ≤ min a (r / 4)) ∧
      (∀ i : Fin L, ∀ k, ∀ x ∈ E i.castSucc k, ∀ y ∈ E i.castSucc k,
        dist x y ≤ δ i.succ) ∧
      (∀ i j z, z ∈ ball (c j) r → ∀ k,
        ((stoppedBrownianLaw (ball (c j) r) z μ).map CurveSpace.endPoint)
          (frontier (E i k)) = 0) ∧
      ∀ᶠ n in atTop, ∃ hfin : ((G.tiling n).closedVertices W).Finite,
        letI : Fintype ((G.tiling n).closedVertices W) := hfin.fintype
        letI : MeasurableSpace ((G.tiling n).closedVertices W) := ⊤
        ∃ _haccess : ((G.tiling n).finiteNetwork ((G.tiling n).closedVertices W)).BoundaryAccessible
            ((G.tiling n).finiteInterior W),
        ∃ _hA : ∀ v ∈ (G.tiling n).finiteInterior W,
            0 < ((G.tiling n).finiteNetwork ((G.tiling n).closedVertices W)).totalConductance v,
        ∃ hB : ∀ j, ∀ v ∈ ({v : (G.tiling n).closedVertices W | (G.tiling n).pos v ∈ ball (c j) r}),
            0 < ((G.tiling n).finiteNetwork ((G.tiling n).closedVertices W)).totalConductance v,
          ∀ i j, ∀ v : (G.tiling n).closedVertices W,
            (G.tiling n).pos v ∈ closedBall (c j) (r / 2) →
            ∀ y ∈ closedBall (c j) (r / 2), dist ((G.tiling n).pos v) y ≤ δ i → ∀ k,
              |(((((G.tiling n).finiteNetwork ((G.tiling n).closedVertices W)).discreteHarmonicMeasure
                  {w : (G.tiling n).closedVertices W | (G.tiling n).pos w ∈ ball (c j) r}
                  (hB j) v).map (fun w : (G.tiling n).closedVertices W => (G.tiling n).pos w))
                    (E i k)).toReal -
                (((stoppedBrownianLaw (ball (c j) r) y μ).map CurveSpace.endPoint)
                  (E i k)).toReal| ≤ b / (m i + 1) := by
  have hBD (j : J) : HasAmbientCollar (ball (c j) r) G.domain :=
    (closure_mono (hBW j)).trans hWD
  obtain ⟨m, E, δ, hδ, hdisj, hcover, hmeas, hbounded, hdiam, hback, hnull, herr⟩ :=
    exists_backward_ball_exit_partitions hd G N c hr hBD happrox hAD hμ hQ ha hb L
  refine ⟨m, E, δ, hδ, hdisj, hcover, hmeas, hbounded, hdiam, hback, hnull, ?_⟩
  filter_upwards [eventually_ambient_finite_accessible hd G N happrox hW hWD, herr]
    with n hgW hn
  obtain ⟨hfin, haccess⟩ := hgW
  refine ⟨hfin, ?_⟩
  letI : Fintype ((G.tiling n).closedVertices W) := hfin.fintype
  letI : MeasurableSpace ((G.tiling n).closedVertices W) := ⊤
  let hA := ((G.tiling n).finiteNetwork ((G.tiling n).closedVertices W)).totalConductance_pos_of_boundaryAccessible
    ((G.tiling n).finiteInterior W) haccess
  let hB : ∀ j, ∀ v ∈ ({v : (G.tiling n).closedVertices W | (G.tiling n).pos v ∈ ball (c j) r}),
      0 < ((G.tiling n).finiteNetwork ((G.tiling n).closedVertices W)).totalConductance v :=
    fun j v hv => hA v (hBW j hv)
  refine ⟨haccess, hA, hB, ?_⟩
  intro i j v hv y hy hnear k
  obtain ⟨hg, herror⟩ := hn j
  have hvball : (G.tiling n).pos v ∈ ball (c j) r :=
    closedBall_subset_ball (half_lt_self hr) hv
  have hbnd := herror i v.val hvball hv y hy hnear k
  rw [(G.tiling n).spatialExitProbability_eq_ambient_discreteHarmonicMeasure
    (hBW j) hg (hB j) v hvball] at hbnd
  exact hbnd

end SpherePackings.AssumptionD
