module

-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne (file
-- `BouRabeeGwynne/BackwardExitPartitions.lean` at commit cf73d6e): the declarations of that file
-- that use the regularity hypothesis `PaperRegularity G`, with the hypothesis replaced by the
-- localized Assumption D `TilingAssumptionD G` and deprecated names updated; the other declarations
-- are imported.
public import BouRabeeGwynne.BackwardExitPartitions
public import SpherePackings.Support.Section4.BallExitCouplingInputs

@[expose] public section

/-! Section 4 of rw-spheres.tex under the localized Assumption D: the declarations of
leobon12's `BouRabeeGwynne.BackwardExitPartitions` that use the regularity hypothesis. -/

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology Classical

-- The copied proofs keep leobon12's `letI` style.
set_option linter.style.haveILetI false

namespace SpherePackings.AssumptionD

open BouRabeeGwynne

private structure ExitPartitionStage {d : ℕ} {J : Type*} (G : TilingSequence d)
    (c : J → Euc d) (r : ℝ) (Q : Set (Euc d))
    (μ : Measure (BrownianPath d)) (hμ : IsStandardBrownianLaw μ) (a b : ℝ) where
  card : ℕ
  cell : Fin card → Set (Euc d)
  modulus : ℝ
  modulus_pos : 0 < modulus
  disjoint : Pairwise (fun i j => Disjoint (cell i) (cell j))
  cover : Q ⊆ ⋃ i, cell i
  measurable : ∀ i, MeasurableSet (cell i)
  bounded : ∀ i, Bornology.IsBounded (cell i)
  diameter : ∀ i, ∀ x ∈ cell i, ∀ y ∈ cell i, dist x y ≤ min a (r / 4)
  frontier_null : ∀ j z, z ∈ ball (c j) r → ∀ i,
    ((stoppedBrownianLaw (ball (c j) r) z μ).map CurveSpace.endPoint)
      (frontier (cell i)) = 0
  comparison : ∀ᶠ n in atTop, ∀ j,
    ∃ hg : (G.tiling n).HasFiniteAccessibleRegion (ball (c j) r),
      ∀ v : (G.tiling n).V,
        ∀ hv : v ∈ (G.tiling n).interiorVertices (ball (c j) r),
          (G.tiling n).pos v ∈ closedBall (c j) (r / 2) →
          ∀ y ∈ closedBall (c j) (r / 2), dist ((G.tiling n).pos v) y ≤ modulus →
          ∀ i,
            |(((G.tiling n).spatialExitProbability (ball (c j) r) hg v
                ((G.tiling n).interiorVertices_subset_closedVertices _ hv) :
                Measure (Euc d)) (cell i)).toReal -
              ((brownianSpatialHarmonicMeasure (ball (c j) r) isOpen_ball μ hμ y :
                Measure (Euc d)) (cell i)).toReal| ≤ b / (card + 1)

private theorem exists_exitPartitionStage {d : ℕ} (hd : 1 ≤ d)
    {J : Type*} [Fintype J] (G : TilingSequence d) (N : NearestVertexData G)
    (c : J → Euc d) {r : ℝ} (hr : 0 < r)
    (hUD : ∀ j, HasAmbientCollar (ball (c j) r) G.domain)
    (happrox : N.ApproximationCondition) (hAD : TilingAssumptionD G)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {Q : Set (Euc d)} (hQ : IsCompact Q) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {η : ℝ} (hη : 0 < η) :
    ∃ P : ExitPartitionStage G c r Q μ hμ a b,
      ∀ i, ∀ x ∈ P.cell i, ∀ y ∈ P.cell i, dist x y ≤ η := by
  have hbase : 0 < min a (r / 4) := lt_min ha (by positivity)
  obtain ⟨m, E, hdisj, hcover, hmeas, hbounded, hdiam, hnull⟩ :=
    exists_common_brownian_exit_continuity_cells hd hμ (fun j => ball (c j) r)
      (fun _ => isOpen_ball) (fun _ => isBounded_ball) hQ (lt_min hbase hη)
  have hsingle : ∀ j, ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop,
      ∃ hg : (G.tiling n).HasFiniteAccessibleRegion (ball (c j) r),
        ∀ v : (G.tiling n).V,
          ∀ hv : v ∈ (G.tiling n).interiorVertices (ball (c j) r),
            (G.tiling n).pos v ∈ closedBall (c j) (r / 2) →
            ∀ y ∈ closedBall (c j) (r / 2), dist ((G.tiling n).pos v) y ≤ δ → ∀ i,
              |(((G.tiling n).spatialExitProbability (ball (c j) r) hg v
                  ((G.tiling n).interiorVertices_subset_closedVertices _ hv) :
                  Measure (Euc d)) (E i)).toReal -
                ((brownianSpatialHarmonicMeasure (ball (c j) r) isOpen_ball μ hμ y :
                  Measure (Euc d)) (E i)).toReal| ≤ b / (m + 1) := by
    intro j
    exact eventually_ball_exit_nearby_cell_error hd G N (c j) hr (hUD j) happrox hAD
      hμ (isCompact_closedBall (c j) (r / 2)) (closedBall_subset_ball (half_lt_self hr)) E
      (fun i z hz => hnull j z (closedBall_subset_ball (half_lt_self hr) hz) i)
      (b / (m + 1)) (by positivity)
  choose δ hδ hcompare using hsingle
  let f : Option J → ℝ := fun j => Option.elim j 1 δ
  let δ₀ : ℝ := Finset.univ.inf' Finset.univ_nonempty f
  have hδ₀ : 0 < δ₀ := by
    apply (Finset.lt_inf'_iff Finset.univ_nonempty).mpr
    intro j hj
    cases j with
    | none => exact zero_lt_one
    | some j => exact hδ j
  have hδle (j : J) : δ₀ ≤ δ j :=
    Finset.inf'_le f (Finset.mem_univ (some j))
  refine ⟨{
    card := m
    cell := E
    modulus := δ₀
    modulus_pos := hδ₀
    disjoint := hdisj
    cover := hcover
    measurable := hmeas
    bounded := hbounded
    diameter := fun i x hx y hy =>
      (hdiam i x hx y hy).le.trans (min_le_left _ _)
    frontier_null := hnull
    comparison := ?_ }, ?_⟩
  · filter_upwards [Filter.eventually_all.mpr hcompare] with n hn
    intro j
    obtain ⟨hg, hbound⟩ := hn j
    exact ⟨hg, fun v hv hvK y hy hdist i =>
      hbound v hv hvK y hy (hdist.trans (hδle j)) i⟩
  · exact fun i x hx y hy => (hdiam i x hx y hy).le.trans (min_le_right _ _)

/-- For finitely many fixed balls and a fixed finite number of excursion
stages, choose common continuity cells backwards. The earlier stage cells fit
inside the next stage's spatial comparison tolerance. A single eventual mesh
index works for every stage and ball. -/
theorem exists_backward_ball_exit_partitions {d : ℕ} (hd : 1 ≤ d)
    {J : Type*} [Fintype J] (G : TilingSequence d) (N : NearestVertexData G)
    (c : J → Euc d) {r : ℝ} (hr : 0 < r)
    (hUD : ∀ j, HasAmbientCollar (ball (c j) r) G.domain)
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
      ∀ᶠ n in atTop, ∀ j,
        ∃ hg : (G.tiling n).HasFiniteAccessibleRegion (ball (c j) r),
          ∀ i, ∀ v : (G.tiling n).V,
            ∀ hv : v ∈ (G.tiling n).interiorVertices (ball (c j) r),
              (G.tiling n).pos v ∈ closedBall (c j) (r / 2) →
              ∀ y ∈ closedBall (c j) (r / 2), dist ((G.tiling n).pos v) y ≤ δ i →
              ∀ k,
                |(((G.tiling n).spatialExitProbability (ball (c j) r) hg v
                    ((G.tiling n).interiorVertices_subset_closedVertices _ hv) :
                    Measure (Euc d)) (E i k)).toReal -
                  ((brownianSpatialHarmonicMeasure (ball (c j) r) isOpen_ball μ hμ y :
                    Measure (Euc d)) (E i k)).toReal| ≤ b / (m i + 1) := by
  let S := ExitPartitionStage G c r Q μ hμ a b
  have hstage (η : ℝ) (hη : 0 < η) :
      ∃ P : S, ∀ k, ∀ x ∈ P.cell k, ∀ y ∈ P.cell k, dist x y ≤ η :=
    exists_exitPartitionStage hd G N c hr hUD happrox hAD hμ hQ ha hb hη
  let start : S := (hstage 1 zero_lt_one).choose
  let next : S → S := fun P => (hstage P.modulus P.modulus_pos).choose
  have hnext (P : S) :
      ∀ k, ∀ x ∈ (next P).cell k, ∀ y ∈ (next P).cell k, dist x y ≤ P.modulus :=
    (hstage P.modulus P.modulus_pos).choose_spec
  let seq : ℕ → S := Nat.rec start (fun _ P => next P)
  let P : Fin (L + 1) → S := fun i => seq (L - i.val)
  have hback (i : Fin L) : ∀ k, ∀ x ∈ (P i.castSucc).cell k,
      ∀ y ∈ (P i.castSucc).cell k, dist x y ≤ (P i.succ).modulus := by
    change ∀ k, ∀ x ∈ (seq (L - i.val)).cell k,
      ∀ y ∈ (seq (L - i.val)).cell k, dist x y ≤ (seq (L - (i.val + 1))).modulus
    have hidx : L - i.val = (L - (i.val + 1)) + 1 := by omega
    rw [hidx]
    exact hnext (seq (L - (i.val + 1)))
  refine ⟨fun i => (P i).card, fun i => (P i).cell, fun i => (P i).modulus,
    fun i => (P i).modulus_pos, fun i => (P i).disjoint, fun i => (P i).cover,
    fun i => (P i).measurable, fun i => (P i).bounded, fun i => (P i).diameter,
    hback, fun i => (P i).frontier_null, ?_⟩
  filter_upwards [Filter.eventually_all.mpr (fun i => (P i).comparison)] with n hn
  intro j
  obtain ⟨hg, _⟩ := hn (0 : Fin (L + 1)) j
  refine ⟨hg, ?_⟩
  intro i
  obtain ⟨hg', hbound⟩ := hn i j
  exact hbound

end SpherePackings.AssumptionD
