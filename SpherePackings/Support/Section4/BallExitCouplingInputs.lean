module

-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne (file
-- `BouRabeeGwynne/Section4BallExitCouplingInputs.lean` at commit cf73d6e): the declarations of that
-- file that use the regularity hypothesis `PaperRegularity G`, with the hypothesis replaced by the
-- localized Assumption D `TilingAssumptionD G` and deprecated names updated; the other declarations
-- are imported.
public import BouRabeeGwynne.Section4BallExitCouplingInputs
public import SpherePackings.Support.Section4.BallExitLevyProkhorov

@[expose] public section

/-! Section 4 of rw-spheres.tex under the localized Assumption D: the declarations of
leobon12's `BouRabeeGwynne.Section4BallExitCouplingInputs` that use the regularity hypothesis. -/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology Classical

-- The copied proofs keep leobon12's `letI` style.
set_option linter.style.haveILetI false

namespace SpherePackings.AssumptionD

open BouRabeeGwynne

/-- A uniform spatial modulus compares the discrete exit from an interior
vertex with the Brownian exit from any nearby point in the same inner compact
set. The modulus is chosen before the eventual mesh index. -/
theorem eventually_ball_exit_nearby_levyProkhorov_error {d : ℕ} (hd : 1 ≤ d)
    (G : TilingSequence d) (N : NearestVertexData G) (c : Euc d) {r : ℝ} (hr : 0 < r)
    (hUD : HasAmbientCollar (Metric.ball c r) G.domain)
    (happrox : N.ApproximationCondition) (hAD : TilingAssumptionD G)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {K : Set (Euc d)} (hK : IsCompact K) (hKU : K ⊆ Metric.ball c r) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop,
      ∃ hg : (G.tiling n).HasFiniteAccessibleRegion (Metric.ball c r),
        ∀ v : (G.tiling n).V, ∀ hv : v ∈ (G.tiling n).interiorVertices (Metric.ball c r),
          (G.tiling n).pos v ∈ K → ∀ y ∈ K, dist ((G.tiling n).pos v) y ≤ δ →
          levyProkhorovDist
            ((G.tiling n).spatialExitProbability (Metric.ball c r) hg v
              ((G.tiling n).interiorVertices_subset_closedVertices _ hv) : Measure (Euc d))
            (brownianSpatialHarmonicMeasure (Metric.ball c r) Metric.isOpen_ball μ hμ y :
              Measure (Euc d)) ≤ ε := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let ν : K → ProbabilityMeasure (Euc d) := fun x =>
    brownianSpatialHarmonicMeasure (Metric.ball c r) Metric.isOpen_ball μ hμ x
  have hν : Continuous ν :=
    (continuous_brownianBallHarmonicMeasure hd hμ c hr).comp
      (continuous_subtype_val.subtype_mk (fun x : K => hKU x.property))
  have hνLP : Continuous (fun x => LevyProkhorov.ofMeasure (ν x)) :=
    LevyProkhorov.continuous_ofMeasure_probabilityMeasure.comp hν
  intro ε hε
  obtain ⟨δ, hδ, hcontrol⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hνLP) (ε / 2) (half_pos hε)
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  filter_upwards [eventually_ball_exit_levyProkhorov_error hd G N c hr hUD happrox hAD
    hμ hK hKU (ε / 2) (half_pos hε)] with n hn
  obtain ⟨hg, hsame⟩ := hn
  refine ⟨hg, ?_⟩
  intro v hv hvK y hy hdist
  have hnear : levyProkhorovDist
      (ν ⟨(G.tiling n).pos v, hvK⟩ : Measure (Euc d))
      (ν ⟨y, hy⟩ : Measure (Euc d)) < ε / 2 := by
    have hdist' : dist (⟨(G.tiling n).pos v, hvK⟩ : K) ⟨y, hy⟩ < δ :=
      hdist.trans_lt (half_lt_self hδ)
    simpa only [LevyProkhorov.dist_probabilityMeasure_def] using hcontrol hdist'
  calc
    _ ≤ levyProkhorovDist
        ((G.tiling n).spatialExitProbability (Metric.ball c r) hg v
          ((G.tiling n).interiorVertices_subset_closedVertices _ hv) : Measure (Euc d))
        (ν ⟨(G.tiling n).pos v, hvK⟩ : Measure (Euc d)) +
        levyProkhorovDist (ν ⟨(G.tiling n).pos v, hvK⟩ : Measure (Euc d))
          (ν ⟨y, hy⟩ : Measure (Euc d)) := levyProkhorovDist_triangle _ _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (hsame v hv hvK).le hnear.le
    _ = ε := add_halves ε

/-- For an already fixed finite family of common continuity cells, actual
discrete and Brownian exits have uniformly close cell probabilities at nearby
inner starting points. This does not assert a partition-independent modulus. -/
theorem eventually_ball_exit_nearby_cell_error {d : ℕ} (hd : 1 ≤ d)
    (G : TilingSequence d) (N : NearestVertexData G) (c : Euc d) {r : ℝ} (hr : 0 < r)
    (hUD : HasAmbientCollar (Metric.ball c r) G.domain)
    (happrox : N.ApproximationCondition) (hAD : TilingAssumptionD G)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {K : Set (Euc d)} (hK : IsCompact K) (hKU : K ⊆ Metric.ball c r)
    {ι : Type*} [Fintype ι] (S : ι → Set (Euc d))
    (hnull : ∀ i, ∀ z ∈ K,
      (brownianSpatialHarmonicMeasure (Metric.ball c r) Metric.isOpen_ball μ hμ z :
        Measure (Euc d)) (frontier (S i)) = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop,
      ∃ hg : (G.tiling n).HasFiniteAccessibleRegion (Metric.ball c r),
        ∀ v : (G.tiling n).V, ∀ hv : v ∈ (G.tiling n).interiorVertices (Metric.ball c r),
          (G.tiling n).pos v ∈ K → ∀ y ∈ K, dist ((G.tiling n).pos v) y ≤ δ → ∀ i,
          |(((G.tiling n).spatialExitProbability (Metric.ball c r) hg v
              ((G.tiling n).interiorVertices_subset_closedVertices _ hv) : Measure (Euc d))
              (S i)).toReal -
            ((brownianSpatialHarmonicMeasure (Metric.ball c r) Metric.isOpen_ball μ hμ y :
              Measure (Euc d)) (S i)).toReal| ≤ ε := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let V : ℕ → Type _ := fun n => {v : (G.tiling n).V //
    v ∈ (G.tiling n).interiorVertices (Metric.ball c r) ∧ (G.tiling n).pos v ∈ K}
  let p : ∀ n, V n → K := fun n v => ⟨(G.tiling n).pos v, v.property.2⟩
  let ν : K → ProbabilityMeasure (Euc d) := fun x =>
    brownianSpatialHarmonicMeasure (Metric.ball c r) Metric.isOpen_ball μ hμ x
  have hν : Continuous ν :=
    (continuous_brownianBallHarmonicMeasure hd hμ c hr).comp
      (continuous_subtype_val.subtype_mk (fun x : K => hKU x.property))
  let μd : ∀ n, V n → ProbabilityMeasure (Euc d) := fun n v =>
    if hg : (G.tiling n).HasFiniteAccessibleRegion (Metric.ball c r) then
      (G.tiling n).spatialExitProbability (Metric.ball c r) hg v
        ((G.tiling n).interiorVertices_subset_closedVertices _ v.property.1)
    else ν (p n v)
  have hgood : ∀ᶠ n in atTop,
      (G.tiling n).HasFiniteAccessibleRegion (Metric.ball c r) := by
    filter_upwards [eventually_ball_exit_levyProkhorov_error hd G N c hr hUD happrox hAD
      hμ hK hKU 1 zero_lt_one] with n hn
    exact hn.choose
  have hLP : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ v : V n,
      levyProkhorovDist (μd n v : Measure (Euc d))
        (ν (p n v) : Measure (Euc d)) < η := by
    intro η hη
    filter_upwards [hgood, eventually_ball_exit_levyProkhorov_error hd G N c hr hUD
      happrox hAD hμ hK hKU η hη] with n hg hn
    obtain ⟨hg', hbound⟩ := hn
    intro v
    simpa only [μd, dite_eq_left hg, ν, p] using hbound v v.property.1 v.property.2
  intro ε hε
  obtain ⟨δ, hδ, hcell⟩ :=
    uniform_nearby_cell_mass_error_of_uniform_levyProkhorov_error V p μd ν hν hLP S
      (fun i z => hnull i z z.property) ε hε
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hgood, hcell] with n hg hn
  refine ⟨hg, ?_⟩
  intro v hv hvK y hy hdist i
  simpa only [μd, dite_eq_left hg, ν, p] using hn ⟨v, hv, hvK⟩ ⟨y, hy⟩ hdist i

end SpherePackings.AssumptionD
