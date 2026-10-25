module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/Section4BallExitLevyProkhorov.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.Section4BallExitConvergence
public import BouRabeeGwynne.Section4BrownianBallKernel
public import BouRabeeGwynne.Section4UniformExitTopology

@[expose] public section

/-! Uniform LP convergence of the actual exit measures from a fixed ball,
on compact sets of interior starting points. -/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology Classical BoundedContinuousFunction

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d) (U : Set (Euc d))

/-- Finite geometric graph closure and structural access to its boundary. -/
def HasFiniteAccessibleRegion : Prop :=
  ∃ hfin : (T.closedVertices U).Finite,
    letI : Fintype (T.closedVertices U) := hfin.fintype
    (T.finiteNetwork (T.closedVertices U)).BoundaryAccessible (T.finiteInterior U)

/-- The actual exit probability, with its finite presentation chosen from
the proved structural well-posedness of the region. -/
noncomputable def spatialExitProbability (hg : T.HasFiniteAccessibleRegion U)
    (v : T.V) (hv : v ∈ T.closedVertices U) : ProbabilityMeasure (Euc d) := by
  letI : Fintype (T.closedVertices U) := hg.choose.fintype
  letI : MeasurableSpace (T.closedVertices U) := ⊤
  exact ⟨T.spatialHarmonicMeasure U hg.choose_spec ⟨v, hv⟩, inferInstance⟩

/-- The chosen presentation is the same actual spatial exit measure as any
finite presentation obtained in the convergence estimates. -/
theorem spatialExitProbability_eq (hg : T.HasFiniteAccessibleRegion U)
    (hfin : (T.closedVertices U).Finite)
    (v : T.V) (hv : v ∈ T.closedVertices U) :
    letI : Fintype (T.closedVertices U) := hfin.fintype
    letI : MeasurableSpace (T.closedVertices U) := ⊤
    ∀ ha : (T.finiteNetwork (T.closedVertices U)).BoundaryAccessible (T.finiteInterior U),
      (T.spatialExitProbability U hg v hv : Measure (Euc d)) =
        T.spatialHarmonicMeasure U ha ⟨v, hv⟩ := by
  intro ha
  rfl

end BouRabeeGwynne.OrthogonalTiling

namespace BouRabeeGwynne

/-- The actual conductance-walk exit laws from one fixed ball converge in LP
distance uniformly over vertices whose positions belong to a fixed compact
subset of the ball. Finiteness and boundary accessibility are conclusions. -/
theorem eventually_ball_exit_levyProkhorov_error {d : ℕ} (hd : 1 ≤ d)
    (G : TilingSequence d) (N : NearestVertexData G) (c : Euc d) {r : ℝ} (hr : 0 < r)
    (hUD : HasAmbientCollar (Metric.ball c r) G.domain)
    (happrox : N.ApproximationCondition) (hreg : PaperRegularity G)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {K : Set (Euc d)} (hK : IsCompact K) (hKU : K ⊆ Metric.ball c r) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∃ hg : (G.tiling n).HasFiniteAccessibleRegion (Metric.ball c r),
        ∀ v : (G.tiling n).V, ∀ hv : v ∈ (G.tiling n).interiorVertices (Metric.ball c r),
          (G.tiling n).pos v ∈ K →
          levyProkhorovDist
            ((G.tiling n).spatialExitProbability (Metric.ball c r) hg v
              ((G.tiling n).interiorVertices_subset_closedVertices _ hv) : Measure (Euc d))
            (brownianSpatialHarmonicMeasure (Metric.ball c r) Metric.isOpen_ball μ hμ
              ((G.tiling n).pos v) : Measure (Euc d)) < ε := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let V : ℕ → Type _ := fun n => {v : (G.tiling n).V //
    v ∈ (G.tiling n).interiorVertices (Metric.ball c r) ∧ (G.tiling n).pos v ∈ K}
  let p : ∀ n, V n → K := fun n v => ⟨(G.tiling n).pos v, v.property.2⟩
  let ν : K → ProbabilityMeasure (Euc d) := fun x =>
    brownianSpatialHarmonicMeasure (Metric.ball c r) Metric.isOpen_ball μ hμ x
  have hν : Continuous ν := by
    have hinc : Continuous (fun x : K => (⟨x.val, hKU x.property⟩ : Metric.ball c r)) :=
      continuous_subtype_val.subtype_mk _
    exact (continuous_brownianBallHarmonicMeasure hd hμ c hr).comp hinc
  let μd : ∀ n, V n → ProbabilityMeasure (Euc d) := fun n v =>
    if hg : (G.tiling n).HasFiniteAccessibleRegion (Metric.ball c r) then
      (G.tiling n).spatialExitProbability (Metric.ball c r) hg v
        ((G.tiling n).interiorVertices_subset_closedVertices _ v.property.1)
    else ν (p n v)
  have hgood : ∀ᶠ n in atTop,
      (G.tiling n).HasFiniteAccessibleRegion (Metric.ball c r) := by
    filter_upwards [eventually_ball_exit_test_error hd G N c hr hUD happrox hreg hμ
      (fun _ => 0) continuous_const zero_lt_one] with n hn
    obtain ⟨hfin, ha, _⟩ := hn
    exact ⟨hfin, ha⟩
  have htest : ∀ f : Euc d →ᵇ ℝ, ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
      ∀ v : V n, |(∫ x, f x ∂(μd n v : Measure (Euc d))) -
        ∫ x, f x ∂(ν (p n v) : Measure (Euc d))| < η := by
    intro f η hη
    filter_upwards [hgood, eventually_ball_exit_test_error hd G N c hr hUD happrox hreg hμ
      f f.continuous (half_pos hη)] with n hg hn
    obtain ⟨hfin, hdata⟩ := hn
    letI : Fintype ((G.tiling n).closedVertices (Metric.ball c r)) := hfin.fintype
    letI : MeasurableSpace ((G.tiling n).closedVertices (Metric.ball c r)) := ⊤
    obtain ⟨ha, hbound⟩ := hdata
    intro v
    let vr : (G.tiling n).closedVertices (Metric.ball c r) :=
      ⟨v.val, (G.tiling n).interiorVertices_subset_closedVertices _ v.property.1⟩
    have herr := (hbound vr v.property.1).trans_lt (half_lt_self hη)
    simpa only [μd, dif_pos hg,
      (G.tiling n).spatialExitProbability_eq _ hg hfin _ _ ha, ν, p, vr] using herr
  have hLP := uniform_levyProkhorovDist_of_uniform_test_error V p μd ν hν htest
  intro ε hε
  filter_upwards [hgood, hLP ε hε] with n hg hn
  refine ⟨hg, ?_⟩
  intro v hv hvK
  simpa only [μd, dif_pos hg, ν, p] using hn ⟨v, hv, hvK⟩

end BouRabeeGwynne
