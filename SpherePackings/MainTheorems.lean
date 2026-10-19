import SpherePackings.Frozen.TheoremA
import SpherePackings.Frozen.TheoremBa
import SpherePackings.Frozen.TheoremBb
import SpherePackings.Frozen.Prop11Cells
import SpherePackings.Frozen.Prop11TheoremAB
import SpherePackings.Frozen.Theorem61Counterexample
import SpherePackings.Frozen.Theorem41
import SpherePackings.Frozen.Prop42General

/-!
# Main results

The main results of the formalization of *Random walk on sphere packings and Delaunay
triangulations in arbitrary dimension* (Ahmed Bou-Rabee and Ewain Gwynne, arXiv:2405.11673v2),
stated in full.  Each restates its frozen counterpart in `SpherePackings/Frozen/` and is proved by
`exact` of it, so the statements displayed here are the certified ones.

The statements of Theorems A and B are leobon12's
(https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne), with the
ambient collar `closure U ⊆ interior D`, a correction recorded in `CORRESPONDENCE.md`, and the
reading that every codimension-one contact of two cells is an edge.  Theorem A and Theorem B(a) are leobon12's
theorems; Theorem B(b), Proposition 1.1, Theorem 4.1, Proposition 4.2 and Theorem 6.1 are proved in
this repository (Theorem 4.1 from leobon12's proof of Theorem A).
-/

open MeasureTheory Metric Filter Set BouRabeeGwynne SpherePackings SpherePackings.Voronoi
open scoped ENNReal NNReal Topology

/-- **Theorem A** (`theorem:convergence-of-rw-trace`): convergence of the stopped conductance walks to stopped Brownian motion, modulo time parametrization, uniformly in the starting point. The certified statement is `SpherePackings.Frozen.theoremA`. -/
theorem SpherePackings.theorem_A :
  ∀ (d : ℕ), 1 ≤ d →
  ∀ (G : TilingSequence d) (N : NearestVertexData G) (U : Set (Euc d)),
    IsLipschitzDomain U → Bornology.IsBounded U → HasAmbientCollar U G.domain →
    N.ApproximationCondition → PaperRegularity G →
    ∃ μ : Measure (BrownianPath d),
      IsStandardBrownianLaw μ ∧
      (∀ z ∈ U,
        AEMeasurable (stoppedBrownianCurve U z) μ ∧
        (∀ᵐ ω ∂μ, continuousExitTime U z ω ≠ ∞) ∧
        IsProbabilityMeasure (stoppedBrownianLaw U z μ)) ∧
      ∃ walkLaw : ℕ → Euc d → Measure (CurveSpace d),
        (∀ᶠ n in Filter.atTop, ∀ z ∈ U,
          IsStoppedTilingWalkLaw (G.tiling n) U (N.vertex n z) (walkLaw n z)) ∧
        ∀ η : ℝ, 0 < η → ∀ᶠ n in Filter.atTop, ∀ z ∈ U,
          levyProkhorovEDist (walkLaw n z) (stoppedBrownianLaw U z μ) ≤
            ENNReal.ofReal η := by
  exact SpherePackings.Frozen.theoremA

/-- **Theorem B(a)** (`theorem:convergence-of-the-dirichlet-problem`): convergence of the Dirichlet problem for data harmonic near `closure U`. The certified statement is `SpherePackings.Frozen.theoremB_a`. -/
theorem SpherePackings.theorem_B_a :
  ∀ (d : ℕ) (G : TilingSequence d) (N : NearestVertexData G)
    (U : Set (Euc d)) (hC : Euc d → ℝ),
    1 ≤ d → IsDomain U → Bornology.IsBounded U →
    HasAmbientCollar U G.domain → N.ApproximationCondition → PaperRegularity G →
    HarmonicNearClosure hC U →
      DirichletApproximationTarget G U hC (fun n v => hC ((G.tiling n).pos v)) := by
  exact SpherePackings.Frozen.theoremB_a

/-- **Theorem B(b)** (`theorem:convergence-of-the-dirichlet-problem`): convergence of the Dirichlet problem on a Lipschitz domain for data continuous on `closure U`. The certified statement is `SpherePackings.Frozen.theoremB_b`. -/
theorem SpherePackings.theorem_B_b :
  ∀ (d : ℕ) (G : TilingSequence d) (N : NearestVertexData G)
    (U : Set (Euc d)) (hC : Euc d → ℝ),
    1 ≤ d → IsLipschitzDomain U → Bornology.IsBounded U →
    HasAmbientCollar U G.domain → N.ApproximationCondition → PaperRegularity G →
    IsHarmonicOn hC U → ContinuousOnClosure hC U →
      Nonempty (NearestClosureBoundaryChoices G U) ∧
      ∀ S : NearestClosureBoundaryChoices G U,
        (∀ n v, S.point n v ∈ frontier U) ∧
        (∀ᶠ n in Filter.atTop, ∀ v : (G.tiling n).boundaryVertices U,
          dist ((G.tiling n).pos v) (S.point n v) ≤ 2 * (G.tiling n).mesh.toReal) ∧
        DirichletApproximationTarget G U hC (S.boundaryData hC) := by
  exact SpherePackings.Frozen.theoremB_b

/-- **Proposition 1.1** (`prop:min-max-edge-length`): the Voronoi cells of Poisson processes of intensity `m μ` (in a neighbourhood `W` of `closure U`) lie between balls of radii `m^{-8/β⁻}` and `m^{-1/(3β⁺)}`. The certified statement is `SpherePackings.Frozen.prop11_cells`. -/
theorem SpherePackings.prop_1_1 {d : ℕ} (hd : 1 ≤ d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hUb : Bornology.IsBounded U) {μ : Measure (EuclideanSpace ℝ (Fin d))} {βp βm : ℝ}
    (hβp : 0 < βp) (hβm : 0 < βm) {W : Set (EuclideanSpace ℝ (Fin d))}
    (hW : IsOpen W) (hUW : closure U ⊆ W) (hμ : HolderMassBounds μ W βp βm)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Λ : ℕ → Ω → Set (EuclideanSpace ℝ (Fin d)))
    (hΛ : ∀ m : ℕ, IsPoissonPointProcess P (fun ω => Λ m ω ∩ W) ((m : ℝ≥0∞) • μ.restrict W)) :
    ∀ᵐ ω ∂P, ∀ᶠ m in atTop, ∀ s ∈ Λ m ω, (cell (Λ m ω) s ∩ U).Nonempty →
      ball s ((m : ℝ) ^ (-8 / βm)) ⊆ cell (Λ m ω) s ∧
        cell (Λ m ω) s ⊆ ball s ((m : ℝ) ^ (-1 / (3 * βp))) := by
  exact SpherePackings.Frozen.prop11_cells hd hUb hβp hβm hW hUW hμ P Λ hΛ

/-- **Proposition 1.1**, "in particular": Theorems A and B hold for Poisson–Voronoi tilings. The certified statement is `SpherePackings.Frozen.prop11_theoremAB`. -/
theorem SpherePackings.prop_1_1_theorems_A_B {d : ℕ} (hd : 1 ≤ d) {U : Set (Euc d)} (hU : IsDomain U)
    (hUb : Bornology.IsBounded U) {μ : Measure (Euc d)} {βp βm : ℝ} (hβp : 0 < βp)
    (hβm : 0 < βm) {W : Set (Euc d)} (hW : IsOpen W) (hUW : closure U ⊆ W)
    (hμ : HolderMassBounds μ W βp βm)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Λ : ℕ → Ω → Set (Euc d))
    (hΛ : ∀ m : ℕ, IsPoissonPointProcess P (fun ω => Λ m ω ∩ W) ((m : ℝ≥0∞) • μ.restrict W))
    (hlf : ∀ m ω (B : Set (Euc d)), Bornology.IsBounded B → (Λ m ω ∩ B).Finite) :
    ∀ᵐ ω ∂P, ∃ G : TilingSequence d, HasAmbientCollar U G.domain ∧
      (∀ᶠ m in atTop, IsVoronoiTilingOf (G.tiling m) (Λ m ω) G.domain) ∧
      -- Theorem B(a)
      (∀ hC : Euc d → ℝ, HarmonicNearClosure hC U →
        DirichletApproximationTarget G U hC (fun n v => hC ((G.tiling n).pos v))) ∧
      -- Theorem B(b)
      (IsLipschitzDomain U → ∀ hC : Euc d → ℝ, IsHarmonicOn hC U → ContinuousOnClosure hC U →
        Nonempty (NearestClosureBoundaryChoices G U) ∧
        ∀ S : NearestClosureBoundaryChoices G U,
          (∀ n v, S.point n v ∈ frontier U) ∧
          (∀ᶠ n in atTop, ∀ v : (G.tiling n).boundaryVertices U,
            dist ((G.tiling n).pos v) (S.point n v) ≤ 2 * (G.tiling n).mesh.toReal) ∧
          DirichletApproximationTarget G U hC (S.boundaryData hC)) ∧
      -- Theorem A
      (IsLipschitzDomain U → ∀ N : NearestVertexData G,
        ∃ ν : Measure (BrownianPath d),
          IsStandardBrownianLaw ν ∧
          (∀ z ∈ U,
            AEMeasurable (stoppedBrownianCurve U z) ν ∧
            (∀ᵐ ω ∂ν, continuousExitTime U z ω ≠ ∞) ∧
            IsProbabilityMeasure (stoppedBrownianLaw U z ν)) ∧
          ∃ walkLaw : ℕ → Euc d → Measure (CurveSpace d),
            (∀ᶠ n in atTop, ∀ z ∈ U,
              IsStoppedTilingWalkLaw (G.tiling n) U (N.vertex n z) (walkLaw n z)) ∧
            ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ z ∈ U,
              levyProkhorovEDist (walkLaw n z) (stoppedBrownianLaw U z ν) ≤
                ENNReal.ofReal η) := by
  exact SpherePackings.Frozen.prop11_theoremAB hd hU hUb hβp hβm hW hUW hμ P Λ hΛ hlf

/-- **Theorem 6.1** (`theorem:counter-example`): a bounded-degree sphere packing on which simple random walk does not converge to Brownian motion; in dimension three every sphere is covered. The certified statement is `SpherePackings.Frozen.theorem61_counterexample`. -/
theorem SpherePackings.theorem_6_1 (d : ℕ) (hd : 3 ≤ d) :
    ∃ P : SpherePacking d,
      (∀ i, P.radius i = 1 ∨ P.radius i = 1 / 2) ∧
      (∃ D : ℕ, ∀ i, {j | P.Tangent i j}.Finite ∧ {j | P.Tangent i j}.ncard ≤ D) ∧
      (d = 3 → ∀ i, P.Covered i) ∧
      ∃ i₀ : P.ι, P.center i₀ = 0 ∧
        (∃ walkLaw : ℕ → Measure (CurveSpace d), ∀ n : ℕ, 1 ≤ n →
          P.IsStoppedSRWLaw ((n : ℝ)⁻¹) (ball 0 1) i₀ (walkLaw n)) ∧
        ∀ μ : Measure (BrownianPath d), IsStandardBrownianLaw μ →
        ∀ walkLaw : ℕ → Measure (CurveSpace d),
          (∀ᶠ n : ℕ in atTop, P.IsStoppedSRWLaw ((n : ℝ)⁻¹) (ball 0 1) i₀ (walkLaw n)) →
          ¬ Tendsto (fun n => levyProkhorovEDist (walkLaw n) (stoppedBrownianLaw (ball 0 1) 0 μ))
            atTop (𝓝 0) := by
  exact SpherePackings.Frozen.theorem61_counterexample d hd

/-- **Theorem 4.1** (`theorem:general-clt`): under Assumption D, the stopped nearest-neighbour walks from the nearest vertices converge to stopped Brownian motion, modulo time parametrization, uniformly in the starting point. The certified statement is `SpherePackings.Frozen.theorem41`. -/
theorem SpherePackings.theorem_4_1 {d : ℕ} (hd : 1 ≤ d) (W : ℕ → NearestNeighbourWalk d)
    (near : ∀ n, Euc d → (W n).V) (hnear : ∀ n, (W n).IsNearestVertex (near n))
    {D : Set (Euc d)} {δ : ℝ} (hAD : AssumptionD W near D δ)
    {U : Set (Euc d)} (hU : IsLipschitzDomain U) (hUb : Bornology.IsBounded U) (hUD : U ⊆ D)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) :
    (∀ᶠ n in atTop, ∀ a : (W n).V, ∀ᵐ ω ∂MarkovChain.law (W n).kernel a,
      FiniteConductanceNetwork.exitTime ((W n).inner U) ω ≠ ⊤) ∧
    ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ z ∈ U,
      levyProkhorovEDist ((W n).stoppedWalkLaw U (near n z)) (stoppedBrownianLaw U z μ) ≤
        ENNReal.ofReal η := by
  exact SpherePackings.Frozen.theorem41 hd W near hnear hAD hU hUb hUD hμ
