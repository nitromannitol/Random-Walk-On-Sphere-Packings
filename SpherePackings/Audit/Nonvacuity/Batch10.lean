module

/- Nonvacuity examples written by the independent reviewer (Claude Haiku 5.5) of audit batch 10;
   see `AUDIT.md`. They show that the hypothesis bundles named below can hold together. -/
public import BouRabeeGwynne.TheoremBStatement
public import BouRabeeGwynne.EuclideanWienerLaw
public import BouRabeeGwynne.BrownianExitReference
public import SpherePackings.Support.Guards.LatticeTilings
public import SpherePackings.Support.Guards.LipschitzBall

@[expose] public section

-- The reviewer's examples, kept as written.
set_option linter.unusedVariables false
set_option linter.deprecated false

namespace SpherePackings.Audit.Nonvacuity10
open BouRabeeGwynne

open BouRabeeGwynne MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

/-- Hypothesis bundle of `TheoremBPartAStatement` (minus the universally quantified
`hC` and `U` that are instantiated here): the lattice tiling sequence, the ball
`U = B(0,1)`, and the zero function, which is harmonic on `ℝ^d`. -/
example {d : ℕ} (hd : 1 ≤ d) :
    ∃ (G : TilingSequence d) (N : NearestVertexData G) (U : Set (Euc d)) (hC : Euc d → ℝ),
      1 ≤ d ∧ IsDomain U ∧ Bornology.IsBounded U ∧ HasAmbientCollar U G.domain ∧
      N.ApproximationCondition ∧ PaperRegularity G ∧ HarmonicNearClosure hC U := by
  obtain ⟨G, hcol, ⟨N⟩, happ, hreg⟩ := SpherePackings.exists_lattice_tilingSequence hd
  refine ⟨G, N, ball (0 : Euc d) 1, fun _ => 0, hd,
    ⟨isOpen_ball, ⟨0, mem_ball_self one_pos⟩, (convex_ball 0 1).isPreconnected⟩,
    isBounded_ball, hcol, happ N, Or.inr (Or.inl hreg), Set.univ, isOpen_univ,
    subset_univ _, ?_⟩
  exact ⟨contDiff_const.contDiffOn, fun x _ => by simp⟩

/-- Hypothesis bundle of `TheoremBPartBStatement` (same instance, with a Lipschitz
domain and `IsHarmonicOn`/`ContinuousOnClosure` in place of `HarmonicNearClosure`). -/
example {d : ℕ} (hd : 1 ≤ d) :
    ∃ (G : TilingSequence d) (N : NearestVertexData G) (U : Set (Euc d)) (hC : Euc d → ℝ),
      1 ≤ d ∧ IsLipschitzDomain U ∧ Bornology.IsBounded U ∧ HasAmbientCollar U G.domain ∧
      N.ApproximationCondition ∧ PaperRegularity G ∧ IsHarmonicOn hC U ∧
      ContinuousOnClosure hC U := by
  obtain ⟨G, hcol, ⟨N⟩, happ, hreg⟩ := SpherePackings.exists_lattice_tilingSequence hd
  refine ⟨G, N, ball (0 : Euc d) 1, fun _ => 0, hd, SpherePackings.isLipschitzDomain_ball hd,
    isBounded_ball, hcol, happ N, Or.inr (Or.inl hreg), ?_, ?_⟩
  · exact ⟨contDiff_const.contDiffOn, fun x _ => by simp⟩
  · exact continuousOn_const

/-- The branch-(b) sampling class is nonempty for any nonempty `U`. -/
example {d : ℕ} (G : TilingSequence d) (U : Set (Euc d)) (hU : U.Nonempty) :
    Nonempty (NearestClosureBoundaryChoices G U) :=
  ⟨NearestClosureBoundaryChoices.ofNonempty G U hU⟩

/-- The actual Gaussian-start-free standard Brownian law on `ℝ²` (`euclideanWienerLaw 2`)
satisfies the hypotheses of the exit-reference lemma for `B(0,1)` and start `0`; the
conclusion is then an instance of the absolute continuity used in the Brownian comparison. -/
example :
    (stoppedBrownianLaw (ball (0 : Euc 2) 1) 0 (euclideanWienerLaw 2)).map CurveSpace.endPoint ≪
      brownianExitReferenceLaw (ball (0 : Euc 2) 1) (euclideanWienerLaw 2) :=
  standardBrownianLaw_exit_absolutelyContinuous_reference (by norm_num)
    (isStandardBrownianLaw_euclideanWienerLaw 2) isOpen_ball isBounded_ball
    (mem_ball_self one_pos)

end SpherePackings.Audit.Nonvacuity10
