/- Nonvacuity examples written by the independent reviewer (Claude Haiku 5.5) of audit batch 12;
   see `AUDIT.md`. They show that the hypothesis bundles named below can hold together. -/
import BouRabeeGwynne.TheoremAProved
import BouRabeeGwynne.UniformStoppedWalkConvergence
import BouRabeeGwynne.StandardBrownianProbabilityMeasure
import SpherePackings.Support.Guards.LatticeTilings
import SpherePackings.Support.Guards.LipschitzBall

-- The reviewer's examples, kept as written.
set_option linter.unusedVariables false
set_option linter.deprecated false

/-! Scratch nonvacuity checks for batch 12 (audit only; not part of the repository). -/

open MeasureTheory Metric Filter Set
open BouRabeeGwynne

namespace SpherePackings.Audit.Nonvacuity12
/-- The non-domain premises of `TheoremAStatement` (ambient collar, (1.3), and (I)–(III))
are jointly satisfiable with `U = ball 0 1` in every dimension `d ≥ 1`. -/
theorem theoremA_premises_satisfiable (d : ℕ) (hd : 1 ≤ d) :
    ∃ (G : TilingSequence d) (N : NearestVertexData G),
      HasAmbientCollar (ball (0 : Euc d) 1) G.domain ∧ N.ApproximationCondition ∧
        PaperRegularity G := by
  obtain ⟨G, hcol, ⟨N⟩, happ, hRII⟩ := SpherePackings.exists_lattice_tilingSequence hd
  exact ⟨G, N, hcol, happ N, Or.inr (Or.inl hRII)⟩

/-- `TheoremAStatement` applied to that instance (with `U = ball 0 1`, which is a Lipschitz
domain and bounded) yields a standard Brownian law `μ`, eventually defined stopped walk laws,
and Lévy–Prokhorov convergence uniformly over `z ∈ U`. -/
theorem theoremA_instance (d : ℕ) (hd : 1 ≤ d) :
    ∃ (G : TilingSequence d) (N : NearestVertexData G) (μ : Measure (BrownianPath d)),
      IsStandardBrownianLaw μ ∧
      ∃ walkLaw : ℕ → Euc d → Measure (CurveSpace d),
        (∀ᶠ n in Filter.atTop, ∀ z ∈ ball (0 : Euc d) 1,
          IsStoppedTilingWalkLaw (G.tiling n) (ball (0 : Euc d) 1) (N.vertex n z)
            (walkLaw n z)) ∧
        ∀ η : ℝ, 0 < η → ∀ᶠ n in Filter.atTop, ∀ z ∈ ball (0 : Euc d) 1,
          levyProkhorovEDist (walkLaw n z) (stoppedBrownianLaw (ball (0 : Euc d) 1) z μ) ≤
            ENNReal.ofReal η := by
  obtain ⟨G, N, hcol, happ, hreg⟩ := theoremA_premises_satisfiable d hd
  obtain ⟨μ, hμ, -, walkLaw, hwalk, hLP⟩ :=
    theoremA_proved d hd G N (ball (0 : Euc d) 1) (SpherePackings.isLipschitzDomain_ball hd)
      isBounded_ball hcol happ hreg
  exact ⟨G, N, μ, hμ, walkLaw, hwalk, hLP⟩

/-- The ambient collar `closure (ball 0 1) ⊆ interior (ball 0 2)` in every dimension. -/
theorem ambient_collar_ball (d : ℕ) :
    HasAmbientCollar (ball (0 : Euc d) 1) (ball (0 : Euc d) 2) := by
  unfold HasAmbientCollar
  rw [isOpen_ball.interior_eq]
  exact closure_ball_subset_closedBall.trans (closedBall_subset_ball one_lt_two)

/-- The coupling setup (the central quantitative statement behind Theorem A) is applicable to
the unit ball with a standard Brownian law; its conclusion gives a positive neighborhood scale. -/
theorem coupling_setup_instance (d : ℕ) (hd : 1 ≤ d) :
    ∃ δ : ℝ, 0 < δ := by
  obtain ⟨μp, hμ⟩ := exists_standardBrownianProbabilityMeasure d
  obtain ⟨δ, r, W, Q, centers, K, hδ, -⟩ :=
    exists_theoremA_coupling_setup hd isOpen_ball isBounded_ball
      (SpherePackings.isLipschitzDomain_ball hd).2 (ambient_collar_ball d)
      (μ := (μp : Measure (BrownianPath d))) hμ one_pos
  exact ⟨δ, hδ⟩

end SpherePackings.Audit.Nonvacuity12
