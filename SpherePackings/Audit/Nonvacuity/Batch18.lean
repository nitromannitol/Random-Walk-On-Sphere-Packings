module

/- Nonvacuity examples written by the independent reviewer (Claude Haiku 5.5) of audit batch 18;
   see `AUDIT.md`. They show that the hypothesis bundles named below can hold together. -/
public import SpherePackings.Support.Guards.AssumptionDLattice
public import SpherePackings.Support.Section4General.CouplingPartitions
public import SpherePackings.Support.Section4General.Prop42
public import SpherePackings.Support.Section4General.Theorem41

@[expose] public section

-- The reviewer's examples, kept as written.
set_option linter.unusedVariables false
set_option linter.deprecated false

/-! Scratch nonvacuity checks for audit batch 18 (not part of the repository).  The lattice witness
`theorem41_hypotheses_satisfiable` supplies the walks, `near`, `δ`, `μ`; the remaining hypotheses are
discharged by proof. -/

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped unitInterval NNReal ENNReal
open BouRabeeGwynne

namespace SpherePackings

variable {d : ℕ}

/-- Theorem 4.1 (`theorem41`) instantiated at the lattice witness with `U = D = ball 0 1`. -/
example (hd : 1 ≤ d) :
    ∃ (W : ℕ → NearestNeighbourWalk d) (near : ∀ n, Euc d → (W n).V) (δ : ℝ)
      (μ : Measure (BrownianPath d)),
      (∀ n, (W n).IsNearestVertex (near n)) ∧ AssumptionD W near (ball (0 : Euc d) 1) δ ∧
      (∀ᶠ n in atTop, ∀ a : (W n).V, ∀ᵐ ω ∂MarkovChain.law (W n).kernel a,
        FiniteConductanceNetwork.exitTime ((W n).inner (ball (0 : Euc d) 1)) ω ≠ ⊤) ∧
      ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ z ∈ ball (0 : Euc d) 1,
        levyProkhorovEDist ((W n).stoppedWalkLaw (ball (0 : Euc d) 1) (near n z))
          (stoppedBrownianLaw (ball (0 : Euc d) 1) z μ) ≤ ENNReal.ofReal η := by
  obtain ⟨W, near, δ, μ, hnear, hAD, hU, hUb, hμ⟩ := theorem41_hypotheses_satisfiable hd
  exact ⟨W, near, δ, μ, hnear, hAD, theorem41 hd W near hnear hAD hU hUb subset_rfl hμ⟩

/-- The coupling-partition bundle `exists_eventual_walkBrownian_coupling_partitions_general` is
satisfiable at the lattice witness with one center `0`, `r = 1`, `C = ball 0 (1/4)`, `Q = closedBall 0 1`,
`a = b = 1`, `K = 1`. -/
example (hd : 1 ≤ d) : ∃ (m : ℕ → ℕ) (E : ∀ i, Fin (m i) → Set (Euc d)) (δ₀ : ℝ), 0 < δ₀ := by
  obtain ⟨W, near, δ, μ, hnear, hAD, -, -, hμ⟩ := theorem41_hypotheses_satisfiable hd
  have hcl : closedBall (0 : Euc d) 1 ⊆ cthickening δ (ball (0 : Euc d) 1) := by
    rw [← closure_ball (0 : Euc d) one_ne_zero]
    exact closure_subset_cthickening δ _
  have hCQ : ball (0 : Euc d) (1 / 4) ⊆ closedBall (0 : Euc d) 1 :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num))
  have hQ : IsCompact (closedBall (0 : Euc d) 1) := isCompact_closedBall _ _
  have hballD : ∀ j : ({0} : Finset (Euc d)),
      closedBall j.val 1 ⊆ cthickening δ (ball (0 : Euc d) 1) := by
    rintro ⟨j, hj⟩
    obtain rfl := Finset.mem_singleton.mp hj
    exact hcl
  have hballQ : ∀ j : ({0} : Finset (Euc d)), closure (ball j.val 1) ⊆ closedBall (0 : Euc d) 1 := by
    rintro ⟨j, hj⟩
    obtain rfl := Finset.mem_singleton.mp hj
    exact (closure_ball _ one_ne_zero).subset
  have hquarter : ∀ x ∈ ball (0 : Euc d) (1 / 4),
      ∃ c ∈ ({0} : Finset (Euc d)), x ∈ ball c (1 / 4) :=
    fun x hx => ⟨0, Finset.mem_singleton_self _, hx⟩
  obtain ⟨m, E, -, -, -, -, δ₀, hδ₀, -⟩ :=
    exists_eventual_walkBrownian_coupling_partitions_general hd W near hnear hAD hμ
      ({0} : Finset (Euc d)) (by norm_num : (0 : ℝ) < 1) hQ hCQ hballD hballQ hquarter
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1) 1
  exact ⟨m, E, δ₀, hδ₀⟩

/-- Proposition 4.2 (`prop42_general`) is applicable at the lattice witness for the ball `ball 0 1`. -/
example (hd : 1 ≤ d) :
    ∃ (W : ℕ → NearestNeighbourWalk d) (near : ∀ n, Euc d → (W n).V) (δ : ℝ)
      (μ : Measure (BrownianPath d)) (hμ : IsStandardBrownianLaw μ),
      AssumptionD W near (ball (0 : Euc d) 1) δ ∧
      ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ x ∈ ball (0 : Euc d) 1,
        levyProkhorovEDist ((W n).harmonicMeasure (ball (0 : Euc d) 1) (near n x))
          (brownianSpatialHarmonicMeasure (ball (0 : Euc d) 1) isOpen_ball μ hμ x :
            Measure (Euc d)) ≤ ENNReal.ofReal η := by
  obtain ⟨W, near, δ, μ, -, hAD, -, -, hμ⟩ := theorem41_hypotheses_satisfiable hd
  have hcl : closedBall (0 : Euc d) 1 ⊆ cthickening δ (ball (0 : Euc d) 1) := by
    rw [← closure_ball (0 : Euc d) one_ne_zero]
    exact closure_subset_cthickening δ _
  exact ⟨W, near, δ, μ, hμ, hAD, prop42_general hd W near hAD (c := 0) (r := 1) one_pos hcl hμ⟩

end SpherePackings
