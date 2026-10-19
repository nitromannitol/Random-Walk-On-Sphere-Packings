/- Nonvacuity examples written by the independent reviewer (Claude Haiku 5.5) of audit batch 00;
   see `AUDIT.md`. They show that the hypothesis bundles named below can hold together. -/
import BouRabeeGwynne.FiniteExit
import BouRabeeGwynne.FiniteDirichlet
import BouRabeeGwynne.EuclideanWienerLaw

-- The reviewer's examples, kept as written.
set_option linter.unusedVariables false
set_option linter.deprecated false

namespace SpherePackings.Audit.Nonvacuity00
open BouRabeeGwynne

open MeasureTheory ProbabilityTheory
open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork

/-- Two vertices joined by a unit-conductance edge. -/
def twoPointNetwork : FiniteConductanceNetwork (Fin 2) where
  a v w := if v = w then 0 else 1
  symm v w := by
    by_cases h : v = w
    · subst h; rfl
    · simp [h, Ne.symm h]
  nonneg v w := by
    by_cases h : v = w <;> simp [h]
  loop_zero v := by simp

/-- The interior `{0}` is boundary accessible: `0` reaches `1 ∉ {0}` in one edge. -/
lemma twoPoint_boundaryAccessible : twoPointNetwork.BoundaryAccessible {0} := by
  intro v hv
  have hv0 : v = 0 := hv
  subst hv0
  refine ⟨1, by simp, Relation.ReflTransGen.single ?_⟩
  simp [twoPointNetwork]

/-- The actual walk from `0` exits `{0}` almost surely. -/
example : ∀ᵐ ω ∂twoPointNetwork.trajectoryLaw ({0} : Set (Fin 2))
    (twoPointNetwork.totalConductance_pos_of_boundaryAccessible {0} twoPoint_boundaryAccessible) 0,
    exitTime ({0} : Set (Fin 2)) ω ≠ ⊤ :=
  twoPointNetwork.trajectoryLaw_ae_finiteExit_of_boundaryAccessible {0}
    twoPoint_boundaryAccessible 0

/-- The finite Dirichlet problem is uniquely solvable on this network. -/
example (g : Fin 2 → ℝ) : ∃! f : Fin 2 → ℝ, twoPointNetwork.SolvesDirichlet {0} g f :=
  twoPointNetwork.existsUnique_dirichlet {0} twoPoint_boundaryAccessible g

/-- The hypothesis of the strict-subharmonic criterion is satisfiable: `Δf(0) = 1 > 0`. -/
example : twoPointNetwork.BoundaryAccessible {0} :=
  twoPointNetwork.boundaryAccessible_of_strict_subharmonic {0}
    (fun v => if v = 1 then 1 else 0) (by
      intro v hv
      have hv0 : v = 0 := hv
      subst hv0
      simp [FiniteConductanceNetwork.laplacian, twoPointNetwork])

/-- Value of the library `energy` on `f = 1_{1}`: `½ (1 + 1) = 1`. The paper's
`𝒟(f,A)` sums over both orientations, which gives `2` here. -/
example : twoPointNetwork.energy (fun v => if v = 1 then 1 else 0) = 1 := by
  simp [FiniteConductanceNetwork.energy, Fin.sum_univ_two, twoPointNetwork]
  norm_num

/-- The standard Brownian law required in Theorem A's conclusion is satisfiable in every dimension. -/
example (d : ℕ) : ∃ μ : Measure (BrownianPath d), IsStandardBrownianLaw μ :=
  ⟨_, isStandardBrownianLaw_euclideanWienerLaw d⟩

end SpherePackings.Audit.Nonvacuity00
