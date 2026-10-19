# Audit batch 18
| Module | Verdict | Summary |
|---|---|---|
| SpherePackings.Support.Section4General.AssumptionD | NOTE | Matches Assumption D (paper 1438–1462); (4.2) quantifies over every discrete solution, so it is vacuous at an index with no solution (the paper presupposes existence). Not a defect of the theorems. |
| SpherePackings.Support.Section4General.BallExitInputs | OK | Quantifier order and the LP/exit-law statements match their docstrings; LP correctly compares sub-probability harmonic measures. |
| SpherePackings.Support.Section4General.CouplingPartitions | NOTE | Bound `(K+1) * ofReal b` matches its docstring; file-local `⊤` σ-algebra on `Option` is harmless on the finite codomain. |
| SpherePackings.Support.Section4General.ExitPartitions | OK | Backward stage construction and the uniform eventual comparison match the docstring; no junk values. |
| SpherePackings.Support.Section4General.NearestStarts | OK | (4.1) consequence and the nearby-start statement match their docstrings; `≤ δ₀` with `δ₀ > 0`. |
| SpherePackings.Support.Section4General.Prop42 | NOTE | Matches paper Prop 4.2 (1511–1516); the explicit hypothesis `closedBall c r ⊆ cthickening δ D` is the correct reading of the unit-ball claim, which the printed statement leaves implicit. |
| SpherePackings.Support.Section4General.StoppedWalkLaw | NOTE | Stopped walk law matches the paper; never-exit paths use a constant-curve convention, harmless given `eventually_ae_exit`; docstring says `U ⊆ D`, statement assumes `U ⊆ cthickening δ D`. |
| SpherePackings.Support.Section4General.Theorem41 | NOTE | Theorem 4.1 (1481–1488) matches the paper; the Brownian stopped law has a μ-null junk value (`toNNReal ⊤ = 0`) that cannot change the law for bounded `U`. |
| SpherePackings.Support.Guards.TilingWalk | NOTE | Conductance walk matches paper 233–236 on active vertices; the absorbing convention for inactive vertices is not proved unused for the witness; `walkWeight` junk `0` is unreachable. |
| SpherePackings.Support.Guards.AssumptionDLattice | NOTE | Witnesses are sequences of finite graphs on `ball 0 2`; the Theorem 4.1, Prop 4.2 and coupling bundles are nonvacuous (compiled examples below). |

Counts: OK 3, NOTE 7, ISSUE 0.

## SpherePackings.Support.Section4General.AssumptionD
- `AssumptionD` (line 32): matches Assumption D (paper lines 1438–1462). `B := closedBall x r ∩ cthickening δ D` is the paper's `B_r(x) ∩ B_δ(D)` (closed balls, paper's `B_r(U)` convention). `inner`/`boundary` in the clause match `V_n[·]`/`∂V_n[·]` (paper line 296). Clause (4.1) (lines 36–37) is the printed limit `sup_{z∈B}‖z^n−z‖ → 0`.
- `AssumptionD` clause (4.2) (lines 41–45): `∀ hD` solving the discrete Dirichlet problem, not "the" harmonic extension. The paper presupposes existence and uniqueness, so the Lean clause is vacuous at an index `n` where no discrete solution exists. This does not weaken the theorems:
  - the `h ≡ 0` instance is never vacuous (0 always solves it), and by linearity it forces every zero-data solution to vanish on `inner B` eventually, hence exit a.s. (this is the content of `eventually_survival_eq_zero`);
  - the proofs apply (4.2) only to solutions that exist (survival function, exit values, `exitValue_solvesDirichlet`).
  The docstring (lines 15–18) states this design choice.
- `IsDomain` (`BouRabeeGwynne/PaperObjects.lean:17`) is open ∧ nonempty ∧ preconnected, matching "domain".
- `near` is an arbitrary choice here; nearest-ness (`IsNearestVertex`, `SpherePackings/General/NearestNeighbourWalk.lean:98`) is imposed separately by the theorems. Combined, this matches the paper's `z^n`.
- Quantifier precedence checked: `∧`/`→`/`∀` parse as intended.

## SpherePackings.Support.Section4General.BallExitInputs
- `eventually_ball_exit_nearby_levyProkhorov_error` (line 26): `∀ε ∃δ' ∀ᶠn ∀v∈K ∀y∈K` — `δ'` is independent of `n`, so the uniformity is as stated. `levyProkhorovEDist` is Mathlib's two-sided LP over all measurable sets, so it controls total-mass differences; that is what is needed for sub-probability harmonic measures.
- `NearestNeighbourWalk.harmonicMeasure_univ_of_survival` (line 68): correct (mass 1 once survival is 0).
- `eventually_survival_eq_zero` (line 85): the clause uses `boundary (closedBall c r)`, which equals the boundary of `ball c r` because the two inner sets coincide (proof lines 97–100). The docstring's "every ball of `B_δ(D)`" corresponds to the hypothesis `closedBall c r ⊆ cthickening δ D`. Matches.
- `eventually_harmonicMeasure_isProbability` (line 111): correct; the sub-probability measure becomes a probability measure eventually.
- `eventually_ball_exit_nearby_cell_error` (line 125): `toReal` is applied to finite measures only (no `⊤` junk); the tolerance `ε` is uniform as stated.

## SpherePackings.Support.Section4General.CouplingPartitions
- local instance (line 22) `MeasurableSpace (Option X) := ⊤`: file-local discrete σ-algebra. On the finite codomain `Option ↥centers` this makes `hs : Measurable (select i)` the genuine fibre-measurability condition, so it is not vacuous. Harmless.
- `exists_eventual_walkBrownian_coupling_partitions_general` (line 28): the order is `∃ m E hE hdE select hs δ₀` before `∀ᶠ n ∀ initial v₀ z`, so the partitions are independent of `n`. The bound `(K+1) * ofReal b` on `∃ i ≤ K, (bad pair)` matches the docstring line 13 ("(K + 1) b"). The cell-diameter bound `a` (line 46) and the good-pair tolerance `a` (via `goodExcursionPair`) are the same parameter, consistently.
- The hypothesis bundle is jointly satisfiable at the lattice witness (Nonvacuity Example 2).

## SpherePackings.Support.Section4General.ExitPartitions
- `ExitPartitionStage` (line 18, `private`): fields are as intended: cells measurable, bounded, covering `Q`, diameter `≤ min a (r/4)`; `frontier_null` (Brownian exit law from any `z ∈ ball` charges no cell frontier); `modulus > 0`; `comparison` with tolerance `b / (card + 1)` (positive denominator, no junk).
- `exists_exitPartitionStage` (line 40): correct.
- `exists_backward_ball_exit_partitions` (line 98): the backward condition `∀ i : Fin L, … E i.castSucc … ≤ δ i.succ` has the intended direction (earlier cells fit inside the next stage's tolerance, docstring lines 94–97). The eventual clause `∀ᶠ n ∀ j i v …` is uniform over balls and stages, and `m`, `E`, `δ` are chosen before `n`.

## SpherePackings.Support.Section4General.NearestStarts
- `eventually_near_dist_le` (line 20): (4.1) uniform on bounded `S ⊆ cthickening δ D`; correct.
- `eventually_near_coupling_starts` (line 33): `∀ᶠ n ∀ z ∈ U ∃ j ∈ centers` with `near n z ∈ closedBall j (r/2)`, `z ∈ closedBall j (r/2)`, `dist ≤ δ₀`; quantifiers and `≤` match the docstring.

## SpherePackings.Support.Section4General.Prop42
- `patch` (line 29): `O.piecewise p f` equals `p` on `O` and `f` off `O` (lemmas at lines 32–40); matches its docstring.
- `mem_cthickening_sphere_of_not_mem_ball` (line 57): correct geometric lemma.
- `prop42_test_core` (line 84), `prop42_test` (line 228), `prop42_test_vertex` (line 242): quantifiers are right (`η'` depends on `ε`, `f`, not `n`); `hM` bounds `f`, so all integrals are of integrable functions against finite measures (no `∫` junk).
- `prop42_general` (line 260): matches paper Prop 4.2 (1511–1516), generalized from the unit ball to any ball and stated with `levyProkhorovEDist` (equal to Prokhorov on probability measures). The Lean statement adds `hB : closedBall c r ⊆ cthickening δ D`, which the printed statement leaves implicit. Assumption D as printed controls only `B_r(x) ∩ B_δ(D)`, so the unit-ball claim needs `B̄_1 ⊆ B_δ(D)`; the Lean hypothesis is the correct reading. Nonvacuous (Example 3).
- `prop42_vertex` (line 296): stronger form, uniform over all vertices `a` of the ball and comparing with the Brownian law from `a` itself. Correct.

## SpherePackings.Support.Section4General.StoppedWalkLaw
- `NearestNeighbourWalk.stoppedWalkLaw` (line 26): the law of the polygonal interpolation stopped at the first exit of `V[U]`, matching the paper's `Y^{z,n}|_{[0,J]}` (lines 1481–1488). It is a genuine probability measure (`stoppedWalkLaw_isProbabilityMeasure`, line 29), so the `Measure.map` default `0` is excluded.
- Convention: on never-exit paths `stoppedPolygonalCurve` totalizes to the constant curve (`untopD 0`, `BouRabeeGwynne/StoppedCurveLaws.lean:60`). Harmless: `eventually_ae_exit` (line 38) gives a.s. exit eventually, and `theorem41_general` records that conjunct.
- `eventually_ae_exit` (line 38): docstring says "U ⊆ D" but the hypothesis is `U ⊆ cthickening δ D`. The statement is the more general one; docstring drift only.

## SpherePackings.Support.Section4General.Theorem41
- `theorem41_general` (line 35) and `theorem41` (line 144): match Theorem 4.1 (1481–1488). `U ⊆ D` bounded Lipschitz (`IsLipschitzDomain = IsDomain ∧ HasLipschitzBoundary`, `BouRabeeGwynne/LipschitzDomain.lean:35`, boundedness separate), walk started at `near n z`, stopped at the first exit of `V_n[U]`, uniform over `z ∈ U`. The LP metric on `CurveSpace d` is the infimum over time changes of the sup error (`BouRabeeGwynne/CurveSpace.lean`, `edist_mk`), i.e. the paper's metric. `theorem41_general` drops connectedness, so it is strictly more general. The a.s.-exit conjunct is extra and correct.
- Junk value on the Brownian side: `stoppedBrownianRepresentative` (`BouRabeeGwynne/StoppedCurveLaws.lean:74–77`) uses `(continuousExitTime U z ω).toNNReal`, which is `0` when the exit time is `⊤` (`ENNReal.toNNReal ⊤ = 0`); the stopped curve is then constant `z`. This happens only on a μ-null event when `U` is bounded (Brownian paths leave bounded open sets a.s., `d ≥ 1`), so the law is unaffected. `theorem41` requires `hUb`. NOTE, not ISSUE.
- local `⊤` σ-algebra on `Option` (line 30): same as CouplingPartitions; harmless.

## SpherePackings.Support.Guards.TilingWalk
- `tilingPoints` (line 25) = `range T.pos`; `tilingEquiv` (line 28) is the injectivity bijection. Correct.
- `walkWeight` (line 34): `0` when the neighbour set is infinite. This junk is unreachable in the walk: `stepMeasure` checks `WalkActive` (which requires `Finite`) before using it. For finite-degree vertices with total weight `≤ 0`, all conductances are `0`, so the walk is absorbing and the weight is never divided by. Harmless.
- `WalkActive` (line 39), `stepMeasure` (line 42): for active vertices `p(a,w) = cond(a,w)/cond(a)`, matching paper lines 233–236. For inactive vertices the walk is absorbing (Dirac); the docstring says this "never occurs in the applications". That is not proved in the file. It is a modelling convention, so the satisfiability claim for `conductanceWalk` as defined is unaffected, but the "conductance walks satisfy Assumption D" phrasing in `AssumptionDLattice` relies on it.
- `conductanceWalk` (line 103): edges are `T.adj` (codimension-one facets, `IsCodimOneFacet` with `finrank = d-1`), plus self-loops at absorbing vertices. The self-loops are irrelevant to `boundary`.
- `discreteLaplacian_eq_zero_of_isHarmonicAt` (line 122): the Lean `discreteLaplacian` is `Σ cond(v,w)(f w − f v)`, the paper's geometric Laplacian (line 289). The Section 4 generator (line 1426) is this divided by `cond(v)`, which is positive for active vertices, so the zero sets (Dirichlet notions) agree. Matches.
- `conductanceWalk_inner` (line 175), `conductanceWalk_boundary` (line 180): match `V[S]`, `∂V[S]` (paper line 296).

## SpherePackings.Support.Guards.AssumptionDLattice
- `exists_walks_assumptionD` (line 49): statement is the satisfiability of Assumption D for the unit ball with nearest vertices. Correct.
- Scope of the witness: every `G.tiling n` is finite (`∀ n, Finite (G.tiling n).V` from `exists_lattice_tilingSequence_finite`, `SpherePackings/Support/Guards/LatticeTilings.lean:45–48`), on the bounded domain `ball 0 2` (`LatticeTilings.lean:52, 70`). So the witness exercises finite graphs only, not the unbounded tiling graphs the paper's "possibly infinite domain" allows. Not a defect of the definitions.
- `theorem41_hypotheses_satisfiable` (line 130): the bundle (walks, `near`, `δ`, `μ`, nearest, Assumption D, Lipschitz, bounded, standard Brownian law) is jointly satisfiable. Nonvacuous (Example 1 instantiates `theorem41` on it).
- Uses `conductanceWalk`, so inherits the absorbing-convention note above.

## Nonvacuity examples
Scratch file: `Nonvacuity.lean`. Compiled from the repository root with:

```
lake env lean Nonvacuity.lean
```

Output (exit 0, no errors, no `sorry`):

```
Nonvacuity.lean:34:38: warning: Variable name `E` is not explicitly referenced.
```

The warning is cosmetic (an unused `E` binder in the statement of Example 2).

```lean
import SpherePackings.Support.Guards.AssumptionDLattice
import SpherePackings.Support.Section4General.CouplingPartitions
import SpherePackings.Support.Section4General.Prop42
import SpherePackings.Support.Section4General.Theorem41

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
```

What the examples show:
- **Example 1** (Theorem 4.1 bundle): the walks, nearest vertices, Assumption D for `D = ball 0 1`, `IsLipschitzDomain`, boundedness and the standard Brownian law are jointly satisfiable, and `theorem41` yields its full conclusion (a.s. exit and uniform LP convergence of the stopped laws) for that witness.
- **Example 2** (coupling-partition bundle): the hypotheses of `exists_eventual_walkBrownian_coupling_partitions_general` (compact `Q`, cover `C ⊆ Q` by `ball 0 (1/4)`, balls inside `cthickening δ (ball 0 1)`, closures inside `Q`, quarter-cover by centers) are discharged by proof for the witness, so the bundle is not contradictory.
- **Example 3** (Proposition 4.2 bundle): `prop42_general` applies to the witness for `ball 0 1`, with the explicit inclusion `closedBall 0 1 ⊆ cthickening δ (ball 0 1)` proved.
- Pre-existing results cited, not re-proved: `exists_walks_assumptionD` (Assumption D satisfiable), `theorem41_hypotheses_satisfiable`, `isLipschitzDomain_ball`, `isStandardBrownianLaw_euclideanWienerLaw`.
