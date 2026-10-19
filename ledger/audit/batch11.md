# Audit batch 11
| Module | Verdict | Summary |
|---|---|---|
| BouRabeeGwynne.BrownianContinuousLaw | NOTE | Continuous modification is `Exists.choose`; only `choose_spec` is used, so the choice is harmless. |
| BouRabeeGwynne.EuclideanWienerLaw | OK | `euclideanWienerLaw d` is the image of the product of d real Wiener laws; `isStandardBrownianLaw_euclideanWienerLaw` is the Brownian nonvacuity witness. |
| BouRabeeGwynne.PolynomialDirichlet | OK | Ball factor evaluates to r^2 - ‖x-c‖^2, Dirichlet operator is Δ(A·q); the standard-law premise of injectivity is witnessed. |
| BouRabeeGwynne.HarmonicPolynomialApproximation | OK | Continuous sphere data approximated by globally harmonic polynomials, plus a closed δ-collar; statements match docstrings. |
| BouRabeeGwynne.Section4BallExitConvergence | NOTE | Main ball-exit estimate is correct and jointly satisfiable; `hreg` carries the `toReal` junk of `RegularityII` (PaperObjects.lean:207-213), harmless here because `ApproximationCondition` forces finite mesh. |
| BouRabeeGwynne.Section4BrownianBallKernel | OK | Weak continuity of z ↦ Brownian ball-exit law on the ball, from harmonic approximants. |
| BouRabeeGwynne.Section4UniformExitTopology | OK | Uniform bounded-test convergence plus a continuous kernel on a compact space gives uniform Lévy–Prokhorov convergence; matches docstring. |
| BouRabeeGwynne.Section4BallExitLevyProkhorov | NOTE | LP convergence is stated only for starting points in a compact K ⊆ ball (as the docstring says), not for the full-ball claim of Prop 4.2; `hreg` junk as above. |
| BouRabeeGwynne.Section4UniformExitCells | OK | Mass comparison on common null-frontier cells; the nearby-start modulus is chosen before the eventual index. |
| BouRabeeGwynne.Section4BallExitCouplingInputs | NOTE | Quantifier order is correct (δ before the eventual index); compact-K restriction and `hreg` junk as above. |
| BouRabeeGwynne.BackwardExitPartitions | NOTE | Backward choice of cells and moduli, one eventual index for all stages and balls, is correct; `hreg` junk as above. |
| BouRabeeGwynne.AmbientExitPartitions | NOTE | Transfer to one ambient network is correct; `hreg` junk as above. |
| BouRabeeGwynne.StoppedTilingWalkLaw | OK | Existence of the stopped tiling walk law, and Dirac at the constant curve when the start is outside U; matches `IsStoppedTilingWalkLaw`. |
| BouRabeeGwynne.AmbientStoppedWalkLaw | OK | Stopped-curve law equals the ambient walk law; curve stops at the U-set, which is the intended convention. |
| BouRabeeGwynne.BoundarySurvivalScales | OK | Scalar selection with concrete satisfying instance (compiled). |
| BouRabeeGwynne.BrownianNestedClock | OK | Nested clock equals the first exits of the nested sets, including infinite exit times; range inclusions correct. |
| BouRabeeGwynne.SkeletonSurvival | OK | Multiplicative survival bound on good histories; `survivalUpTo` is the intended event. |
| BouRabeeGwynne.BrownianNestedSurvival | NOTE | `uniform_brownian_nested_survival` also quantifies over δ ≤ 0, where `cthickening δ U` is `closure U`; these instances are implied by δ > 0 and the bound stays true. |
| BouRabeeGwynne.BrownianExitRangeComparison | OK | Exit-time comparisons and closed-collar inclusion; matches docstring. |
| BouRabeeGwynne.BrownianNestedConfinement | OK | Nested survival controls the whole outer-stopped path; `N - 1` is guarded by `0 < N`. |
| BouRabeeGwynne.BrownianStoppingEvent | OK | Strong-Markov transfer bound; finiteness is a.s., so the ⊤ totalization is null. |
| BouRabeeGwynne.BrownianExitInterval | OK | Both endpoints of [τ, next exit] lie in the excursion range; 2η bound correct. |
| BouRabeeGwynne.BrownianStoppingOscillation | OK | η-confinement of a fresh path gives 2η-oscillation on [τ, next exit] except on probability ≤ ε. |
| BouRabeeGwynne.BrownianBoundaryOscillation | NOTE | `innerDomain` is junk (`infDist x ∅ = 0`) when Uᶜ = ∅; excluded by the bounded-U hypothesis; ⊤ exit times are μ-null. |
| BouRabeeGwynne.BrownianSkeletonOscillation | OK | Transfer of the oscillation bound to the skeleton representation; bound ε + r is correct. |
| BouRabeeGwynne.BrownianFiniteProbability | OK | Quantifier order matches docstring: boundary cutoff a, then (ε, δ, W, r), then stage count K, then G, z, j₀, selector, P. |
| BouRabeeGwynne.BrownianUniformFiniteProbability | OK | Same statement with the label type J quantified after a; a stronger form. |

Verdict counts: OK 19, NOTE 8, ISSUE 0.

## BouRabeeGwynne.BrownianContinuousLaw
- `isKolmogorovProcess_brownianProjectiveLaw` (line 21): fourth moment `∫ edist^4 = 3·edist^2` for the projective Gaussian law; matches the Kolmogorov input.
- `exists_continuous_brownianProjective_modification` (line 48): a measurable, a.e.-equal, everywhere-continuous modification exists; matches.
- `continuousBrownianProcess` (line 62): `Exists.choose` of line 48. Any witness with the proven spec would do, and downstream uses only `choose_spec`. NOTE: harmless.
- `realWienerLaw` (line 85, instance line 88): pushforward of the projective law under the continuous path map, a probability measure. Matches the real Wiener law.
- `isBrownianReal_realWienerLaw` (line 92): Mathlib `IsBrownianReal` (Gaussian f.d.d., a.s. continuous paths); matches.

## BouRabeeGwynne.EuclideanWienerLaw
- `assembleBrownianPath` (line 20): ω ↦ (t ↦ (ω_i t)_i) into `WithLp 2`; continuous; matches.
- `euclideanWienerLaw` (line 39, instance line 42): image of `Measure.pi` of d real Wiener laws; probability measure; matches the standard d-dimensional Wiener measure.
- `isStandardBrownianLaw_euclideanWienerLaw` (line 83): establishes `IsStandardBrownianLaw` (StoppedCurveLaws.lean:38-41: probability, coordinatewise `IsBrownianReal`, independence). Witness for every Brownian premise in the batch.

## BouRabeeGwynne.PolynomialDirichlet
- `polynomialBallFactor` (line 21; evaluation lemma line 35): evaluates to `r^2 - ‖x-c‖^2`; matches.
- `ballDirichletOperator` (line 40): `q ↦ Δ(A·q)` on degree ≤ m with A the ball factor; matches the finite-dimensional Dirichlet operator.
- `ballDirichletOperator_injective` (line 45): the `IsStandardBrownianLaw μ` premise is witness-only and satisfied by `euclideanWienerLaw`. Not vacuous.
- `exists_harmonic_polynomial_on_sphere_of_brownianLaw` (line 89) and `exists_harmonic_polynomial_on_sphere` (line 120): every polynomial sphere datum has a globally harmonic polynomial extension. Matches the classical statement; line 120 removes the premise.

## BouRabeeGwynne.HarmonicPolynomialApproximation
- `exists_harmonic_polynomial_near_sphere_data` (line 23): uniform approximation of continuous sphere data by globally harmonic polynomials; matches docstring.
- `exists_harmonic_polynomial_near_sphere_collar` (line 38): `∃ δ > 0` with `cthickening δ (sphere c r)` in the approximation set; matches.

## BouRabeeGwynne.Section4BallExitConvergence
- `eventually_ball_exit_test_error` (line 18): for continuous f and ε > 0, eventually in n the discrete exit expectations from every interior vertex are ε-close to the Brownian ball-exit expectations at `pos v`. Matches docstring; ε is quantified before n.
  - NOTE: `hreg : PaperRegularity G` includes `RegularityII` (PaperObjects.lean:207-213), which uses `mesh.toReal`. Since `ENNReal.toReal ⊤ = 0`, a sequence with infinite mesh satisfies the first conjunct trivially. Harmless here: `happrox` (`ApproximationCondition`, Approximation.lean:40, an ℝ≥0∞ limit) forces the mesh finite eventually, and the conclusion is eventual.

## BouRabeeGwynne.Section4BrownianBallKernel
- `continuous_brownianBallHarmonicMeasure` (line 17): z ↦ Brownian exit law is continuous on the ball for the weak topology; matches.

## BouRabeeGwynne.Section4UniformExitTopology
- `uniform_levyProkhorovDist_of_uniform_test_error` (line 19): compactness of the parameter space plus continuity of the limit kernel turns uniform bounded-test convergence into uniform LP convergence. The subsequence argument is valid; matches docstring.

## BouRabeeGwynne.Section4BallExitLevyProkhorov
- `HasFiniteAccessibleRegion` (line 19): `∃` finite closed-vertex set with `BoundaryAccessible`; matches.
- `spatialExitProbability` (line 26) and `spatialExitProbability_eq` (line 34): the finite presentation comes from `hg.choose`, which is a Prop-level finiteness proof, so the choice is harmless; the identity holds by `rfl`.
- `eventually_ball_exit_levyProkhorov_error` (line 52): LP convergence is uniform only over starting points in a compact `K ⊆ ball`. Matches its docstring, but it is weaker than the paper's `sup_{z∈U}` claim (paper/rw-spheres.tex:1487) and than the Prop 4.2 claim "uniformly over the open ball" recorded in CORRESPONDENCE.md:147. This is an intermediate lemma, and the full-ball claim is not established here.
  - NOTE: same `hreg` junk as Section4BallExitConvergence.

## BouRabeeGwynne.Section4UniformExitCells
- `continuous_probability_cell_mass` (line 17): `z ↦ ν_z(S)` is continuous when every `ν_z(∂S) = 0`; Portmanteau; `toReal` is safe on probability masses.
- `uniform_cell_mass_error_of_uniform_levyProkhorov_error` (line 29): uniform mass error on a fixed null-frontier S. Correct; the null-frontier hypothesis is necessary, as the docstring says.
- `uniform_nearby_cell_mass_error_of_uniform_levyProkhorov_error` (line 92): `∀ε ∃δ ∀ᶠ n`: the starting-point modulus precedes the eventual index; correct.

## BouRabeeGwynne.Section4BallExitCouplingInputs
- `eventually_ball_exit_nearby_levyProkhorov_error` (line 17): `∀ε ∃δ>0 ∀ᶠ n ∃hg ∀v … ∀y∈K, dist ≤ δ → LP ≤ ε`; quantifier order correct.
  - NOTE: compact-K restriction as above; `hreg` junk as above.
- `eventually_ball_exit_nearby_cell_error` (line 68): same order; the null-frontier hypothesis is assumed only for z ∈ K, which matches the conclusion (y ∈ K).

## BouRabeeGwynne.BackwardExitPartitions
- `ExitPartitionStage` (line 16, private): fields encode a cell partition with diameter ≤ min(a, r/4), null frontier for the stopped law, and the comparison (lines 31-42). Correct.
- `exists_backward_ball_exit_partitions` (line 109): stage count L is fixed first, cells are chosen backwards with `diam(E_i) ≤ δ_{i+1}`, and one eventual index serves all stages and balls. Matches docstring.
  - NOTE: `hreg` junk as above.

## BouRabeeGwynne.AmbientExitPartitions
- `spatialExitProbability_eq_ambient_discreteHarmonicMeasure` (line 18): exit law from U in the closed region equals the ambient harmonic measure of `{pos ∈ U}`, pushed to Euclidean space. Matches the convention at paper/rw-spheres.tex:1507-1508.
- `exists_backward_ambient_exit_partitions` (line 69): the ball-level construction transferred to one ambient network W. Its hypotheses should be satisfied by the lattice witness with `W = ball 0 1` and balls of radius ≤ 1/2 (reasoned from the lattice statement, not compiled).
  - NOTE: `hreg` junk as above.

## BouRabeeGwynne.StoppedTilingWalkLaw
- `exists_isStoppedTilingWalkLaw` (line 63): given structural accessibility, a stopped curve law exists; the existence used by Theorem A.
- `isStoppedTilingWalkLaw_eq_dirac_of_not_mem` (line 99): start outside U gives the Dirac law at the constant curve; matches the convention.

## BouRabeeGwynne.AmbientStoppedWalkLaw
- `isStoppedTilingWalkLaw_eq_ambient` (line 33): any law satisfying `IsStoppedTilingWalkLaw` equals the ambient walk law pushed by the stopped polygonal curve at the U-set. Since A ⊇ U-set, the curve stops at the U-set, which is the intended convention.

## BouRabeeGwynne.BoundarySurvivalScales
- `exists_boundary_survival_scales` (line 16): the premises are satisfiable (`nonvacuous_survival_scales` compiled). The conclusion gives `a ≤ r`, `a < κr/2`, and `q^N ≤ ε`; correct.

## BouRabeeGwynne.BrownianNestedClock
- `brownianSkeletonClock_nested` (line 15): the nested-clock recursion equals `continuousExitTime (U n)` for monotone U, including infinite exits; matches docstring.
- `stoppedBrownianRepresentative_range_subset` (line 30) and `brownianSkeletonExcursion_nested_range_subset` (line 61): range inclusions correct.

## BouRabeeGwynne.SkeletonSurvival
- `survivalUpTo` (line 52): `{ω | ∀ i ≤ n, ω i ∈ S i}`; matches.
- `survivalUpTo_le` (line 64): the bound `μ(S 0) · q^k` uses the transition estimate only on good histories, as the docstring says.

## BouRabeeGwynne.BrownianNestedSurvival
- `nestedBrownianBall` (line 17): ball of radius `R·r·R^i`; matches the nesting used in `nestedExcursionValid`.
- `brownian_nested_survival_le_of_step` (line 66): one-step excursion bound `q` gives `N`-step survival `q^N`; correct, and nonvacuous for q < 1 when the kernel estimate holds.
- `HasLipschitzBoundary.uniform_brownian_nested_survival` (line 207): NOTE: `∀ δ < κr/2` includes δ ≤ 0. Mathlib defines `cthickening δ E = {x | infEDist x E ≤ ENNReal.ofReal δ}` (Thickening.lean:181-182), so for δ ≤ 0 the event is `curveRangeEvent (closure U)`. That instance is implied by the δ > 0 instances, so the statement stays true and harmless.

## BouRabeeGwynne.BrownianExitRangeComparison
- `mem_closure_of_le_continuousExitTime` (line 16), `mem_cthickening_of_le_outerExit` (line 26), `stoppedBrownianRepresentative_dist_le_of_exit_le` (line 34): exit-time comparisons and collar inclusion; matches.

## BouRabeeGwynne.BrownianNestedConfinement
- `brownian_outer_exit_range_bad_le_of_step` (line 16): `μ{stopped curve leaves closedBall x η} ≤ q^N` under the nested step bound; correct.

## BouRabeeGwynne.BrownianStoppingEvent
- `standardBrownianLaw_stopping_event_le` (line 14): strong-Markov transfer bound; the a.s. finiteness hypothesis (line 18) makes the ⊤-totalization of `(τ ω).toNNReal` a null-set effect; correct.

## BouRabeeGwynne.BrownianExitInterval
- `mem_range_stoppedBrownianNextRepresentative` (line 16) and `dist_le_of_stoppedBrownianNextRepresentative_range` (line 38): both endpoints of `[τ, next exit]` lie in the excursion range; 2η bound correct.

## BouRabeeGwynne.BrownianStoppingOscillation
- `standardBrownianLaw_stopping_oscillation_le` (line 42): η-confinement of the fresh stopped path, with probability ≤ ε, gives 2η-oscillation on `[τ, next exit]`; matches.

## BouRabeeGwynne.BrownianBoundaryOscillation
- `HasLipschitzBoundary.uniform_brownian_outer_range` (line 17): `∃a` uniform in the boundary point p, the start x ∈ U near p, and δ ∈ (0, a]; matches.
- `HasLipschitzBoundary.uniform_brownian_boundary_oscillation` (line 47): NOTE: `innerDomain U b` (BrownianInnerExit.lean:15) is `{x | b < infDist x Uᶜ}`. Mathlib `infDist_empty` (HausdorffDistance.lean:477) gives 0 for an empty complement, so `innerDomain` collapses to ∅ for an unbounded U. Excluded by `hUb`. The ⊤ exit times for the bounded thickening are μ-null, so the totalization does not change μ. Harmless.

## BouRabeeGwynne.BrownianSkeletonOscillation
- `physical_clock_not_unitCurveExitOscillationBad` (line 22) and `brownianSkeleton_not_unitCurveExitOscillationBad` (line 71): reparametrization transfer; correct.
- `brownianSkeleton_oscillationBad_measure_le` (line 108): `μ(bad) ≤ ε + r`; the r-term is the still-active clock tail `(clock).1 = false`, which matches the flag semantics.

## BouRabeeGwynne.BrownianFiniteProbability
- `pastedBrownianCurve` (line 16): concatenation of the excursion prefix chain along a time partition; matches.
- `HasLipschitzBoundary.uniform_brownian_finiteSkeleton_probability` (line 28): quantifier order is a → (ε, δ) → (W, r) → K → (G, z, j₀, selector, P), matching the docstring. The `.1 = false` event is the still-active tail (the flag is `isNone` of the selector choice in `brownianClockUpdate`).

## BouRabeeGwynne.BrownianUniformFiniteProbability
- `HasLipschitzBoundary.uniform_brownian_finiteSkeleton_probability_all_indices` (line 17): the same statement with the label type J (universe u) quantified after a. A stronger form; matches.

## Nonvacuity examples
Compiled from the repository root with `lake env lean`: exit 0, no messages, about 5 s. The first attempt failed on my own example (`∃ a > 0` defaulted to ℕ); that was fixed, and nothing else failed. In the repository: `SpherePackings/Audit/Nonvacuity/Batch11.lean`. No `sorry`.

```lean
import BouRabeeGwynne.Section4BallExitConvergence
import BouRabeeGwynne.EuclideanWienerLaw
import BouRabeeGwynne.BrownianBoundaryOscillation
import BouRabeeGwynne.BoundarySurvivalScales
import SpherePackings.Support.Guards.LatticeTilings
import SpherePackings.Support.Guards.LipschitzBall

open MeasureTheory BouRabeeGwynne

/-- Section 4 ball-exit bundle `(G, N, hUD, happrox, hreg, μ)` is jointly satisfiable:
the lattice guard supplies the tiling sequence, nearest vertices with (1.3), the ambient collar
`closure (ball 0 1) ⊆ interior G.domain` and hypothesis (II); the Euclidean Wiener law is the
standard Brownian law. -/
theorem nonvacuous_section4_bundle (d : ℕ) (hd : 1 ≤ d) :
    ∃ (G : TilingSequence d) (N : NearestVertexData G),
      HasAmbientCollar (Metric.ball (0 : Euc d) 1) G.domain ∧
      N.ApproximationCondition ∧ PaperRegularity G ∧
      IsStandardBrownianLaw (euclideanWienerLaw d) := by
  obtain ⟨G, hUD, ⟨N⟩, happrox, hII⟩ := SpherePackings.exists_lattice_tilingSequence hd
  exact ⟨G, N, hUD, happrox N, Or.inr (Or.inl hII), isStandardBrownianLaw_euclideanWienerLaw d⟩

/-- The same bundle feeds the Section 4 theorem `eventually_ball_exit_test_error` with the
constant test function, so its hypotheses are met by actual objects. -/
theorem nonvacuous_section4_applied (d : ℕ) (hd : 1 ≤ d) : True := by
  obtain ⟨G, hUD, ⟨N⟩, happrox, hII⟩ := SpherePackings.exists_lattice_tilingSequence hd
  have _h := eventually_ball_exit_test_error hd G N (0 : Euc d) one_pos hUD (happrox N)
    (Or.inr (Or.inl hII)) (isStandardBrownianLaw_euclideanWienerLaw d)
    (fun _ => (0 : ℝ)) continuous_const one_pos
  trivial

/-- The Lipschitz-domain bundle for the Brownian boundary estimates: the unit ball is a
Lipschitz domain and `euclideanWienerLaw d` is a standard Brownian law. -/
theorem nonvacuous_lipschitz_bundle (d : ℕ) (hd : 1 ≤ d) :
    IsLipschitzDomain (Metric.ball (0 : Euc d) 1) ∧ IsStandardBrownianLaw (euclideanWienerLaw d) :=
  ⟨SpherePackings.isLipschitzDomain_ball hd, isStandardBrownianLaw_euclideanWienerLaw d⟩

/-- The Lipschitz bundle feeds `HasLipschitzBoundary.uniform_brownian_boundary_oscillation`. -/
theorem nonvacuous_boundary_oscillation (d : ℕ) (hd : 1 ≤ d) :
    ∃ a : ℝ, 0 < a := by
  have hL := (SpherePackings.isLipschitzDomain_ball hd).2
  obtain ⟨a, ha, _⟩ := HasLipschitzBoundary.uniform_brownian_boundary_oscillation hd hL
    Metric.isOpen_ball Metric.isBounded_ball (euclideanWienerLaw d)
    (isStandardBrownianLaw_euclideanWienerLaw d) one_pos one_pos
  exact ⟨a, ha⟩

/-- The scalar survival bundle of `exists_boundary_survival_scales` has concrete solutions. -/
theorem nonvacuous_survival_scales :
    ∃ N : ℕ, 0 < N := by
  obtain ⟨N, hN, _⟩ := exists_boundary_survival_scales (q := 1 / 2) (R := 2) (s := 1)
    (κ := 1) (η := 1) (ε := 1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨N, hN⟩
```

What they show:
- `nonvacuous_section4_bundle`: the Section 4 hypothesis bundle is jointly satisfiable for every d ≥ 1. The witnesses are a real `TilingSequence` from `SpherePackings.exists_lattice_tilingSequence`, nearest-vertex data with (1.3), the ambient collar `closure (ball 0 1) ⊆ interior D`, hypothesis (II) through `PaperRegularity`, and the standard Brownian law `euclideanWienerLaw d`. The Section 4 ball-exit lemmas therefore have non-empty hypotheses.
- `nonvacuous_section4_applied`: the bundle can be passed to `eventually_ball_exit_test_error` with the constant test function. The application typechecks against real objects. This shows applicability, not the content of the conclusion.
- `nonvacuous_lipschitz_bundle`: `IsLipschitzDomain (ball 0 1)` holds, together with the standard Brownian law. This is the bundle used by the Brownian boundary estimates.
- `nonvacuous_boundary_oscillation`: `HasLipschitzBoundary.uniform_brownian_boundary_oscillation` applies at `U = ball 0 1`, `μ = euclideanWienerLaw d`, `η = ε = 1`, and yields `∃ a > 0`.
- `nonvacuous_survival_scales`: the scalar premises are satisfiable with `q = 1/2`, `R = 2`, `s = 1`, `κ = 1`, `η = 1`, `ε = 1/2`. The check is trivial, but it shows the premises are not contradictory.

Not attempted: a nonvacuity instance for the one-step excursion hypothesis `hstep` of `brownian_nested_survival_le_of_step` with `q < 1`, and the Upstream `IsKolmogorovProcess` definition (not in this batch).

Out-of-batch observation (for the owner of PaperObjects.lean): `RegularityII` (lines 207-213) uses `mesh.toReal`, so a tiling sequence with infinite mesh and minimal tile volume ≥ 1 satisfies it with q_n = 0. That makes `PaperRegularity` weaker than paper hypothesis (II) when used without `ApproximationCondition`. That module should be recorded as an ISSUE. Within this batch it is harmless, as noted above.
