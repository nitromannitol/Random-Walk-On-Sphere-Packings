# Audit batch 4
| Module | Verdict | Summary |
|---|---|---|
| BouRabeeGwynne.BrownianStoppedLimit | OK | Bounded stopped harmonic identity; hypothesis bundle satisfiable (see nonvacuity witness 2). |
| BouRabeeGwynne.BrownianFiniteExit | OK | A.s. finite exit from bounded sets, Gaussian tail lemmas; `1 ≤ d` is essential and assumed. |
| BouRabeeGwynne.BrownianHarmonicExit | NOTE | Harmonic exit identity; `toNNReal` of exit time in the integrand is junk only on a μ-null set. |
| BouRabeeGwynne.BrownianExcursionKernel | NOTE | Kernel `μ.map (stoppedBrownianRepresentative U)` is the excursion law only when P(exit = ∞) = 0; all uses in this batch are bounded balls. |
| BouRabeeGwynne.LipschitzDomain | NOTE | Chart definition is the standard local strict-epigraph definition; `d - 1` truncation is harmless (d = 0 has no frontier). |
| BouRabeeGwynne.LipschitzExteriorGeometry | OK | Coordinate projections and norm bounds; correct. |
| BouRabeeGwynne.LipschitzExteriorBalls | OK | Ball of radius ρ below a K-Lipschitz graph when (K+1)ρ ≤ a; correct. |
| BouRabeeGwynne.LipschitzChartExteriorBalls | OK | Exterior ball inside one rigid chart; cylinder margins are exactly what is needed. |
| BouRabeeGwynne.LipschitzLocalExteriorBalls | OK | Local exterior balls with κ = 1/(2(K+1)); correct. |
| BouRabeeGwynne.LipschitzUniformExteriorBalls | OK | Uniform s, κ by compactness of the frontier; empty-frontier case vacuous; correct. |
| BouRabeeGwynne.ExteriorBallBuffer | OK | Half-radius ball lies outside the δ-collar for δ < R/2; correct by triangle inequality. |
| BouRabeeGwynne.BrownianBoundaryExcursion | OK | Uniform boundary survival contraction, ∃ q < 1, R > 1 before ∀ U, p, c, r; statement and bound are correct. |
| BouRabeeGwynne.WalkCanonicalStopping | NOTE | `untopD 0` makes a no-exit prefix have exit index 0; excluded by `f a ∉ U`. The Bool flag is not used by the support set. |
| BouRabeeGwynne.BoundaryStoppingGeometry | OK | Vertex-exit time lies in [l, u] under the stated collar conditions; both bounds verified. |
| BouRabeeGwynne.BrownianInnerExit | NOTE | `innerDomain` uses `infDist x Uᶜ`, which is 0 when U = univ; such U are excluded by every caller. |
| BouRabeeGwynne.UnitCurveOscillation | OK | Affine reparametrization onto [a, b], closed diameter bound, measurable bad set; correct. |
| BouRabeeGwynne.FiniteStoppedCurveComparison | OK | Deterministic comparison; hypotheses consistent; conclusion `ofReal (ε + η)` is correct. |
| BouRabeeGwynne.UnitCurveExitMonotone | OK | Capped exit time commutes with monotone surjective reparametrization; correct. |
| BouRabeeGwynne.PhysicalExcursionRecovery | OK | Monotone knots allow zero durations as documented; zero total duration handled. |
| BouRabeeGwynne.BrownianExitRestart | OK | Restart identity holds including the ∞ case; no hidden premise. |
| BouRabeeGwynne.BrownianPathFreezing | NOTE | Measurability of the frozen path at a stopping time; `toNNReal` totalization on {τ = ∞} is explicit and harmless. |
| BouRabeeGwynne.BrownianStoppingLimit | OK | `map_eq_of_ae_tendsto_of_map_eq` is a correct dominated-convergence law identification. |
| BouRabeeGwynne.BoundedBrownianMarkov | OK | Strong Markov at bounded stopping times; statement correct. |
| BouRabeeGwynne.BrownianStrongMarkov | NOTE | Strong Markov at a.s. finite times; `toNNReal` junk only on {τ = ∞}, a μ-null set excluded by `hfinite`. |
| BouRabeeGwynne.BrownianStoppingHistory | NOTE | Joint history/future law; same `toNNReal` totalization on a μ-null set guarded by `hfinite`. |
| BouRabeeGwynne.BrownianNextExit | OK | `brownianNextExitTime = τ + η`; ⊤ absorbs the junk; a.s. finiteness correct. |
| BouRabeeGwynne.BrownianPhysicalSegments | OK | Stopped representative equals the physical-time segment as maps; hypotheses present. |
| BouRabeeGwynne.PhysicalPrefixExit | OK | Exit parameter times T equals the exit time when τ ≤ T; premise present. |
| BouRabeeGwynne.BrownianSelectedExit | OK | `none` retains τ; the frozen-choice hypothesis is satisfiable (constant choice). |

Totals: OK 21, NOTE 8, ISSUE 0. No declaration was found to be false, vacuous or contradictory. The NOTEs are junk-value regimes that either lie on a μ-null set guarded by a hypothesis, or are unreachable from the batch's uses. One regime is not guarded in the definition itself: `brownianExcursionKernel` for unbounded U (see BrownianExcursionKernel). Its docstring is accurate only for bounded U, and downstream definitions outside this batch use it with unbounded-capable hypotheses; flagged for their auditor.

Shared definitions verified (outside this batch): `IsStandardBrownianLaw` (StoppedCurveLaws.lean:38) is d independent Mathlib `IsBrownianReal` coordinates, which matches standard d-dimensional Brownian motion; `continuousExitTime` (StoppedCurveLaws.lean:67) is the infimum of first times in the complement of U, with `⨅ ∅ = ⊤` documented; `IsHarmonicOn` (Harmonic.lean:17) is `ContDiffOn ℝ 2` plus `Δ h = 0` on U; `IsDomain` (PaperObjects.lean:17) is open, nonempty and preconnected; `pathRangeEvent` (ContinuousPathRange.lean:16) is the sup-norm bound on [0, T]; `dyadicStoppingTime` (BrownianStoppingApprox.lean:19) is ⌈σ 2ⁿ⌉/2ⁿ, an upper dyadic approximation; `shiftedBrownianPath` (BrownianWeakMarkov.lean:18) is `ω(t + ·) − ω t`; `brownianNaturalFiltration` (BrownianExitStoppingTime.lean:17) is the natural filtration of coordinate evaluations; `exitTime` (StoppedWalk.lean:117) is the hitting time of the complement, with `exitTime_eq_top_iff` at line 120.

Paper references checked: `paper/rw-spheres.tex:260` (Theorems A and B assume a bounded Lipschitz domain, with a footnote saying Lipschitz is needed so that Brownian motion started near the boundary exits near its start); `paper/rw-spheres.tex:1483` (a bounded Lipschitz domain in another theorem); `paper/rw-spheres.tex:1600` (Brownian exit estimate for Lipschitz U, cited there to Mörters–Peres Lemma 3.11). The paper does not define "Lipschitz domain"; the formal definition is the standard one.

---

## BouRabeeGwynne.BrownianStoppedLimit
- `measurable_nnreal_brownian_stopping` (line 19), `measurable_brownian_random_evaluation` (26), `dyadic_grid_length_le` (32): measurability and grid-length helpers; correct.
- `standardBrownianLaw_bounded_stopped_harmonic_difference` (46): matches its docstring. Hypotheses (`ContDiff ℝ 2 f`, `HasCompactSupport f`, `IsHarmonicOn f U`, σ bounded stopping time, path in U before σ) are satisfiable; the same bundle is witnessed by `nonvacF` below. No junk values.

## BouRabeeGwynne.BrownianFiniteExit
- `standardGaussian_measure_shrinking_interval_tendsto_zero` (21, private): correct; uses `NullSingletonClass` for the Gaussian.
- `gaussian_square_time_measure_bounded_tendsto_zero` (54): matches its docstring (Gaussian mass of a fixed interval at variance (n+1)² tends to 0).
- `preBrownian_ae_not_bounded_square_times` (75): correct; the conclusion is an a.s. statement about the pre-Brownian process.
- `standardBrownianLaw_ae_finiteExit` (95): matches docstring. Requires `1 ≤ d`: in d = 0 the single point never leaves U, so the hypothesis is necessary and present.
- `standardBrownianLaw_measure_lateExit_le` (123): correct. On {exit > t} one has z + B_t ∈ U, so |B_t¹| ≤ 2R.
- `standardBrownianLaw_uniform_exitTail` (152): matches docstring ("time truncation"); the ∀ᶠ n quantifier is over all z ∈ U.

## BouRabeeGwynne.BrownianHarmonicExit
- `standardBrownianLaw_eval_zero_ae` (21): correct.
- `standardBrownianLaw_integral_exit_harmonic_compactSupport` (30): correct optional-stopping identity. The integrand `f (z + ω (continuousExitTime U z ω).toNNReal)` uses the junk value 0 on {τ = ∞}; that set is μ-null by `standardBrownianLaw_ae_finiteExit`, so the integral is unaffected.
- `standardBrownianLaw_integral_stopped_endPoint_harmonic_compactSupport` (108): correct push-forward restatement.
- Nonvacuity: the hypothesis bundle is satisfied by the nonzero compactly supported harmonic function `nonvacF` (witness 2 below).

## BouRabeeGwynne.BrownianExcursionKernel
- `translatedBrownianPath` (21, def): `t ↦ z + ω t`; correct.
- `continuous_translatedBrownianPath` (24), `continuousExitTime_translated` (30), `stoppedBrownianRepresentative_translated` (43), `measurable_stoppedBrownianRepresentative_joint` (61): helpers; correct.
- `brownianExcursionKernel` (74, def): NOTE. Defined for every open U, with no boundedness hypothesis. `stoppedBrownianRepresentative` (StoppedCurveLaws.lean:74) totalizes τ = ∞ to the constant path at z. When U is unbounded and P(τ = ∞) > 0, that totalized mass is part of the push-forward, so the kernel is not the law of the excursion. Example: d = 3, U = ℝ³ \ closedBall(0,1), z with |z| > 1; P(τ = ∞) = 1 − 1/|z| > 0. The docstring ("the actual pushforward law") holds only for bounded U or with τ < ∞ a.s. Every use inside this batch is a bounded ball (BrownianBoundaryExcursion.lean:33, 107). Downstream definitions with only `IsOpen` hypotheses are flagged below.
- `brownianExcursionKernel_apply` (86): rfl; correct.
- `brownianExcursionKernel_isMarkov` (90, instance): correct for `IsProbabilityMeasure μ`.
- `brownianExcursionKernel_ae_start` (97): correct; holds for every open U (τ = ∞ paths also start at z).
- `stoppedBrownianRepresentative_mem_closure` (107) and `brownianExcursionKernel_ae_mem_closure` (127): match docstring; `hUb` and `hd` are used.
- `brownianExcursionKernel_project` (143): correct; holds for every open U.
- Cross-batch: `brownianSkeletonInitialLaw` (BrownianSkeletonLaw.lean:23–26) and `BrownianExcursionSampler.lean:69, 134` use `brownianExcursionKernel (hU j) μ` with only `∀ j, IsOpen (U j)`. If those objects are meant for unbounded cells, the totalization above matters there. Their auditor should check.

## BouRabeeGwynne.LipschitzDomain
- `cylinderCoordinates` (12, def): `none ↦ t`, `some j ↦ q j`; correct.
- `HasLipschitzBoundary` (24, def): matches the standard definition: at each boundary point a rigid chart, a Lipschitz graph φ with φ(0) = 0, the graph inside the cylinder, and U ∩ cylinder equal to the strict epigraph. Slits and boundary points with U on both sides are excluded, because the chart equivalence forces one side. Paper: `rw-spheres.tex:260` (bounded Lipschitz domain).
- NOTE: `Euc (d - 1)` and `Option (Fin (d - 1))` use natural-number subtraction. For d = 0, `Option (Fin 0)` has one point while `Euc 0` has none, so no isometry R exists and `HasLipschitzBoundary U` holds iff frontier U = ∅. In d = 0 every open set has empty frontier (the space is a point), so the chart clause is never exercised there; the batch's chart-based lemmas either assume `1 ≤ d` or have empty frontier in d = 0. I checked the lemmas in this batch only, not every consumer.
- `IsLipschitzDomain` (35, def): IsDomain ∧ HasLipschitzBoundary; boundedness is deliberately left to the theorems, as the docstring says.
- `IsLipschitzDomain.isDomain` (38), `.hasLipschitzBoundary` (41): projections; correct.
- Nonvacuity: `SpherePackings.isLipschitzDomain_ball` (cited, compiled in witness 1).

## BouRabeeGwynne.LipschitzExteriorGeometry
- `cylinderHorizontal` (14), `cylinderHorizontal_cylinderCoordinates` (18), `cylinderCoordinates_reconstruct` (24), `norm_cylinderCoordinates_sq` (30), `norm_cylinderHorizontal_le` (34), `cylinderHorizontal_sub` (41), `cylinderHorizontal_dist_le` (48): coordinate projection and its 1-Lipschitz property; correct.

## BouRabeeGwynne.LipschitzExteriorBalls
- `closedBall_below_lipschitz_graph` (17): if t ≤ φ q and (K+1)ρ ≤ a, the closed ball of radius ρ at (q, t−a) lies below the graph. Verified: φ(y_h) ≥ φ(q) − Kρ ≥ t − Kρ ≥ y_v. Correct.

## BouRabeeGwynne.LipschitzChartExteriorBalls
- `closedBall_compl_of_lipschitz_chart` (14): the ball of radius ρ around (q, t−a) in the chart lies in Uᶜ; the margins `‖q‖+ρ < r` and `|t−a|+ρ < h` are the ones used. Correct.

## BouRabeeGwynne.LipschitzLocalExteriorBalls
- `HasLipschitzBoundary.exists_local_exterior_balls` (16): s = min(r₀,h₀)/4, κ = 1/(2(K+1)) ≤ 1/2. For x ∈ frontier U near p and r < s there is c with dist c x = r and closedBall c (κr) ⊆ Uᶜ. Correct; hypothesis `IsOpen U` is used.

## BouRabeeGwynne.LipschitzUniformExteriorBalls
- `HasLipschitzBoundary.exists_uniform_exterior_balls` (14): uniform s, κ over the compact frontier (from boundedness). The conclusion `∃ c, dist c p = r ∧ closedBall c (κr) ⊆ Uᶜ` is the standard uniform exterior-ball condition. Empty frontier: vacuous. Correct.

## BouRabeeGwynne.ExteriorBallBuffer
- `closedBall_subset_compl_cthickening_of_exteriorBall` (14): for δ < R/2, closedBall c (R/2) avoids cthickening δ U. Verified via `cthickening_subset_iUnion_closedBall_of_lt`. Correct.
- `HasLipschitzBoundary.exists_uniform_buffered_exterior_balls` (27): correct; the δ quantifier covers negative δ, which gives an empty collar.

## BouRabeeGwynne.BrownianBoundaryExcursion
- `curveRangeEvent` (17, def): `{f | ∀ t, f t ∈ K}`; correct.
- `isClosed_curveRangeEvent` (20): correct.
- `standardBrownianLaw_uniform_boundary_excursion_survival` (25): quantifier order is right (∃ q R, then ∀ U p c r). q = 1 − a/2 < 1, R = L + 2 > 1. The bound is uniform over all U (no openness needed), all scales r > 0, and all starts x with dist x p ≤ r. Hypotheses are not contradictory. The proof uses ball(p, R r), which is bounded.
- `HasLipschitzBoundary.uniform_brownian_excursion_survival` (98): correct; ∃ s κ q R, then ∀ p ∈ frontier U, r < s. This is a survival contraction, not the paper's estimate |τ_δ − τ^U| ≤ Cδ at `rw-spheres.tex:1600`. That estimate is cited there and not proved; this lemma does not claim to be it. Its consumers should be checked against this.
- Nonvacuity: witness 1 instantiates this theorem at the unit disc in ℝ² with the Wiener law.

## BouRabeeGwynne.WalkCanonicalStopping
- `pastedWalkCurve` (21, def): concatenation of the prefix chain on the time partition P; correct.
- `measurable_pastedWalkCurve` (26): correct.
- `canonicalWalkStoppingSupport` (32, def): the three conjuncts (projection equals the reconstructed stopped curve; `f a ∉ U`; `a = 0 ∨` prefix in cthickening δ U) match the intended support. NOTE: `a` is `pastedVertexExitParameter` (ClockedWalkExitParameter.lean), which uses `concatenatedExitIndex` (line 119) with `untopD 0`. A prefix that never leaves U gets index 0, hence a = 0. The support rejects it: `exitTime_eq_top_iff` (StoppedWalk.lean:120) says the exit time is ⊤ only if every vertex lies in U, so f 0 ∈ U and `f a ∉ U` fails. Harmless. The Bool flag (the permanent-stop bit of `actualWalkStage`, ActualWalkSkeleton.lean:75–77) is not used by the set; it enters only through `trajectoryLaw_map_ae_canonicalWalkStoppingSupport`.
- `measurableSet_canonicalWalkStoppingSupport` (39): correct under `MeasurableSet U`.
- `canonicalWalkStoppingSupport_pre` (53): before the vertex exit, the pasted curve lies in cthickening δ U; correct.
- `polygonalCurve_prefix_of_scaled_vertex` (75, private), `prefixTimeData_actualWalkStage` (93), `pastedWalkCurve_actual_eq_comp_canonical` (108): helper identities.
- `canonicalWalkStoppingSupport_actual` (147): hypotheses `hexit`, `hedge` are the right ones; `untopD 0` is not reached because `hexit` forces finiteness.
- `trajectoryLaw_map_ae_canonicalWalkStoppingSupport` (237): the conclusion `(e n).1 = false ∨ e ∈ support` is a support statement with the active case left to a separate tail bound, as the docstring says. Not weaker than its docstring.

## BouRabeeGwynne.BoundaryStoppingGeometry
- `vertexExit_timeChange_mem_boundaryInterval` (18): the matched exit time lies in [l, u], using the inner ball and outer cthickening conditions. Both halves verified. Zero exit time allowed, as documented.
- `curveSpace_edist_prefixes_le_of_vertexExit` (43): edist ≤ ofReal(ε + η); the endpoints b and a both lie in [l, u], so the oscillation hypothesis applies. Correct.

## BouRabeeGwynne.BrownianInnerExit
- `innerDomain` (15, def): `{x | ε < infDist x Uᶜ}`. NOTE: for U = univ, Uᶜ = ∅ and `infDist x ∅ = 0` (Mathlib convention), so the inner domain is ∅ for ε > 0. Harmless: `FiniteStoppedCurveComparison` requires a point of g outside thickening δ U, which excludes U = univ, and `innerExit_exists_frontier_near` assumes bounded U ≠ univ.
- `isOpen_innerDomain` (18), `closure_innerDomain_subset` (22), `frontier_innerDomain_infDist` (31), `closedBall_subset_of_mem_innerDomain` (36): correct.
- `innerExit_position` (44): the actual inner exit lies in U and within ε of Uᶜ, including the case where the exit is at time 0. Correct.
- `innerExit_exists_frontier_near` (61): ∃ p ∈ frontier U with dist ≤ ε; correct.

## BouRabeeGwynne.UnitCurveOscillation
- `unitIntervalAffine` (15, def) and `_zero` (25), `_one` (29), `unitIntervalAffine_mem_Icc` (33), `unitIntervalAffine_surjOn` (42): affine map [0,1] → [a,b] covering Icc a b; correct. Orientation does not matter.
- `unitCurveInterval` (48, def), `measurable_unitCurveInterval` (51): correct.
- `unitCurveDiameterBound` (66, def), `isClosed_unitCurveDiameterBound` (69): correct; η < 0 gives ∅ and is harmless.
- `unitCurveExitOscillationBad` (79, def), `measurableSet_unitCurveExitOscillationBad` (84): correct; inherits the `unitCurveExitTime` cap at 1 (UnitCurveExit.lean:34).
- `unitCurve_oscillation_le_of_not_bad` (93): correct.

## BouRabeeGwynne.FiniteStoppedCurveComparison
- `curveSpace_edist_prefix_unitExit_le_of_not_bad` (16): hypotheses `ε + mesh < δ`, `hgood`, `hgexit` are jointly consistent and needed. The bound `ofReal (ε + η)`: if η < 0 the bad set is everything, so `hgood` is false and the statement is vacuous; no junk.
- `curveSpace_edist_prefix_unitExit_le_of_endpoint_outside` (48): specialization at g 1; correct.

## BouRabeeGwynne.UnitCurveExitMonotone
- `unitCurveExitTime_comp_monotone` (15): φ monotone, φ 0 = 0, φ 1 = 1, so φ is surjective and exit commutes with reparametrization. Hypotheses are satisfied by the identity. Correct.
- `unitCurveExitProjection_comp_monotone` (44): correct.

## BouRabeeGwynne.PhysicalExcursionRecovery
- `physicalTimeSegment` (13, def), `physicalTimeSegment_zero` (24), `_one` (30), `_self` (36): correct.
- `PhysicalTimeKnots` (47, structure): monotone times with `times 0 = 0`. Zero durations allowed, as documented. `duration` (56) is the last time.
- `normalize` (61, def): requires `0 < duration`, the stated hypothesis. `chain` (71, def): consecutive segments match at endpoints. `chain_eq_restrictChain` (77) and `project_concatenate_chain` (98): zero-total-duration case handled.

## BouRabeeGwynne.BrownianExitRestart
- `continuousExitTime_pos_of_mem` (18): correct for open U.
- `continuousExitTime_eq_add_shift` (29): the restart identity under `t ≤ τ`; holds for τ = ∞ as stated. Correct.
- `continuousExitTime_shift_endpoint` (59): correct.

## BouRabeeGwynne.BrownianPathFreezing
- `frozenBrownianPath` (19, def): `s ↦ ω (min s t)`; correct.
- `frozenBrownianPath_apply` (22), `shiftedBrownianPath_frozen` (25), `measurable_frozenBrownianPath` (34), `continuousExitTime_le_frozen` (42): correct.
- `continuousExitTime_frozen` (51): the frozen exit is τ if τ ≤ t, else ∞; correct, including τ = t.
- `isStoppingTime_of_frozen_events` (74): correct criterion for a measurable τ.
- `measurable_frozenBrownianPath_stopping` (88): NOTE. Uses `(τ ω).toNNReal`; on {τ = ∞} the value is frozen at ω 0 via an explicit `piecewise`, and the docstring documents this. Harmless.

## BouRabeeGwynne.BrownianStoppingLimit
- `continuous_shiftedBrownianPath` (21): correct.
- `map_eq_of_ae_tendsto_of_map_eq` (28): correct; bounded continuous tests identify the limit law. Needs `IsFiniteMeasure P`, which is stated.

## BouRabeeGwynne.BoundedBrownianMarkov
- `stoppingTime_measurableSpace_congr` (19, private): correct.
- `standardBrownianLaw_boundedStopping_map_restrict` (26): (μ|A) ∘ θ_σ⁻¹ = μ(A)·μ for bounded σ and A ∈ F_σ. Correct strong Markov statement.
- `standardBrownianLaw_boundedStoppingENNReal_map_restrict` (59): extended-valued τ ≤ N; no junk since τ ≤ N. Correct.

## BouRabeeGwynne.BrownianStrongMarkov
- `tendsto_measure_truncated_by_ae_finite` (20, private): correct.
- `standardBrownianLaw_aeFiniteStopping_map_restrict` (46): NOTE. The shift uses `(τ ω).toNNReal`; on {τ = ∞}, a μ-null set excluded by `hfinite`, so the identity is unaffected. Otherwise correct.
- `standardBrownianLaw_exit_map_restrict` (97): specialization to the exit time; correct.

## BouRabeeGwynne.BrownianStoppingHistory
- `measurable_brownianPosition_stopping` (19): correct.
- `standardBrownianLaw_stopping_history_joint` (31): NOTE. Same `toNNReal` shift as above, under `hfinite` (μ-null junk). The product-law identity is correct and not affected.

## BouRabeeGwynne.BrownianNextExit
- `measurable_continuousExitTime_joint` (16): correct.
- `brownianNextExitTime` (21, def): τ + exit time of the shifted path. ⊤ absorbs the `toNNReal` junk inside, so no junk value is observable. Correct.
- `le_brownianNextExitTime` (26), `measurable_brownianNextExitTime` (31): correct.
- `brownianNextExitTime_frozen` (52): correct freezing identity under the hypothesis on τ.
- `isStoppingTime_brownianNextExitTime` (94): correct.
- `standardBrownianLaw_ae_finiteNextExit` (107): the next exit is a.s. finite for bounded open U given a.s. finite τ. Correct.

## BouRabeeGwynne.BrownianPhysicalSegments
- `stoppedBrownianRepresentative_eq_physicalTimeSegment` (14): equality as continuous maps, not only as endpoints (matches docstring).
- `stoppedBrownianNextRepresentative_eq_physicalTimeSegment` (23): hypothesis `hfinite` is present and needed for the `toNNReal` sum. Correct.

## BouRabeeGwynne.PhysicalPrefixExit
- `unitCurveExitTime_eq_of_exit_at` (15), `physicalTimeSegment_initial_apply` (23), `prefix_physicalTimeSegment_eq` (29): correct.
- `unitCurveExitTime_physicalTimeSegment_mul` (42): exit parameter × T equals the physical exit time when τ ≤ T; the premise is present and needed. Correct.
- `unitCurveExitRepresentative_physicalTimeSegment` (80), `unitCurveExitProjection_physicalTimeSegment` (90): correct.

## BouRabeeGwynne.BrownianSelectedExit
- `brownianSelectedNextExitTime` (17, def): `none` keeps τ, `some j` uses U j. Matches the docstring. Correct.
- `le_brownianSelectedNextExitTime` (24), `measurable_brownianSelectedNextExitTime` (32), `brownianSelectedNextExitTime_frozen` (48): correct; the `hchoice` frozen-invariance hypothesis is satisfiable (a constant choice).
- `isStoppingTime_brownianSelectedNextExitTime` (76): correct.
- `standardBrownianLaw_ae_finiteSelectedNextExit` (92): correct; uses `hfinite` and per-j finiteness.

---

## Nonvacuity examples

Source: `Nonvacuity.lean`.
Compiled from the repository root with
`lake env lean Nonvacuity.lean`.
Exit status 0, no errors. The output is in `nonvacuity.out` in the same directory.

Verbatim source:

```lean
import BouRabeeGwynne.BrownianBoundaryExcursion
import BouRabeeGwynne.BrownianHarmonicExit
import BouRabeeGwynne.EuclideanWienerLaw
import SpherePackings.Support.Guards.LipschitzBall
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

open MeasureTheory Metric InnerProductSpace Laplacian
open scoped NNReal ENNReal

namespace BouRabeeGwynne

/-! Witness 1: the hypothesis bundle of `HasLipschitzBoundary.uniform_brownian_excursion_survival`
(`IsOpen U`, bounded `U`, `HasLipschitzBoundary U`, a probability measure with
`IsStandardBrownianLaw`) is satisfied by the open unit ball of `ℝ²` and the Wiener law. -/

#check HasLipschitzBoundary.uniform_brownian_excursion_survival (d := 2) (by norm_num)
    (SpherePackings.isLipschitzDomain_ball (d := 2) (by norm_num)).hasLipschitzBoundary
    isOpen_ball isBounded_ball (euclideanWienerLaw 2) (isStandardBrownianLaw_euclideanWienerLaw 2)

example := HasLipschitzBoundary.uniform_brownian_excursion_survival (d := 2) (by norm_num)
    (SpherePackings.isLipschitzDomain_ball (d := 2) (by norm_num)).hasLipschitzBoundary
    isOpen_ball isBounded_ball (euclideanWienerLaw 2) (isStandardBrownianLaw_euclideanWienerLaw 2)

/-! Witness 2: the hypotheses of `standardBrownianLaw_integral_exit_harmonic_compactSupport`
(`ContDiff ℝ 2 f`, `HasCompactSupport f`, `IsHarmonicOn f U`) with a NONZERO `f` on `U`. -/

/-- Cutoff: `χ = 1` on `ball 0 2`, support in `closedBall 0 3`. -/
noncomputable def nonvacBump : ContDiffBump (0 : Euc 2) :=
  { rIn := 2, rOut := 3, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }

/-- The linear functional `x ↦ x₀`. -/
noncomputable def nonvacCoord : Euc 2 →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin 2)

/-- Compactly supported `C^∞` test function, equal to `x ↦ x₀` on `ball 0 2`, hence
nonzero on the unit ball and harmonic there. -/
noncomputable def nonvacF : Euc 2 → ℝ := fun x => nonvacBump x * nonvacCoord x

lemma nonvacF_contDiff : ContDiff ℝ 2 nonvacF :=
  (nonvacBump.contDiff.mul nonvacCoord.contDiff)

lemma nonvacF_hasCompactSupport : HasCompactSupport nonvacF :=
  nonvacBump.hasCompactSupport.mul_right

lemma laplacian_nonvacCoord (x : Euc 2) : Δ (fun y => nonvacCoord y) x = 0 := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp [iteratedFDeriv_succ_eq_comp_right]

lemma nonvacF_harmonic : IsHarmonicOn nonvacF (ball (0 : Euc 2) 1) := by
  refine ⟨nonvacF_contDiff.contDiffOn, fun x hx => ?_⟩
  have hx2 : x ∈ ball (0 : Euc 2) 2 := ball_subset_ball (by norm_num) hx
  have hev : nonvacF =ᶠ[nhds x] fun y => nonvacCoord y := by
    filter_upwards [isOpen_ball.mem_nhds hx2] with y hy
    have hy' : y ∈ closedBall (0 : Euc 2) nonvacBump.rIn := by
      have hr : nonvacBump.rIn = 2 := rfl
      rw [hr]
      exact ball_subset_closedBall hy
    simp only [nonvacF, nonvacBump.one_of_mem_closedBall hy', one_mul]
  exact ((laplacian_congr_nhds hev).eq_of_nhds).trans (laplacian_nonvacCoord x)

#check standardBrownianLaw_integral_exit_harmonic_compactSupport (d := 2) (by norm_num)
    (isStandardBrownianLaw_euclideanWienerLaw 2) isOpen_ball isBounded_ball
    nonvacF_contDiff nonvacF_hasCompactSupport nonvacF_harmonic (0 : Euc 2)

end BouRabeeGwynne
```

Compiler output (verbatim, from `nonvacuity.out`; the two `#check` lines and the `example` produced no errors):

```
HasLipschitzBoundary.uniform_brownian_excursion_survival
  (Mathlib.Meta.NormNum.isNat_le_true (Mathlib.Meta.NormNum.isNat_ofNat ℕ (Eq.refl 1))
    (Mathlib.Meta.NormNum.isNat_ofNat ℕ (Eq.refl 2)) (Eq.refl true))
  (IsLipschitzDomain.hasLipschitzBoundary
    (SpherePackings.isLipschitzDomain_ball
      (Mathlib.Meta.NormNum.isNat_le_true (Mathlib.Meta.NormNum.isNat_ofNat ℕ (Eq.refl 1))
        (Mathlib.Meta.NormNum.isNat_ofNat ℕ (Eq.refl 2)) (Eq.refl true))))
  isOpen_ball isBounded_ball (euclideanWienerLaw 2)
  (isStandardBrownianLaw_euclideanWienerLaw
    2) : ∃ s > 0,
  ∃ κ > 0,
    ∃ q R,
      0 ≤ q ∧
        q < 1 ∧
          1 < R ∧
            ∀ p ∈ frontier (ball 0 1),
              ∀ (r : ℝ≥0),
                0 < r →
                  ↑r < s →
                    ∀ (x : Euc 2) (δ : ℝ),
                      dist x p ≤ ↑r →
                        δ < κ * ↑r / 2 →
                          ((brownianExcursionKernel ⋯ (euclideanWienerLaw 2)) x)
                              (curveRangeEvent (cthickening δ (ball 0 1))) ≤
                            ENNReal.ofReal q
standardBrownianLaw_integral_exit_harmonic_compactSupport
  (Mathlib.Meta.NormNum.isNat_le_true (Mathlib.Meta.NormNum.isNat_ofNat ℕ (Eq.refl 1))
    (Mathlib.Meta.NormNum.isNat_ofNat ℕ (Eq.refl 2)) (Eq.refl true))
  (isStandardBrownianLaw_euclideanWienerLaw 2) isOpen_ball isBounded_ball nonvacF_contDiff nonvacF_hasCompactSupport
  nonvacF_harmonic
  0 : ∫ (ω : BrownianPath 2), nonvacF (0 + ω (continuousExitTime (ball 0 1) 0 ω).toNNReal) ∂euclideanWienerLaw 2 =
  nonvacF 0
```

What the examples show:
- **Witness 1 (boundary survival bundle).** The hypotheses of `HasLipschitzBoundary.uniform_brownian_excursion_survival` are jointly satisfiable by real objects: the open unit disc in ℝ² (Lipschitz by the existing `SpherePackings.isLipschitzDomain_ball`), bounded and open, with the Wiener law `euclideanWienerLaw 2` (standard by `isStandardBrownianLaw_euclideanWienerLaw`). The instantiated conclusion is a non-trivial statement with q < 1 and R > 1. It is not vacuous.
- **Witness 2 (harmonic exit bundle).** `nonvacF` is C^∞ with compact support, harmonic on the unit ball (it equals x₀ on ball 0 2), and nonzero there. So the harmonic-exit hypotheses are satisfied by a non-trivial function, not only by f = 0. The displayed instance has z = 0, where f(0) = 0; the example shows satisfiability, not a nonzero right-hand side.
- Not separately instantiated: `IsLipschitzDomain` and `IsStandardBrownianLaw` are used through the cited existing witnesses; no new example was built for them.
