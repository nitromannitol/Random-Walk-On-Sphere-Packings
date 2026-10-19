# Audit batch 5
| Module | Verdict | Summary |
|---|---|---|
| BouRabeeGwynne.BrownianSkeletonClock | NOTE | Clock/flag/time definitions match the intended semantics; ∞-time junk only on a null set; selector index 0 unused; z ∉ U j₀ gives a zero-length active excursion (harmless convention). |
| BouRabeeGwynne.BrownianObservedHistory | OK | Freezing-based stopping-time measurability and endpoint lemmas; hypotheses are exactly the stopping-time freezing identities. |
| BouRabeeGwynne.BrownianExcursionSampler | OK | Sampler matches the selected/absorbing excursion kernels; terminated flag is absorbing. |
| BouRabeeGwynne.BrownianSkeletonExcursion | OK | Successive excursions use the original clock and the shifted path at it; endpoint and flag identities consistent. |
| BouRabeeGwynne.BrownianSkeletonLaw | OK | Full excursion-sequence law equals the Markov trajectory law; premises satisfied by the Wiener law (Nonvacuity 1). |
| BouRabeeGwynne.BrownianSkeletonPrefix | OK | Physical knots (0, τ₀,…,τₙ) give n+1 pieces matching excursions 0..n; duration equals the clock; no junk (finiteness hypothesis carried). |
| BouRabeeGwynne.BrownianUniformModulus | NOTE | Modulus event and its ε-oscillation meaning are right; docstring mentions translation invariance and "uniform over translated starts", which the file does not state or prove. |
| BouRabeeGwynne.BrownianSkeletonTail | OK | Pigeonhole short-step lemma and uniform skeleton-count tail; quantifier order ∃K ∀z∈U is correct. |
| BouRabeeGwynne.BrownianNestedExit | OK | Exit times are monotone in the domain; nested restart identity holds including ∞. |
| BouRabeeGwynne.BrownianActiveSkeletonTail | OK | Uniform active-tail bound with K depending only on V, ε, η, μ; margin hypothesis satisfiable (Nonvacuity 2). |
| BouRabeeGwynne.BrownianStoppedSkeleton | OK | Stopped-curve reconstruction under the target-exit hypothesis; Lévy–Prokhorov bound by bad-event mass; hypotheses consistent. |
| BouRabeeGwynne.FinitePartitionCouplingKernel | NOTE | Exact marginals and failure bound are right; `(κ a univ)⁻¹ = ⊤` at zero mass is harmless (⊤ • 0 = 0). |
| BouRabeeGwynne.FiniteCellCouplingError | OK | Cell-error bound with ENNReal truncated subtraction used only as an upper bound; covering hypothesis ν(⋃F)=1 is the right one. |
| BouRabeeGwynne.SkeletonCoupling | OK | Adaptive first-failure bound uses the one-step estimate only on good histories; joint path law has the stated marginals. |
| BouRabeeGwynne.WalkBrownianCoupling | NOTE | Matching cells exclude terminated states; `brownianSelectorForWalk` at n=0 is unused junk; joint-law marginal lemma does not link z to pos v (downstream supplies dist ≤ a). |
| BouRabeeGwynne.WalkBrownianCellMeasures | NOTE | Cell masses and finite-cell bad bound are right; m = 0 is vacuous (hcover with z ∈ U is contradictory); herror is automatic when b ≥ m+1. |
| BouRabeeGwynne.FixedBallCover | OK | Fixed-ball cover, inner-ball containment (strict) and exit displacement r/2 are correct. |
| BouRabeeGwynne.FiniteCellSelector | NOTE | Label/selector definitions correct under the disjointness hypotheses; `exists_cell_ball_choices` demands diameter bounds for every cell although only cells meeting K need them. |
| BouRabeeGwynne.WalkBrownianGoodEvent | OK | Success set = same active cell, or both terminated with endpoint distance ≤ a; mixed flags never succeed. |
| BouRabeeGwynne.WalkBrownianStep | OK | Row identities and one-step bad-mass bounds (active, terminated, initial) match the intended coupling; herror is a per-history hypothesis. |

Counts: OK = 14, NOTE = 6, ISSUE = 0. No proofs were reviewed; findings are about definitions and statements only.

Shared definitions used by this batch (checked, defined outside the batch):
- `continuousExitTime` (`StoppedCurveLaws.lean:67`): infimum over the exit set; ∞ when the path never leaves U (documented). Correct.
- `stoppedBrownianRepresentative` (`StoppedCurveLaws.lean:74`): z + ω(t·τ); ∞ exit totalized to constant z (documented, null set).
- `brownianNextExitTime` (`BrownianNextExit.lean:21`): τ + exit of the shifted path from z + ω(τ). Correct; ∞ propagates.
- `brownianSelectedNextExitTime` (`BrownianSelectedExit.lean:17`): `none ↦ τ` (time retained), `some j ↦` next exit from U j. This is what makes termination absorbing.
- `shiftedBrownianPath` (`BrownianWeakMarkov.lean:18`): s ↦ ω(t+s) − ω t. Correct.
- `frozenBrownianPath` (`BrownianPathFreezing.lean:19`): s ↦ ω(min s t). Correct stopped path.
- `IsStandardBrownianLaw` (`StoppedCurveLaws.lean:38`): probability measure, each coordinate Mathlib `IsBrownianReal` (zero start via Gaussian fdd laws, a.s. continuity), coordinates independent. Correct standard d-dimensional Brownian law.
- `brownianNaturalFiltration` (`BrownianExitStoppingTime.lean:17`): natural filtration of evaluations. Correct.
- `Euc` (`PaperObjects.lean:14`): `EuclideanSpace ℝ (Fin d)`. Correct.
- `ClockedWalkExcursion` (`ClockedWalkExcursion.lean:16-17`): ℕ × (ℕ → Euc d); `endPoint e = e.2 e.1`, `constant z = (0, const z)`. Consistent with the cell definitions.
- `discreteHarmonicMeasure` (`DiscreteHarmonicMeasure.lean:114`): exit-vertex law of the walk from v. Correct.
- `BoundaryAccessible` (`FiniteDirichlet.lean:18`): every v ∈ A reaches the complement of A by positive-conductance steps. Correct (guarantees exit).
- `balancedProduct` (`SubcouplingCompletion.lean:22`): `(α univ)⁻¹ • α.prod β`; mass-preserving when the masses agree (hypothesis of `balancedProduct_fst`, which holds for the residuals since both have mass Σᵢ min).
- `finitePartitionCoupling` (`FinitePartitionCoupling.lean:79`): `completeSubcoupling` of `finiteMatchedCoupling`. Marginals and bound are proved in the file.

Paper context: the Brownian ball-exit construction of the paper (`paper/rw-spheres.tex:1568-1579`: stopping times τ_k, nearest grid point to the current position, stop when the grid point leaves B_δ(U)) is the special case of `brownianSkeletonClock` with balls as domains, with `none` playing the role of "stop". `hnone : selector n x = none → x ∉ U` (`BrownianStoppedSkeleton`) is the formal counterpart of the stop rule. No batch statement is a printed-paper theorem; they are internal lemmas.

## BouRabeeGwynne.BrownianSkeletonClock
- `brownianClockChoice` (line 21): selects `selector (z + ω (state ω).2.toNNReal)` unless the flag is set. NOTE: when the time is ∞, `toNNReal = 0` and the selector is read at z; this only happens on {exit = ∞}, which is null by `standardBrownianLaw_ae_finiteSkeletonClock` (line 144). Harmless.
- `brownianClockUpdate` (line 25): flag := `(choice).isNone`, time := `brownianSelectedNextExitTime`. Termination is permanent (`brownianSkeletonClock_absorbed`, line 164). Matches the docstring.
- `brownianSkeletonClock` (line 32): index 0 is the exit time of U j₀ from z; step n+1 reads `selector (n+1)`, so `selector 0` is never read (harmless). Zero-length active excursions occur if z ∉ U j₀ (exit 0); the theorems do not assume z ∈ U j₀, and the walk side uses the same convention.
- `ClockRespectsFreezing` (line 66, private) and freezing lemmas (116, 124): proof infrastructure, statements correct.
- `isStoppingTime_brownianSkeletonClock` (line 132): correct stopping-time statement for the clock.
- `standardBrownianLaw_ae_finiteSkeletonClock` (line 144): a.s. finiteness of every stage; hypotheses (bounded open domains, standard law, d ≥ 1) jointly satisfiable.
- `brownianSkeletonClock_time_le_succ` (line 156): monotone clock; correct.

## BouRabeeGwynne.BrownianObservedHistory
- `measurable_brownianHistory_stopping_of_frozen` (line 15): payload measurable w.r.t. F_τ when frozen at τ. Standard and correct; hypothesis `hf` is the right "observed up to τ" criterion.
- `stoppedBrownianRepresentative_frozen_of_exit_le` (line 47): freezing after the exit leaves the stopped curve unchanged. Correct.
- `stoppedBrownianRepresentative_endPoint` (line 72): endpoint = z + ω(exit). Correct.
- `stoppedBrownianRepresentative_next_endPoint` (line 77): endpoint of the next excursion = z + ω(next exit) under finiteness. Correct.
- `stoppedBrownianNextRepresentative_frozen` (line 91): hypothesis `hτ` is the freezing identity that every stopping time of the clock satisfies (`brownianSelectedNextExitTime_frozen`). Correct.

## BouRabeeGwynne.BrownianExcursionSampler
- `selectedBrownianExcursionSampler` (line 23): `none ↦ (true, constant x)`, `some j ↦ (false, stopped representative of U j from x)`. Matches the docstring.
- `absorbingBrownianExcursionSampler` (line 87): if the flag is set, the selector is ignored (`if q.1 then none`); otherwise the selector is applied to the endpoint `c 1`. Matches the docstring "termination permanent, independently of later selectors".
- `selectedBrownianExcursionSampler_map` (line 65) and `absorbingBrownianExcursionSampler_map` (line 129): pushforwards equal the shared kernels. Correct.

## BouRabeeGwynne.BrownianSkeletonExcursion
- `brownianSkeletonExcursion` (line 18): index 0 is the first excursion from z in U j₀; index n+1 starts at z + ω(τₙ) using the path shifted at τₙ, with the selector applied to the same point (the choice in `brownianClockChoice`). Consistent with the clock.
- `measurable_brownianSkeletonExcursion` (line 28), `brownianSkeletonExcursion_flag` (line 49), `brownianSkeletonExcursion_endPoint` (line 61), `brownianSkeletonExcursion_frozen_of_le` (line 86), `measurable_brownianSkeletonExcursion_stopping` (line 123), `brownianSkeletonExcursion_eq_absorbingSampler` (line 133): the identities relate the excursions to the clock and to the absorbing sampler consistently. Correct.

## BouRabeeGwynne.BrownianSkeletonLaw
- `brownianSkeletonInitialLaw` (line 22): law of the first excursion from (some j₀, z). Correct.
- `brownianSkeletonKernel` (line 36): absorbing kernel with `selector (n+1)`, comapped to the last coordinate of the history. Correct.
- `standardBrownianLaw_skeleton_history_next` (line 71): one-step compProd identity. Proof-level; statement consistent.
- `standardBrownianLaw_skeleton_map` (line 127): the law of the full sequence of genuine excursions equals `Kernel.trajMeasure` of the initial law and the kernel. Premises (standard law, bounded open domains, measurable selectors, d ≥ 1) are jointly satisfiable; see Nonvacuity 1. The docstring claim ("exactly the genuine history-dependent trajectory law") matches the statement.

## BouRabeeGwynne.BrownianSkeletonPrefix
- `brownianSkeletonPhysicalKnots` (line 29): knots `Fin.cases 0 (clock i)` on Fin (n+2): 0, τ₀, …, τₙ, giving n+1 pieces. The pieces match excursions 0..n (`brownianSkeletonPhysicalKnots_chain_apply`, line 49). Uses the finiteness hypothesis, so no ∞ junk enters.
- `brownianSkeletonPhysicalKnots_duration` (line 43): duration = clock n's time. Correct.
- `brownianSkeleton_prefixChain_eq` (line 91), `brownianSkeleton_concatenate_eq_comp` (line 111), `brownianSkeleton_concatenatedCurve_eq_prefix` (line 126): exact recovery of the genuine prefix, including duration 0 (the docstring's "including duration zero" is covered by the case split in the proof). Correct.

## BouRabeeGwynne.BrownianUniformModulus
- `pathModulusEvent` (line 23): {ω | ∀ s,t ∈ [0,T], |s−t| ≤ 1/(n+1) → |ω s − ω t| ≤ ε}. This is the correct closed modulus event; the complement is "oscillation > ε on a mesh-1/(n+1) interval".
- `isClosed_pathModulusEvent` (line 27), `monotone_pathModulusEvent` (line 35), `iUnion_pathModulusEvent` (line 42): correct (uniform continuity on compact [0,T]).
- `measure_compl_pathModulusEvent_tendsto_zero` (line 59): for every finite μ, μ(modulus event)ᶜ → 0 as n → ∞. Correct and not vacuous.
- NOTE (docstring): the header says "Translation of the path by its initial position leaves these events unchanged" and the theorem docstring says "This applies uniformly to all translated starts". The file neither states nor proves translation invariance or any uniformity over starts. The statement is for an arbitrary finite μ, so translated laws are covered implicitly, but the uniform-over-starts claim is not formalized here.

## BouRabeeGwynne.BrownianSkeletonTail
- `pathModulusEvent_forces_short_step` (line 23): on the modulus event, K moves of size ≥ ε inside [0,T] with K/(m+1) > T is impossible. The mathematics is correct.
- `ballSkeletonCountEvent` (line 61): ∃ monotone τ with τ_K ≤ exit time and ∀ k<K, ε ≤ |ω τₖ − ω τₖ₊₁|. Matches the docstring "K successive ε-moves before actual exit".
- `ballSkeletonCountEvent_subset` (line 67): inclusion in {T < exit} ∪ modulus-complement. Correct.
- `standardBrownianLaw_uniform_skeletonTail` (line 86): ∃ K ∀ z ∈ U, μ(event) ≤ η. The quantifier order is the uniform one the docstring describes; the bound is for bounded U, so the statement is not vacuous.

## BouRabeeGwynne.BrownianNestedExit
- `continuousExitTime_mono` (line 14): U ⊆ V ⇒ exit U ≤ exit V, including ∞. Correct.
- `brownianNextExitTime_eq_of_le` (line 21): if τ ≤ exit V, the next V-exit equals the V-exit (both the finite and the ∞ branch). Correct.
- `brownianNextExitTime_from_nested_exit` (line 35): next V-exit after the U-exit equals the V-exit. Correct.

## BouRabeeGwynne.BrownianActiveSkeletonTail
- `brownianSkeletonClock_le_ambient_exit` (line 18): clock ≤ exit of the ambient V. Correct.
- `brownianSkeletonClock_flag_monotone` (line 40), `brownianSkeletonClock_active_of_le` (line 49): flags are monotone (false → true); active at n ⇒ active at m ≤ n. Correct.
- `brownianSkeletonClock_active_step_dist` (line 62): under the margin hypothesis (ball of radius ε about the selected point inside U j), an active step moves the clock point by ≥ ε. Correct.
- `standardBrownianLaw_uniform_activeSkeletonTail` (line 106): ∃ K, independent of U, z, j₀, selector (only V, ε, η, μ), ∀ admissible data μ{flag false at K} ≤ η. The margin hypothesis is satisfiable (Nonvacuity 2). The docstring's "independent of all fine continuity-cell partitions" matches.

## BouRabeeGwynne.BrownianStoppedSkeleton
- `brownianSkeletonClock_exit_le_of_stopped` (line 20): if the skeleton has stopped at stage n, the target exit happened by the clock time. Uses `hnone` (none ⇒ endpoint ∉ U). Correct.
- `brownianSkeleton_stopped_concatenate` (line 48): the reconstructed continuously stopped curve equals the stopped Brownian curve when the target exit ≤ the clock. Correct, including duration 0.
- `reconstructedBrownianStoppedCurve` (line 83): unitCurveExitProjection of the concatenated prefix. Correct definition.
- `levyProkhorov_stoppedBrownian_reconstruction_le` (line 98): LP(stopped law, reconstructed skeleton law) ≤ r, given μ(not stopped by n) ≤ r. Matches the docstring; not vacuous. Premises are satisfiable in principle (not compiled; needs a concrete selector and partition). The paper's "stop when the grid point leaves B_δ(U)" corresponds to `hnone`.

## BouRabeeGwynne.FinitePartitionCouplingKernel
- `weightedKernel`, `cappedCellKernel`, `matchedCellKernel`, `finiteMatchedKernel`, `residualKernel` (lines 22, 31, 60, 73, 98; private): measurable kernel constructions. Junk: `cappedCellKernel` divides by `κ a E`, which is 0 only when the weight is 0 (`min ≤ κ a E`, so `x/0` multiplies a zero measure). Harmless.
- `balancedProductKernel` (line 48): `(κ a univ)⁻¹ • (κ ×ₖ ν) a`. Junk: `(0)⁻¹ = ⊤` at zero mass, but then the measure is 0 and `⊤ • 0 = 0`. NOTE, harmless.
- `finitePartitionCouplingKernel` (line 116) and `finitePartitionCouplingKernel_apply` (line 134): pointwise equal to `finitePartitionCoupling`. Correct.
- `finitePartitionCouplingKernel_isMarkov` (line 147): Markov. Correct.
- `finitePartitionCouplingKernel_spec` (line 159): exact marginals κ a and ν a, and the bad-set bound `≤ 1 − Σᵢ min(κ(Eᵢ), ν(Fᵢ))` (truncated subtraction is intended here). Matches the docstring.

## BouRabeeGwynne.FiniteCellCouplingError
- `coupling_bad_zero_of_dirac_marginals` (line 18): if both marginals are Dirac at the absorbing states, the coupling is concentrated there. Correct.
- `commonCellDeficit_le` (line 41): `1 − Σ min(aᵢ,bᵢ) ≤ card·ε` under Σ b = 1 and |aᵢ−bᵢ| ≤ ε. Correct; the ENNReal truncated subtraction is harmless because the statement is an upper bound.
- `finitePartitionCoupling_bad_le_of_cell_error` (line 70): hcover `ν(⋃ F) = 1` makes Σ ν(Fᵢ) = 1 (uses disjointness). Correct, with the right side being the Brownian/second marginal.

## BouRabeeGwynne.SkeletonCoupling
- `next_event_le` (line 21), `goodHistory` (line 47), `badUpTo` (line 56), `measurableSet_*` (lines 50, 59), `prefix_good_iff` (line 69), `initial_event_eq` (line 77): correct definitions and helper statements.
- `badUpTo_le` (line 97): P(∃ i ≤ k, failure) ≤ μ(B₀) + Σᵢ<k εᵢ, with the one-step hypothesis only on good histories. Matches the docstring ("required only on histories with no earlier failure"). Correct.
- `jointPathLaw` (line 143): Kernel.trajMeasure on pairs, pushed to a pair of paths (Ionescu–Tulcea). Correct; `jointPathLaw_fst`/`_snd` (lines 150, 158) identify the marginals with `trajMeasure`. Correct.
- `jointPathLaw_bad_le` (line 167): simultaneous bad-event bound. Correct.

## BouRabeeGwynne.WalkBrownianCoupling
- `activeEndpointCell` (line 24): {flag = false ∧ endpoint ∈ E}. Terminated states are excluded from matching, as the docstring says. Correct.
- `measurableSet_activeEndpointCell` (line 27), `pairwiseDisjoint_activeEndpointCell` (line 32): correct.
- `brownianSelectorForWalk` (line 41): `n ↦ select (n−1)`. NOTE: at n = 0 it returns `select 0`; the Brownian clock never reads index 0 (step n+1 reads `selector (n+1)`), so this is harmless junk. `brownianSelectorForWalk_succ` (line 44) is the one that matters and is correct.
- `walkEndpointCell` (line 51): active cell intersected with `range pos`, so off-graph walk states never count as success. Correct; `measurableSet_walkEndpointCell` (line 55) and `pairwiseDisjoint_walkEndpointCell` (line 60) are correct.
- `walkBrownianCouplingKernel` (line 79): cells E(n+1) on both sides, walk history kernel comapped by `prefixMap Prod.fst`, Brownian kernel by `prefixMap Prod.snd`. Index alignment is correct (walk step n uses `select n`, Brownian uses `selector (n+1) = select n`).
- `walkBrownianCouplingKernel_marginals` (line 102), `walkBrownianInitialCoupling` (line 111), `walkBrownianInitialCoupling_isProbability` (line 119), `walkBrownianInitialCoupling_marginals` (line 128): exact marginals. Correct.
- `walkBrownianJointLaw` (line 141): `SkeletonCoupling.jointPathLaw` of the kernel. Correct.
- `walkBrownianJointLaw_marginals` (line 150): the walk marginal is the pushforward of the trajectory law of the walk, and the Brownian marginal is the pushforward of μ by the skeleton excursion map. Correct. NOTE: no hypothesis links the Brownian start z with `pos v`; the marginals hold for any z. Downstream (`WalkBrownianActiveTransfer`, `ActualStoppedLawComparison`) impose `dist (pos v) z ≤ a`, so the bundle is used correctly.

## BouRabeeGwynne.WalkBrownianCellMeasures
- `activeEndpointCell_map_false` (line 16): (ν.map (false,·))(activeEndpointCell endpoint E) = (ν.map endpoint)(E). Correct.
- `brownian_activeEndpointCell_mass` (line 27): cell mass equals the stopped-law endpoint mass. Correct.
- `brownian_activeEndpointCells_cover` (line 39): the cells cover the active Brownian endpoints a.s. when closure U ⊆ ⋃Eᵢ and z ∈ U (exit endpoint lies in closure U). Correct.
- `walkEndpointCell_mass` (line 65): equals the discrete harmonic measure pushed by pos. Correct.
- `finite_walkBrownian_excursion_bad_le` (line 85): bad mass ≤ ofReal b, given per-cell errors ≤ b/(m+1). NOTE: (i) for m = 0 the hypotheses are contradictory (hcover with z ∈ U forces closure U ⊆ ∅), so the lemma is vacuous there; harmless since m ≥ 1 is used. (ii) Both sides are probability masses, so herror holds automatically when b ≥ m+1; the content is only for b < m+1. Neither is a defect.

## BouRabeeGwynne.FixedBallCover
- `exists_fixed_ball_cover` (line 20): compact K inside open W gives r ∈ (0, rmax] and a finite family of centers in K covering K by balls of radius r/4 with closedBall c r ⊆ W. Correct; non-vacuous (K = closedBall 0 1, W = ball 0 2). The docstring's "arbitrarily small" is the rmax bound.
- `exists_inner_ball_for_cell` (line 45): a cell meeting K with diameter ≤ r/4 lies in ball c (r/2) (strict). Correct.
- `near_cover_point_mem_inner_ball` (line 60): correct.
- `inner_ball_exit_displacement` (line 70): x ∈ closedBall c (r/2), y ∉ ball c r ⇒ r/2 ≤ dist x y. Correct; this is the margin used later.

## BouRabeeGwynne.FiniteCellSelector
- `cellLabel` (line 17): `some (choose)` if x lies in some cell, else `none`. Correct under disjointness; with overlapping cells the choice is arbitrary, but every lemma carries `Pairwise Disjoint`. `cellLabel_eq_none_iff` (line 20), `cellLabel_some_mem` (line 28), `cellLabel_eq_some_iff` (line 37): correct.
- `measurable_cellLabel` (line 47): measurable for countable labels with disjoint measurable cells. Correct.
- `cellSelector` (line 74): `(cellLabel E x).bind select`, so points outside every cell stop. Correct. `measurable_cellSelector` (line 77) and `cellSelector_some_mem` (line 90): correct.
- `exists_cell_ball_choices` (line 103): fixed balls of radius r/2 around centers from a fixed family; `select i = none ↔ E i ∩ K = ∅`; `select i = some c → E i ⊆ ball c (r/2)`. Correct. NOTE: the hypothesis `hdiam : ∀ i, ...` (line 106) asks for diameter ≤ r/4 for every cell, though only the cells meeting K are used. The lemma therefore excludes partitions with a large or unbounded cell outside K. Strengthening is not a falsity, but it is not the minimal hypothesis.
- NOTE (wording): the module header says "a point outside every bounded cell receives `none`", but the definition gives `none` for any point outside all cells, and cells need not be bounded.

## BouRabeeGwynne.WalkBrownianGoodEvent
- `goodExcursionPair` (line 20): success = (both active, same cell E i, walk endpoint in range pos) ∨ (both terminated, walk endpoint in range pos, endpoint distance ≤ a). Mixed flags never succeed. Matches the docstring.
- `measurableSet_goodExcursionPair` (line 28), `goodExcursionPair_dist_le` (line 46), `goodExcursionPair_walk_in_range` (line 54), `goodExcursionPair_flags` (line 61), `goodExcursionPair_active_cell` (line 67), `goodExcursionPair_same_selector` (line 76), `goodExcursionPair_compl_disjoint_cell` (line 85): correct.
- `coupling_bad_goodExcursionPair_constants_zero` (line 93): both Dirac constant marginals at distance ≤ a ⇒ zero bad mass. Correct.

## BouRabeeGwynne.WalkBrownianStep
- `walkSkeletonHistoryKernel_active_row` (line 23), `walkSkeletonHistoryKernel_constant_row` (line 39): walk-side transition rows (active: the clocked excursion from v with flag false; stopped: Dirac at the constant state). Correct.
- `brownianSkeletonKernel_active_row` (line 61), `brownianSkeletonKernel_constant_row` (line 77): Brownian-side rows, same convention. Correct.
- `walkBrownianCouplingKernel_apply` (line 102): the coupling kernel is the finite partition coupling of the two rows (both histories comapped). Correct.
- `walkBrownianCouplingKernel_active_bad_le` (line 115): under active flags, the same selected j, the cover hypothesis and the per-cell herror, the next-step bad mass is ≤ ofReal b. Consistent with the docstring. herror is a per-history hypothesis and is automatically true when b ≥ m+1. Correct.
- `walkBrownianCouplingKernel_constant_bad_zero` (line 140): both rows constant and the endpoints within a ⇒ zero bad mass. Matches the docstring ("also applies when the current active pair both select termination now").
- `walkBrownianInitialCoupling_bad_le` (line 159): the initial coupling bad mass ≤ ofReal b under the start-point cover. Correct.

## Nonvacuity examples
Scratch file: `Nonvacuity.lean`. Compiled with `lake env lean …/Nonvacuity.lean` from the repository root. Exit 0, no output, no warnings, no `sorry`. Output saved in `nonvacuity.out` (empty).

Compiled file body (the file text from the imports onward; only its module docstring is omitted):

```lean
import BouRabeeGwynne.BrownianSkeletonLaw
import BouRabeeGwynne.BrownianActiveSkeletonTail
import BouRabeeGwynne.EuclideanWienerLaw

open MeasureTheory ProbabilityTheory Set Metric
open scoped NNReal ENNReal unitInterval

namespace BouRabeeGwynne

instance nvOptionUnitMeasurableSpace : MeasurableSpace (Option Unit) := ⊤

instance nvOptionUnitMeasurableSingleton :
    MeasurableSingletonClass (Option Unit) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

-- The standard Wiener law on `ℝ¹` is a probability measure.
instance nvWienerIsProbability : IsProbabilityMeasure (euclideanWienerLaw 1) :=
  (isStandardBrownianLaw_euclideanWienerLaw 1).1

/-- Select the unique domain `()` near the origin, and stop elsewhere. -/
noncomputable def nvSelector : ℕ → Euc 1 → Option Unit :=
  fun _ x => if ‖x‖ < 3 / 2 then some () else none

lemma nvSelector_measurable (n : ℕ) : Measurable (nvSelector n) :=
  Measurable.ite (measurableSet_lt measurable_norm measurable_const)
    measurable_const measurable_const

/-- The single domain: the open ball of radius `2` about the origin. -/
noncomputable def nvDomain : Unit → Set (Euc 1) := fun _ => ball (0 : Euc 1) 2

lemma nvDomain_open : ∀ j, IsOpen (nvDomain j) := fun _ => isOpen_ball

lemma nvDomain_bounded : ∀ j, Bornology.IsBounded (nvDomain j) :=
  fun _ => isBounded_ball

-- Premises of `standardBrownianLaw_skeleton_map` are satisfied, so its
-- conclusion (equality of the full excursion-sequence law with the Markov
-- trajectory law) is a genuine, non-vacuous statement for this data.
example : (euclideanWienerLaw 1).map
      (fun ω k => brownianSkeletonExcursion nvDomain (0 : Euc 1) () nvSelector k ω) =
    Kernel.trajMeasure (X := fun _ => Bool × C(unitInterval, Euc 1))
      (brownianSkeletonInitialLaw nvDomain nvDomain_open (euclideanWienerLaw 1) 0 ())
      (brownianSkeletonKernel nvDomain nvDomain_open (euclideanWienerLaw 1)
        nvSelector nvSelector_measurable) :=
  standardBrownianLaw_skeleton_map le_rfl (isStandardBrownianLaw_euclideanWienerLaw 1)
    nvDomain nvDomain_open nvDomain_bounded 0 () nvSelector nvSelector_measurable

-- The margin hypothesis of `standardBrownianLaw_uniform_activeSkeletonTail`
-- holds for `nvSelector` with `ε = 1/2` and ambient `V = ball 0 2`, so the
-- uniform active-tail bound applies to a concrete configuration.
example : ∃ K : ℕ, (euclideanWienerLaw 1)
    {ω | (brownianSkeletonClock nvDomain (0 : Euc 1) () nvSelector K ω).1 = false} ≤
      ENNReal.ofReal (1 / 2) := by
  obtain ⟨K, hK⟩ := standardBrownianLaw_uniform_activeSkeletonTail (d := 1) (J := Unit) le_rfl
    (isStandardBrownianLaw_euclideanWienerLaw 1) (V := ball (0 : Euc 1) 2)
    isBounded_ball (ε := 1 / 2) (η := 1 / 2) (by norm_num) (by norm_num)
  refine ⟨K, hK nvDomain nvDomain_open (fun _ => subset_rfl) 0
    (mem_ball_self (by norm_num)) () nvSelector nvSelector_measurable ?_⟩
  intro n x j hx y hy
  unfold nvSelector at hx
  split_ifs at hx with h
  · have h1 : dist y x < 1 / 2 := hy
    have h2 : dist x 0 < 3 / 2 := by rw [dist_zero_right]; exact h
    have h3 := dist_triangle y x (0 : Euc 1)
    show dist y 0 < 2
    linarith
```

What the examples show:
1. **Nonvacuity 1** (`standardBrownianLaw_skeleton_map`): the Wiener law `euclideanWienerLaw 1` is a standard Brownian law (cited `isStandardBrownianLaw_euclideanWienerLaw`). With the open bounded domain `nvDomain = ball 0 2` (one domain, `J = Unit`) and the measurable selector `nvSelector`, all premises of the theorem hold. Its conclusion, the equality of the full excursion-sequence law with the trajectory law, is therefore a real statement about these concrete data, not an implication with unsatisfiable premises.
2. **Nonvacuity 2** (`standardBrownianLaw_uniform_activeSkeletonTail`): the margin hypothesis `∀ n x j, selector n x = some j → ball x ε ⊆ U j` is satisfiable with ε = 1/2, V = ball 0 2, U = ball 0 2, by a selector that picks the domain only on ‖x‖ < 3/2 (the proof of the margin is the triangle inequality). The uniform theorem applies and gives a concrete bound μ{flag false at K} ≤ 1/2 for some K. This shows the active-tail hypotheses are jointly satisfiable and that the margin bundle is not vacuous.

Not attempted (time budget): the walk-side bundles (`walkBrownianCouplingKernel_active_bad_le`, `finite_walkBrownian_excursion_bad_le`, `walkBrownianJointLaw_marginals`, `levyProkhorov_stoppedBrownian_reconstruction_le`). Each needs a concrete `FiniteConductanceNetwork` with boundary accessibility and a quantitative harmonic-measure approximation (herror), so a nonvacuity witness would take much longer than the budget. Their herror hypotheses are automatically satisfied when b ≥ m+1 (both sides are probability masses, so |difference| ≤ 1), which shows only that the bundle is not contradictory; it does not show the small-b regime is satisfiable.
