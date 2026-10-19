# Audit batch 12
| Module | Verdict | Summary |
|---|---|---|
| BouRabeeGwynne.CouplingErrorBudget | NOTE | Arithmetic budget lemmas are correct; `hr : 0 < r` in `exists_coupling_stopped_error_budget` is unused (harmless). |
| BouRabeeGwynne.CouplingNeighborhoods | OK | Finite r/4-cover of the δ-thickening inside a compact Q with balls inside W, as intended; satisfiable. |
| BouRabeeGwynne.CouplingPartitions | NOTE | Index-`⊤` σ-algebra is the discrete one (finite `centers`); docstring "selectors are total" holds only on `C` (statement: `∀ x ∈ C, select i x ≠ none`). |
| BouRabeeGwynne.NearestCouplingStarts | OK | Eventual nearest-start approximation in the fixed inner ball, uniform in the start; matches docstring. |
| BouRabeeGwynne.StandardBrownianProbabilityMeasure | OK | Bundles `euclideanWienerLaw` as a `ProbabilityMeasure` that is a standard Brownian law; nonvacuous (compiled). |
| BouRabeeGwynne.TheoremACouplingSetup | NOTE | Bounds hold for all `z ∈ U` and all `j₀` (no `z ∈ ball j₀` hypothesis): stronger than the one use; `μ.map` is of a measurable map, so no junk 0. |
| BouRabeeGwynne.TheoremAProcessLaws | OK | Standard BM with a.s. finite exit and probability stopped laws; `IsStoppedTilingWalkLaw` pins the walk law (no junk satisfier). |
| BouRabeeGwynne.TheoremAStatement | NOTE | Matches paper Thm A (lines 259–277) except the ambient collar `closure U ⊆ interior D` (strictly stronger hypothesis; README correction 1 gives the counterexample refuting the printed `closure U ⊆ D`). |
| BouRabeeGwynne.WalkEdgeSupport | OK | Step bound `2·mesh.toReal` is guarded by `mesh ≠ ∞`; positive-conductance step lemma correct. |
| BouRabeeGwynne.TilingStoppedLawComparison | NOTE | `innerDomain U ε` is `∅` (not `univ`) when `Uᶜ = ∅` (Mathlib `infDist _ ∅ = 0`); harmless since every use has bounded `U`. |
| BouRabeeGwynne.UniformStoppedWalkConvergence | OK | Final uniform Lévy–Prokhorov estimate over every ν satisfying `IsStoppedTilingWalkLaw`; matches Thm A's uniform-in-z claim. |
| BouRabeeGwynne.TheoremAProved | OK | `theoremA_proved : TheoremAStatement`; axioms are only `propext`, `Classical.choice`, `Quot.sound`; premises jointly satisfiable (compiled instance). |
| BouRabeeGwynne.Upstream.BrownianMotion.Auxiliary.Algebra | OK | Generic monotonicity and finrank lemmas; side conditions (`0 ≤ c`, `c ≠ 0`, `Nontrivial`) present. |
| BouRabeeGwynne.Upstream.BrownianMotion.Auxiliary.DenseCountable | NOTE | `denseCountable` is an `Exists.choose` countable dense set; only density and countability are used. |
| BouRabeeGwynne.Upstream.BrownianMotion.Auxiliary.ENNReal | OK | Statements hold at the `0`/`⊤` junk points; side conditions (`p ≠ ⊤`, `0 < x`) present. |
| BouRabeeGwynne.Upstream.BrownianMotion.Auxiliary.FiniteInf | OK | Every `max'`/`min'`/`⨆`/`⨅` lemma that fails on `∅` carries nonemptiness. |
| BouRabeeGwynne.Upstream.BrownianMotion.Auxiliary.MeanInequalities | OK | Jensen/Hölder and Minkowski bounds, ENNReal corners (`μ univ = ⊤`, `∫f^r = 0`) checked. |
| BouRabeeGwynne.Upstream.BrownianMotion.Auxiliary.MeasureTheory | NOTE | Junk-0 conventions for `condExp` and variance are harmless (statements stay true); `measure_closeBall_const` has a typo in two names. |
| BouRabeeGwynne.Upstream.BrownianMotion.Auxiliary.Metric | OK | `IsSeparated` is strict in Mathlib, so `disjoint_closedBall` is correct, including `ε = ⊤`. |
| BouRabeeGwynne.Upstream.BrownianMotion.Auxiliary.Nat | OK | Single lemma `pow_two_mul_abs`, true for all `n`; file name is misleading. |
| BouRabeeGwynne.Upstream.BrownianMotion.Auxiliary.Topology | OK | Hölder lemmas carry the needed side conditions (`0 < r`, bounded space, bounded set). |
| BouRabeeGwynne.Upstream.BrownianMotion.Continuity.Chaining | NOTE | Junk branches of `nearestPt` and the truncated `k - (n+1)` index are never reached by the lemmas that use them. |
| BouRabeeGwynne.Upstream.BrownianMotion.Continuity.CoveringNumber | NOTE | Uses Mathlib's `coveringNumber`; `EMetric.isCover_iff_subset_iUnion_closedBall` is misnamed (it is about `closedEBall`); the ε ≤ 1 bound needs `ε ≤ 1`. |
| BouRabeeGwynne.Upstream.BrownianMotion.Continuity.HasBoundedInternalCoveringNumber | NOTE | `HasBoundedCoveringNumber` quantifies over `ε ∈ ℝ≥0` including `0` (docstring says `(0, diam]`); the extra clause is stronger only for finite sets with `d ≤ 0`. |
| BouRabeeGwynne.Upstream.BrownianMotion.Continuity.IsKolmogorovProcess | NOTE | Only `Cp` is defined here (a max of two positive constants for `d < q`, `⊤` otherwise); the Kolmogorov notions are Mathlib's, and the estimates are conservative. |

## BouRabeeGwynne.CouplingErrorBudget
- `coupling_step_error_budget` (line 17): per-step budget `(η/100)/(K+1)` with `(K+1)·budget = η/100` in ℝ≥0∞; matches its statement and is satisfiable.
- `exists_coupling_stopped_error_budget` (line 30): explicit witness `q = η/3` satisfies the five ℝ≥0∞ inequalities; `hr : 0 < r` (line 31) is never used. NOTE only.

## BouRabeeGwynne.CouplingNeighborhoods
- `exists_coupling_neighborhoods` (line 73): the output gives `0 < r ≤ δ/100`, open bounded `W` and compact `Q` with `HasAmbientCollar W D`, `cthickening δ U ⊆ Q`, centers inside `cthickening δ U`, an r/4-cover of `cthickening δ U`, and `closedBall c r ⊆ W`, `closure (ball c r) ⊆ Q`. This is the intended finite-cover data; the hypotheses are satisfied by any bounded `U` with `closure U ⊆ interior D` (e.g. `ball 0 1` in `ball 0 2`).

## BouRabeeGwynne.CouplingPartitions
- `local instance (Option X) := ⊤` (line 17): correct here because every use has `Option ↥centers` with `centers : Finset`, so `⊤` is the discrete σ-algebra and `Measurable (select i)` means each fibre is Borel.
- `exists_eventual_walkBrownian_coupling_partitions` (line 22): the coupling failure bound `(K+1) · ofReal b` is a union bound over the `K+1` excursion pairs and is uniform in the initial centre and the nearby starts; the `∀ᶠ n` index is shared by both starts. Hypotheses are outputs of earlier lemmas and are jointly satisfiable.
- NOTE: the docstring "Selectors are total" is stronger than line 39: totality is required only on `C`, `∀ i, ∀ x ∈ C, select i x ≠ none`. The conclusion is still what the docstring means for the active region.

## BouRabeeGwynne.NearestCouplingStarts
- `NearestVertexData.eventually_nearest_coupling_starts` (line 148): for `n` large, every `z ∈ U` has a vertex `v = N.vertex n z` in `closedVertices W` with `pos v ∈ closedBall j (r/2)`, `z ∈ closedBall j (r/2)`, and `dist (pos v) z ≤ δ`, where `j` is a centre covering `z`. This matches the docstring; `hcover` (line 152) only needs to cover `U`.

## BouRabeeGwynne.StandardBrownianProbabilityMeasure
- `standardBrownianProbabilityMeasure` (line 28) is `⟨euclideanWienerLaw d, inferInstance⟩`, a `ProbabilityMeasure`; `isStandardBrownianLaw_standardBrownianProbabilityMeasure` (line 37) and `exists_standardBrownianProbabilityMeasure` (line 47) are the existence statements. They match the docstrings.
- `IsStandardBrownianLaw` (StoppedCurveLaws.lean:38) is a probability measure, each coordinate `IsBrownianReal` (Mathlib: pre-Brownian finite-dimensional laws plus a.s. continuous paths, `Mathlib/Probability/BrownianMotion/Basic.lean:303`), and the coordinate processes are independent; this is the standard d-dimensional zero-start Brownian motion. Nonvacuous: see the Nonvacuity section.

## BouRabeeGwynne.TheoremACouplingSetup
- `exists_theoremA_coupling_setup` (line 70): the clock bound `μ{clock = false} ≤ η/100` says the skeleton has been absorbed after `K` steps (`brownianSkeletonClock`, `BrownianSkeletonClock.lean:32`) with high probability, which is the intended tail bound. The excursion bound `μ.map (…) {γ | pasted ∈ unitCurveExitOscillationBad …} ≤ 2η/100` uses a map that is measurable (`measurable_brownianSkeletonExcursion`; `hΓ` in UniformStoppedWalkConvergence line 66), so `Measure.map` does not collapse to the junk value 0.
- NOTE: the statement is `∀ z ∈ U, ∀ j₀`, with no `z ∈ ball j₀ (r/2)` hypothesis. It is stronger than the one application (which has that closeness), so it is not a weakening.
- The selector quantifier `∀ selector` is satisfiable on paper: the cover at line 80 gives r/4-balls covering `cthickening δ U`, so the nearest-centre selector meets the margin and `none`-conditions. I did not exhibit a measurable selector formally (time budget), so this bundle is argued, not compiled.

## BouRabeeGwynne.TheoremAProcessLaws
- `exists_standardBrownianLaw_with_stopped_laws` (line 19): gives a standard Brownian `μ` such that for `z ∈ U`, `stoppedBrownianCurve` is AE-measurable, the first exit `continuousExitTime U z` is a.s. finite (the only junk, `⨅ ∅ = ⊤`, is excluded a.s.), and the stopped law is a probability measure. This matches the paper's stopped Brownian motion (paper lines 259–277, conclusion of Thm A).
- `NearestVertexData.exists_eventually_stoppedWalkLaws` (line 35): `∃ walkLaw`, eventually `IsStoppedTilingWalkLaw` for every `z : Euc d` (stronger than `z ∈ U`). `IsStoppedTilingWalkLaw` (StoppedCurveLaws.lean:100) requires `μ = law.map curve` for the trajectory law of the finite conductance network on `R = closedVertices U ∪ {v₀}`, with positive conductance on the interior, a.s. finite exit, and an AE-measurable curve. So it pins down one measure rather than being satisfied by arbitrary measures.

## BouRabeeGwynne.TheoremAStatement
- `TheoremAStatement` (line 107) against paper Thm A (`paper/rw-spheres.tex` lines 259–277):
  - bounded Lipschitz domain: `IsLipschitzDomain U` (`IsDomain` plus `HasLipschitzBoundary`, LipschitzDomain.lean:35) together with `Bornology.IsBounded U`; matches.
  - orthogonal tilings of `D`: `TilingSequence` with `OrthogonalTiling` (PaperObjects.lean:173, 194); matches.
  - nearest vertex with any minimiser (paper: lexicographic tie-break): `NearestVertexData` (Approximation.lean:16); this is a generalisation of the paper's convention, so not a weakening.
  - (1.3), `lim (ε_n + sup_z ‖z^n − z‖) = 0`: `ApproximationCondition` (Approximation.lean:40) is `mesh + uniformError → 0` in ℝ≥0∞, with `mesh = sup diamENN` (PaperObjects.lean:157) and `uniformError` a sup over `G.domain`; matches paper line 263.
  - (I)–(III): `PaperRegularity = RegularityI ∨ RegularityII ∨ RegularityIII` (PaperObjects.lean:200–224); matches paper lines 268–272.
  - conclusion: uniform Lévy–Prokhorov convergence of stopped walk laws to stopped Brownian laws, with the metric on `CurveSpace` the Fréchet infimum over increasing homeomorphisms (`CurveSpace.lean:44–52`), which is paper eq. (cmp-topology) at line 251.
- DIFFERENCE (NOTE): `HasAmbientCollar U D` is `closure U ⊆ interior D` (PaperObjects.lean:21), whereas the paper assumes `closure U ⊆ D` (line 260). This is the correction in README "Corrections" item 1, with a counterexample to the printed statement (square grid on `[0,1]×[0,2]`, `U = (0,1)×(1/2,3/2)`). The Lean statement is therefore strictly weaker than the printed claim, and the printed claim is false.
- NOTE (context): `RegularityII` uses `mesh.toReal` and `minTileVolume.toReal` (PaperObjects.lean:210, 213); these take the junk value 0 at `⊤`. Under `ApproximationCondition` (which forces `mesh → 0`, so `mesh < ⊤` eventually) they cannot change the meaning. `RegularityIII` takes a max over an empty set as `0` for isolated cells, which only excludes degenerate single-cell tilings.
- Nonvacuity: `theoremA_instance` (Nonvacuity section) instantiates the premises for `U = ball 0 1` with the lattice tiling guard.

## BouRabeeGwynne.TheoremAProved
- `theoremA_proved : TheoremAStatement` (line 141) is the proof of that statement. `#print axioms` gives only `propext`, `Classical.choice`, `Quot.sound`, so there is no `sorryAx` in the proof term.
- Verdict OK. The statement is the one the README describes, subject to the NOTE under TheoremAStatement.

## BouRabeeGwynne.WalkEdgeSupport
- `FiniteConductanceNetwork.stepPMF_ae_edge_or_constant` (line 20) and `trajectoryLaw_ae_edge_or_constant` (line 38): almost surely each step either moves along a positive-conductance edge or stays put. This is the right dichotomy for the stopped walk.
- `OrthogonalTiling.trajectoryLaw_ae_step_dist_le_two_mesh` (line 54): the bound `dist ≤ 2·mesh.toReal` uses the `toReal` of `mesh`, which is the junk value 0 at `⊤`, but the hypothesis `hmesh : T.mesh ≠ ∞` (line 57) rules that out. OK.

## BouRabeeGwynne.TilingStoppedLawComparison
- `OrthogonalTiling.levyProkhorov_actual_tiling_stopped_laws_le` (line 86) is a budget-splitting lemma. Its hypotheses `hfailure`, `htail`, `hosc` and the budgets are the outputs of the coupling lemmas, and `hbuffer`, `hpoint`, `hsmall` are jointly satisfiable (shrink `ε` and `a`).
- NOTE: `innerDomain U ε := {x | ε < infDist x Uᶜ}` (BrownianInnerExit.lean:15). When `Uᶜ = ∅`, Mathlib's `infDist _ ∅ = 0`, so `innerDomain univ ε = ∅` rather than `univ`. The lemma takes any open `U` (line 108), so the junk is reachable through the hypothesis `hosc`; its callers in `BouRabeeGwynne` and in the `SpherePackings/Support/Section4` adaptation (both `UniformStoppedWalkConvergence`, which take `hUb`) have bounded `U`, so it cannot matter.
- `T.mesh.toReal` (lines 109, 113) is guarded by `hmesh` (line 93).

## BouRabeeGwynne.UniformStoppedWalkConvergence
- `NearestVertexData.eventually_stoppedWalkLaw_levyProkhorov_le` (line 22): `∀ᶠ n, ∀ z ∈ U, ∀ ν, IsStoppedTilingWalkLaw … ν → LP(ν, stoppedBrownianLaw U z μ) ≤ ofReal η`. Quantifying over all `ν` with the defining property is the right form, and that property pins `ν` (see TheoremAProcessLaws). The `∀ᶠ n` index is shared across `z ∈ U`, which gives the uniformity claimed in Thm A.
- Hypotheses (`hL : HasLipschitzBoundary U`, `hU`, `hμ`, `hη`, `happrox`, `hreg`) are jointly satisfiable (Nonvacuity section).
- Verdict OK.

## Upstream
Read with the same criteria; summarised here. Spot-checked against source: `denseCountable` (DenseCountable.lean:27) is `Exists.choose`; `Cp` (IsKolmogorovProcess.lean:543) is a max of two terms; `HasBoundedCoveringNumber` (HasBoundedInternalCoveringNumber.lean:34–36) quantifies `ε : ℝ≥0` with `ε ≤ ediam A`, so `ε = 0` is included, as stated. The Kolmogorov notions and covering numbers are Mathlib's (`IsKolmogorovProcess`, `IsAEKolmogorovProcess`, `coveringNumber`, `IsCover`, `IsSeparated`), not defined in these files. None of the 13 files defines Brownian motion or a Kolmogorov extension.

## BouRabeeGwynne.Upstream.BrownianMotion.Auxiliary.Algebra — OK
- `Monotone.finset_sum` (line 20), `Monotone.const_smul_of_nonneg` (26, needs `0 ≤ c`), `div_left_injective₀` (31, needs `c ≠ 0`): no `x/0 = 0` trap.
- `Module.finrank_ne_zero` (40) requires `Nontrivial M`, so the junk `finrank = 0` of a trivial module cannot matter. Trailing `open Finset` (45) is cosmetic.

## BouRabeeGwynne.Upstream.BrownianMotion.Auxiliary.DenseCountable — NOTE
- `denseCountable` (line 27) is `Exists.choose` of `exists_countable_dense`: an arbitrary countable dense set (empty if `T` is empty), matching its docstring. Only `dense_denseCountable` (30) and `countable_denseCountable` (34) carry meaning; `LimitModification.lean` uses it only through those two lemmas, so no result depends on the choice.

## BouRabeeGwynne.Upstream.BrownianMotion.Auxiliary.ENNReal — OK
- Statements hold at the ENNReal junk points: `le_one_div_iff` (28), `div_le_one_of_le` (32), `one_le_toReal` and `toReal_pos_of_one_le` (39, 44, with `p ≠ ⊤`), `rpow_iSup` (47, needs `0 < x`, fine for an empty index), `sum_geometric_two_le` (20), `ofReal_one_div` (24, `0 < x`), `ENat.toENNReal_le'` (62).

## BouRabeeGwynne.Upstream.BrownianMotion.Auxiliary.FiniteInf — OK
- Every lemma that is false on `∅` (`⨆ = ⊥`, `⨅ = ⊤`) carries nonemptiness: `Finset.Nonempty.sSup_eq_max'` (25), `Finset.iSup_eq_max'_image` (28), `iInf_eq_min'_image` (46), `Finset.iInf_mem_image` (56), `Set.Finite.iInf_mem_image` (61), `Set.Finite.lt_iInf_iff` (66, takes `s.Nonempty`).

## BouRabeeGwynne.Upstream.BrownianMotion.Auxiliary.MeanInequalities — OK
- `rpow_lintegral_le` (19) is the Jensen/Hölder bound `(∫f)^r ≤ μ(univ)^(r-1)·∫f^r` for `r ≥ 1`; ENNReal corners checked (`μ univ = ⊤`, `∫f^r = 0`). `lintegral_Lp_finsum_le` and its primed form (33, 48) are Minkowski for finite sums; `rpow_finsetSum_le_finsetSum_rpow` (55) is subadditivity for `0 < p ≤ 1`.

## BouRabeeGwynne.Upstream.BrownianMotion.Auxiliary.MeasureTheory — NOTE
- All statements are the intended ones. Harmless points: `condExp_inner_of_aestronglyMeasurable_left/right` (43, 48) have no `m ≤ mΩ`, but then `condExp` is the junk 0 on both sides; variance/covariance statements (`variance_fun_div` 264, `centralMoment_of_integral_id_eq_zero` 92, `covariance_fun_add_*` 254, 259) rely on Mathlib's variance-is-0 convention for non-L² variables, and remain true; `volume_closedBall_div'` (226) is correct for arbitrary `r, s : ℝ≥0∞`; `volume_of_nonempty_of_subsingleton` (115) gets `BorelSpace` from `Countable.instBorelSpace`.
- Typo: `measure_closeBall_const` (158, 202) names are misspelled.

## BouRabeeGwynne.Upstream.BrownianMotion.Auxiliary.Metric — OK
- `Metric.IsSeparated ε s` is strict (`s.Pairwise (ε < edist · ·)`), which is what makes `IsSeparated.disjoint_closedBall` (32) true; `disjoint_ball` (20), `disjoint_closedBall` (32) are correct at `ε = ⊤`; `closedEBall_add_closedEBall` (49), `nonempty_closedEBall` (45) fine.

## BouRabeeGwynne.Upstream.BrownianMotion.Auxiliary.Nat — OK
- `pow_two_mul_abs` (17): `|a|^(2n) = a^(2n)`, true for all `n`.

## BouRabeeGwynne.Upstream.BrownianMotion.Auxiliary.Topology — OK
- Hölder lemmas carry their side conditions: `Dense.holderWith_extend` (31, `0 < r`); `MemHolder.mono` and `mono'` (62, 79, bounded space); `HolderOnWith.mono_right` and `mono_right'` (88, 95, bounded set); `HolderWith.HolderWith_of_le_of_le` (106) and `HolderOnWith.holderOnWith_of_le_of_le` (124) interpolate with `max C₁ C₂`, correctly. `eventually_nhdsGT` (20), `neBot_comap_nhds` (28), `boundedSpace_toPseudoMetricSpace` (50) fine.

## BouRabeeGwynne.Upstream.BrownianMotion.Continuity.Chaining — NOTE
- `nearestPt` (43) is `Exists.choose` of an argmin, or `x` when `s = ∅`; every use goes through `nearestPt_mem` (46, needs `s.Nonempty`), `edist_nearestPt_le` (52), `edist_nearestPt_of_isCover` (59), and `chainingSequence_mem` gets nonemptiness from `IsCover` of a nonempty set.
- `chainingSequenceReverse` (100) uses `k - (n+1)`, which truncates only for `n ≥ k`; `chainingSequence` (128) calls it only at `k - n ≤ k`, so the truncated region is never entered. `scale_change` (236) and `scale_change_rpow` (285) are trivial for `m > k`.

## BouRabeeGwynne.Upstream.BrownianMotion.Continuity.CoveringNumber — NOTE
- Mathlib's `coveringNumber ε A : ℕ∞` is `⨅ (C ⊆ A) (IsCover ε A C), C.encard`; the index family is never empty (`C = A` covers), so `⊤` means "no finite internal cover".
- `TotallyBounded.coveringNumber_ne_top` (40) needs `r ≠ 0`. `coveringNumber_Icc_zero_one_le_one_div` (46) needs `ε ≤ 1`, false for `ε > 1`. Volume lemmas (146–301) handle the trivial and nontrivial `E` cases. `coveringNumber_closedBall_ge`, `one_ge`, `le`, `one_le`, `le_three_mul` (303–345) state `(r/ε)^d ≤ N ≤ (2r/ε+1)^d` and are consistent at `ε = 0`.
- Cosmetic: `EMetric.isCover_iff_subset_iUnion_closedBall` (136) is named `closedBall` but is about `closedEBall`; it duplicates Mathlib's `Metric.isCover_iff_subset_iUnion_closedEBall`, which the file uses (166).

## BouRabeeGwynne.Upstream.BrownianMotion.Continuity.HasBoundedInternalCoveringNumber — NOTE
- `HasBoundedCoveringNumber` (line 34) requires `ediam A < ∞` and `∀ ε : ℝ≥0, ε ≤ ediam A → coveringNumber ε A ≤ c * (ε:ℝ≥0∞)⁻¹ ^ d`, with `d : ℝ`. The docstring says `ε ∈ (0, diam A]`, but the Lean quantifier includes `ε = 0`, where the bound reads `c * ⊤ ^ d`.
- Effect: for `d > 0` the `ε = 0` clause is vacuous when `c > 0`; for `d < 0` it forces `coveringNumber 0 A ≤ 0`, so `A = ∅`, and for a singleton it is false while the docstring version is vacuous (range `(0, 0]` empty). The Lean definition is therefore stronger only in degenerate cases (finite sets with `d ≤ 0`); it is satisfiable for nonempty finite `J` with `c = |J| · diam^d`. It cannot make the statement vacuous in the regime used (`d > 0`).
- `coveringNumber_lt_top` (38), `subset` (53, gives `(2^d c, d)`) and `IsCoverWithBoundedCoveringNumber` (83) are correct; the last is shown satisfiable by `isCoverWithBoundedCoveringNumber_Ico_nnreal` (94).

## BouRabeeGwynne.Upstream.BrownianMotion.Continuity.IsKolmogorovProcess — NOTE
- Only `Cp` (line 543, `max (1/(2^((q-d)/p) - 1)^p) (1/(2^(q-d) - 1))`, ENNReal truncated subtraction) is defined here. For `d < q` and `p > 0` it is a finite positive constant; otherwise it degrades to `⊤`, which is conservative.
- The Mathlib notions it relies on: `IsKolmogorovProcess X P p q M` is Borel pair-measurability with `∀ s t, ∫⁻ edist(X s)(X t)^p ≤ M · edist s t ^ q`, `0 < p`, `0 < q`; `IsAEKolmogorovProcess` is "some Kolmogorov `Y` with `∀ t, X t =ᵐ Y t`", the usual modification. `P` is an arbitrary measure, not necessarily probability; the bounds are upper bounds on lintegrals, so they stay true. With `M = 0`, `0 · ⊤ = 0` forces points at infinite distance to coincide a.e., which is a stronger hypothesis and never a weaker conclusion.
- The estimates (pair reduction at 123, cover bounds at 156, 243, the `p ≥ 1` chain 272–362, the `p ≤ 1` chain 428–540, `second_term_bound` 546, `lintegral_sup_cover_eq_of_lt_iInf_dist` 569, `exists_nat_pow_lt_iInf` 637, and the three `finite_set_bound_of_edist_le*` lemmas 679–1017) carry the side conditions that matter (`1 ≤ p` vs `p ≤ 1`, `0 < d < q`, `δ ≠ 0`, `c ≠ ⊤`, nonempty and finite `J`). `finite_set_bound_of_edist_le` (1017) gives the stated bound. The reviewer reports that the `ofReal` truncation of the log term is harmless; I did not re-derive that.

## Nonvacuity examples
File: `Nonvacuity.lean`. Compiled from the repository root with `lake env lean …/Nonvacuity.lean`, exit status 0, no errors, no `sorry`. Output:
```
'BouRabeeGwynne.theoremA_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'A12Audit.theoremA_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'A12Audit.coupling_setup_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'BouRabeeGwynne.exists_standardBrownianProbabilityMeasure' depends on axioms: [propext, Classical.choice, Quot.sound]
'SpherePackings.exists_lattice_tilingSequence' depends on axioms: [propext, Classical.choice, Quot.sound]
'SpherePackings.isLipschitzDomain_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Contents of `Nonvacuity.lean`:
```lean
import BouRabeeGwynne.TheoremAProved
import BouRabeeGwynne.UniformStoppedWalkConvergence
import BouRabeeGwynne.StandardBrownianProbabilityMeasure
import SpherePackings.Support.Guards.LatticeTilings
import SpherePackings.Support.Guards.LipschitzBall

/-! Scratch nonvacuity checks for batch 12 (audit only; not part of the repository). -/

open MeasureTheory Metric Filter Set
open BouRabeeGwynne

namespace A12Audit

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

end A12Audit

#print axioms BouRabeeGwynne.theoremA_proved
#print axioms A12Audit.theoremA_instance
#print axioms A12Audit.coupling_setup_instance
#print axioms BouRabeeGwynne.exists_standardBrownianProbabilityMeasure
#print axioms SpherePackings.exists_lattice_tilingSequence
#print axioms SpherePackings.isLipschitzDomain_ball
```

What they show:
- `theoremA_instance`: the premise bundle of `TheoremAStatement` (Lipschitz `ball 0 1`, bounded, ambient collar in `G.domain`, (1.3), and (II)) is jointly satisfiable for every `d ≥ 1`, and applying `theoremA_proved` to it produces a standard Brownian law and eventually defined walk laws whose stopped laws converge uniformly over `z ∈ U`. So the theorem is not vacuous, and `IsStoppedTilingWalkLaw` is inhabited for the actual lattice tilings.
- `coupling_setup_instance`: the hypotheses of `exists_theoremA_coupling_setup` are satisfied by `ball 0 1` with a standard Brownian law from `exists_standardBrownianProbabilityMeasure`, so the coupling bundle is applicable (not vacuous in its premises). It does not show that the selector quantifier is non-empty; see TheoremACouplingSetup.
- Axioms: no `sorryAx`.

Not attempted (time budget): a formal measurable selector witnessing the `∀ selector` quantifier in `exists_theoremA_coupling_setup`, and a witness for the 10+ hypotheses of `exists_eventual_walkBrownian_coupling_partitions`.

## Process notes
- Two repository files have modification times inside the audit window and are outside this batch: `SpherePackings/Support/Section4General/Prop42.lean` (18:59:16) and `SpherePackings/General/MarkovChain/Absorbed.lean` (19:02:24). The Upstream reviewer was told not to edit and reports that it changed nothing. I cannot attribute the edits from timestamps alone, so their source is unknown and should be checked.
- Verdict counts for this batch: 14 OK, 11 NOTE, 0 ISSUE (12 main modules: 7 OK, 5 NOTE; 13 Upstream modules: 7 OK, 6 NOTE). The Upstream reviewer's own summary says "five files carry NOTEs", but its list contains six NOTE verdicts; the table uses the six.
