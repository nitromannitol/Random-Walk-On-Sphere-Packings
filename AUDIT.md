# Audit of the code adapted from Leonardo Bonanno's formalization

The directory `BouRabeeGwynne/` is copied from Leonardo Bonanno's (leobon12) formalization of the
paper, <https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne> (commit
`cf73d6e`), and modules of `SpherePackings/` adapt parts of it: Section 4 for tilings
(`Support/Section4/`) and for general walks (`Support/Section4General/`, with the walk/Brownian
coupling generalized to an arbitrary Markov kernel in `General/`), and the paper forms of Sections 2
and 3 (`Support/Section2/`, `Support/Section3/`).  Every proof is checked by the
Lean kernel; this audit checks what the kernel cannot: that each definition means what it says (and
what the paper means), that no statement has vacuous or contradictory hypotheses, and that no
statement is weaker than its docstring or the paper claims.

**Method.**  The 330 modules present at the first audit (the 319 copied files and the 11 of
`Support/Section4/`) were split into 15 batches in dependency order (batches 00–14); the 63 modules
adapted since (`General/`, `Support/Section4General/`, the guards `Support/Guards/TilingWalk` and
`AssumptionDLattice`, `Support/Section2/`, `Support/Section3/`) were reviewed in six more batches
(15–19; 20, the module `PlanarQuadratic` added afterwards, on its own).  Batch 21
reviewed the modules whose definitions or statements changed afterwards (the Poisson point process,
the covered spheres of Theorem 6.1, Lemmas 2.5 and 5.1) together with their frozen statements, and
replaces the batch-19 entry for `Support/Section2/DualCoverage`.  Batches 22 and 23 reviewed, against
the corrected paper `paper/rw-spheres-corrected.tex`, the modules added or changed for it (complete
cells, Propositions 2.6 and 3.2, the internal-edge layer and Theorems 3.3, 3.6 and 3.7, Lemma 5.1,
Proposition 1.1) with their frozen statements, and replace the earlier entries of the modules they
cover.  Each batch was reviewed
by an independent reviewer, Claude Haiku 5.5, a different model from the one that adapted the code
(Claude Opus 5.5), with read-only access and the paper.  For each module the reviewer checked every
`def`, `structure`, `class` and `instance` against the paper (with line references) and for junk-value
traps (`toReal ⊤ = 0`, division by zero, truncated subtraction, empty suprema, `tsum` of non-summable
families, defaults from `Classical.choice`), and every theorem statement for joint satisfiability and
for agreement with its docstring and with the paper.  For the hypothesis bundles whose satisfiability
is not obvious it wrote Lean examples, now in `SpherePackings/Audit/Nonvacuity/` (one file per batch,
all compiling).  The full reports are in `ledger/audit/`.

**Result.**  427 modules: 278 `OK`, 145 `NOTE` (a harmless convention,
recorded), 4 `ISSUE`.  No definition was found that does not mean what it says, and no
contradictory statement.  One vacuity was found later, outside these batches: the statements of
Proposition 1.1 assumed that `Λ_m` is a Poisson point process of intensity `m μ` on all of `ℝ^d`,
which no process satisfies when `μ` has an atom outside `W`; they now assume this only of the
points in `W`, with intensity `m μ|_W`, which follows from the old hypothesis
(`IsPoissonPointProcess.restrict_inter`).  The issues are about labels and disclosed hypotheses (the
summaries below are the reviewers', and describe the registry at the time of each review):

- `BouRabeeGwynne.Section3HarmonicInput`: Docstring calls `harmonic_error_energy_le_incidentMass` "Proposition 2.6", but the statement is the weaker PARTIAL variant (Hessian bound on 2·mesh balls around all of R, global mesh).  *Action:* The docstring of a copied file calls the weaker energy bound “Proposition 2.6”; the registered Proposition 2.6 is now `SpherePackings.harmonic_energy_bound_complete` (as in the corrected paper, `SpherePackings/Support/Section3/EnergyComplete.lean`; batch 22). No code change in the copied file.
- `SpherePackings.Support.Section4.Prop42`: `prop42_assumptionD` is labelled Proposition 4.2, but part (b) is uniform only over compact `K ⊂ ball`; the paper claims `sup` over the open unit ball.  *Action:* The tiling-only result is no longer registered as Proposition 4.2 (the general Proposition 4.2 is `SpherePackings.prop42_general`, uniform over the whole ball); its docstring now says it is a partial result.

- `SpherePackings.Support.Section3.PlanarCuts`: the docstring says that `Y` meets the unit line in a set of measure at most `ℓ`, while the hypothesis bounds the one-dimensional measure of all of `Y` (stronger; the two coincide at the use site, where `Y` lies on the line).  *Action:* the docstring now states the hypothesis as it is.
- `SpherePackings.Support.Section3.PlanarRateFull`: Theorem 3.3 assumes `L` is a Lipschitz constant of `h_C` between the vertices of `V̄[U]`, which the printed `L = sup_Û |∇ h_C|` does not imply.  *Action:* the module is now an intermediate result and is not registered; its header says so and that the printed mean value step can fail.  The registered Theorem 3.3 is the corrected paper's quadratic bound and rate, with no Lipschitz hypothesis (`PlanarInternal`, batch 23).

Batches 22 and 23 found no `ISSUE`.  *Actions on their notes:* the frozen headers of Propositions 2.6
and 3.2 and Theorems 3.3, 3.6 and 3.7 now say that harmonicity and the Hessian bound are asked only
on the cells of `V[U]` (a stronger statement than the corrected paper's), the cross-reference of
Theorem 3.3 to the corrected paper is fixed, the smallness condition `12 M ε ≤ 1` is described as an
instance of the paper's `ε < (C M)⁻¹`, and the header of `Support/Section3/InternalTaylor` states its
Laplacian bound as it is.

Repository-level note (batch 13): the vendored files under `BouRabeeGwynne/Upstream/` pointed to
`LICENSE` and `PROVENANCE.md` files that did not exist.  *Action:* those files were added in
`Upstream/BrownianMotion/` and `Upstream/KolmogorovExtension/`; the pointers now resolve.

Recurring notes (all harmless, each guarded by the hypotheses of every statement that uses it):
totalisation of never-exiting paths by exit time `⊤ ↦ 0` (`untopD 0`) or by the starting vertex;
`mesh.toReal` with `mesh = ⊤` in `RegularityII`, ruled out by the approximation condition (1.3);
undirected edge sums in the energies (half the paper's directed sums, documented in `CORRESPONDENCE.md`);
junk values of divisions and projections at degenerate parameters (`e = 0`, zero conductance) that
every statement excludes.

## Verdicts by module

| Module | Batch | Verdict | Summary |
|---|---|---|---|
| `BouRabeeGwynne.AbsorbingExcursionKernel` | 00 | OK | Generic selector/absorbing kernels; all maps total, no junk values. |
| `BouRabeeGwynne.DiscretePDEAlgebra` | 00 | NOTE | `energy` is half the paper's Dirichlet energy 𝒟(f,A): it sums each edge once, the paper sums directed edges. Constant factor 2 only. |
| `BouRabeeGwynne.StoppedWalk` | 00 | NOTE | Transition rows are the paper's p(w,v) and absorption. A zero-conductance interior row is junk (zero), unreachable because all uses assume `hpos`. |
| `BouRabeeGwynne.FiniteDirichlet` | 00 | OK | Accessibility, Dirichlet problem, maximum principle, uniqueness and stability match; accessibility criterion's hypothesis satisfiable (compiled). |
| `BouRabeeGwynne.FiniteExit` | 00 | OK | Survival probability is P(τ > n) by absorption; finite exit a.s. under accessibility. |
| `BouRabeeGwynne.CurveSpace` | 00 | OK | Fréchet distance is the infimum over increasing homeomorphisms of the supremal error (paper eq. cmp-topology); quotient is the metric curve space. |
| `BouRabeeGwynne.LocalGeometry` | 00 | OK | Mesh-distance lemmas; every `toReal` use is guarded by `mesh ≠ ∞`. |
| `BouRabeeGwynne.LocalRegion` | 00 | OK | V[U], ∂V[U], \bar V[U] match the paper; finiteness lemmas; guards as above. |
| `BouRabeeGwynne.FacetMeasure` | 00 | OK | Facet area positive and finite for adjacent cells (lemmas only). |
| `BouRabeeGwynne.DiscretePDE` | 00 | OK | `conductanceReal` = (1.1), `discreteLaplacian` = (1.4), `SolvesDirichlet` and `DirichletError` = discrete Dirichlet problem and (1.5). |
| `BouRabeeGwynne.TilingNetwork` | 00 | OK | Restriction to the closed region is faithful: interior neighbours lie in `closedVertices`. Uniqueness is only on the closed region, as documented. |
| `BouRabeeGwynne.PaperObjects` | 00 | NOTE | `RegularityII` uses `mesh.toReal` (⊤ ↦ 0), so the standalone predicate admits infinite mesh. Neutralised in Theorems A/B by `ApproximationCondition`. Other definitions match (1.1), (1.3), (I)–(III). |
| `BouRabeeGwynne.StoppedCurveLaws` | 00 | NOTE | `IsStandardBrownianLaw` = Mathlib Brownian motion per coordinate plus independence (satisfiable, compiled). Exit-time totalisations and `Measure.map` junk are guarded by the a.s./AEMeasurable conjuncts. |
| `BouRabeeGwynne.StoppedCurveMeasurable` | 00 | NOTE | `untopD 0` totalisation of never-exiting paths. The measurability statements are true for the totalised maps and irrelevant under a.s. finite exit. |
| `BouRabeeGwynne.DiscreteHarmonicMeasure` | 00 | NOTE | `exitVertex` totalises never-exit to the start vertex; `discreteHarmonicMeasure` is a probability measure even without accessibility. Every theorem assumes `haccess`. |
| `BouRabeeGwynne.TrajectoryCoupling` | 00 | OK | Generic intertwining lemma; hypotheses jointly satisfiable and conclusion correct. |
| `BouRabeeGwynne.WalkRestart` | 01 | OK | Shift and exit-time/exit-vertex restart identities are correct. |
| `BouRabeeGwynne.WalkMemoryless` | 01 | OK | Continuation law is the fresh walk from the last vertex; prefix shift is correct. |
| `BouRabeeGwynne.WalkJointRestart` | 01 | OK | Walk kernel and restart kernel are the genuine trajectory law; joint prefix/future factorisation is correct. |
| `BouRabeeGwynne.WalkStoppedHistory` | 01 | NOTE | `observedHistory`/`futureAt` totalise `τ = ⊤` to time 0; harmless because all uses are a.s. finite or absorbed by `⊤`. |
| `BouRabeeGwynne.WalkStrongMarkov` | 01 | OK | Strong Markov factorisation at an a.s. finite stopping time; restart depends only on the terminal vertex; `hfin` is satisfiable. |
| `BouRabeeGwynne.WalkAdaptiveStopping` | 01 | OK | Adaptive next-exit time is a stopping time; `⊤` and `none` cases are correct; inclusion direction of `exitTime_le_of_subset` is correct. |
| `BouRabeeGwynne.WalkPathStopping` | 01 | OK | `stoppedWalkPath B` freezes at the first vertex outside `B`; `≤` at the exit time is correct. |
| `BouRabeeGwynne.StoppedCurveProperties` | 01 | NOTE | Interpolation identities are correct; endpoint on never-exiting paths is `pos (ω 0)` (same totalisation as `exitVertex`), harmless. |
| `BouRabeeGwynne.LevyProkhorovMaps` | 01 | OK | 1-Lipschitz measurable maps contract Mathlib's Lévy–Prokhorov edistance; endpoint map is 1-Lipschitz on `CurveSpace`. |
| `BouRabeeGwynne.HarmonicMeasureBridge` | 01 | NOTE | Endpoint identity is correct without `BoundaryAccessible` only because both sides share the `⊤` totalisation; `discreteHarmonicMeasure` is the true harmonic measure only under a.s. finite exit, which the docstring omits. |
| `BouRabeeGwynne.TimePartition` | 01 | OK | `n+1` nondegenerate intervals from 0 to 1; piecewise-affine increasing homeomorphism is correct; `Classical.choose` is harmless. |
| `BouRabeeGwynne.SkeletonCurveComparison` | 01 | OK | Segment-oscillation bounds give Fréchet bound `α+β+γ` in the paper's inf-over-increasing-homeomorphisms metric; constant-curve distance is correct. |
| `BouRabeeGwynne.ExcursionConcatenation` | 01 | OK | Adjacent-endpoint chain condition, 1-Lipschitz concatenation and exact `concatenate ∘ restrictChain` are correct. |
| `BouRabeeGwynne.WalkExcursionKernel` | 01 | NOTE | `stoppedPolygonalRepresentative` totalises `⊤` to a constant curve at `ω 0`; harmless (a.s. excluded), identities are correct. |
| `BouRabeeGwynne.ClockedWalkExcursion` | 01 | NOTE | `ofWalk` totalises `⊤` to duration 0; the pair type is not quotiented, so entries beyond the duration are representation-dependent, but kernels only produce canonically padded values. |
| `BouRabeeGwynne.DependentKernelMap` | 01 | OK | Dependent-kernel pushforward identity is correct; hypothesis `hmap` is satisfiable. |
| `BouRabeeGwynne.WalkAbsorption` | 01 | OK | Absorption locality (stopping an `A`-walk at first exit from `B ⊆ A` gives the `B`-absorbed walk) is correct, including infinite-exit paths. |
| `BouRabeeGwynne.WalkSelectedRestart` | 01 | NOTE | Selected-excursion kernel and joint-law theorem are correct; `[MeasurableSpace (Option J)]` is a free parameter that is forced to be `⊤` for countable `J`, harmless. |
| `BouRabeeGwynne.ActualWalkSkeleton` | 01 | NOTE | Stage recursion is correct and `actualWalkStage_ae_all_clocks_finite` matches its docstring; selector is memoryless (stage and current vertex, as in the paper), and `clockedWalkSegment` uses truncated subtraction (valid only for `a ≤ b`). |
| `BouRabeeGwynne.ClockedWalkConcatenation` | 01 | NOTE | `append` has no docstring and no endpoint-compatibility precondition (junction taken from `e`, `f.2 0` dropped); correct for the segments actually used. |
| `BouRabeeGwynne.ClockedWalkStopping` | 02 | NOTE | `vertexStoppedCurve` totalizes a never-exiting trajectory to the start curve; every lemma assumes `exitTime ≤ M` |
| `BouRabeeGwynne.WalkSegmentRestriction` | 02 | OK | Scaled-time restriction identities are correct; `b - a` (ℕ) only used under `a ≤ b` |
| `BouRabeeGwynne.CurvePauses` | 02 | NOTE | Pause invariance matches the paper's inf over increasing homeomorphisms; `terminalPauseClock a` is junk for `a ≤ 0`, all uses have `0 < a` |
| `BouRabeeGwynne.WeakExcursionClock` | 02 | OK | Weak knots and `weakClock` are genuine continuous monotone clocks from 0 to 1 |
| `BouRabeeGwynne.WeakExcursionRecovery` | 02 | OK | Restriction chains recover the Fréchet class; statements match |
| `BouRabeeGwynne.WalkExcursionRecovery` | 02 | OK | Pasted actual segments recover the original polygonal class; hypotheses satisfiable |
| `BouRabeeGwynne.ClockedWalkExitParameter` | 02 | NOTE | `concatenatedExitIndex` is 0 when the pasted walk never leaves U (silent); harmless, the consumer requires `f a ∉ U` |
| `BouRabeeGwynne.WalkSkeletonObservation` | 02 | OK | Observed past recovers the whole prefix; `hfin` is the needed finiteness hypothesis |
| `BouRabeeGwynne.ExcursionEndpointExtension` | 02 | OK | Constant off-graph extension agrees with the vertex kernel at every vertex |
| `BouRabeeGwynne.WalkSkeletonKernel` | 02 | OK | Stage-n history kernel uses `select n` at the current endpoint, as `actualWalkStage` does |
| `BouRabeeGwynne.DependentKernelMapAE` | 02 | OK | Standard a.e.-intertwining lemma; hypotheses are the needed ones |
| `BouRabeeGwynne.TrajectoryIdentification` | 02 | OK | Law of a sequence determined by initial law and one-step conditionals; no hidden contradictions |
| `BouRabeeGwynne.WalkSkeletonLaw` | 02 | OK | Main law identity; bundle is nonvacuous (Example 1); `ofWalk` junk excluded by `haccess` |
| `BouRabeeGwynne.ExcursionTrajectory` | 02 | NOTE | `zeroChain` fallback is junk on incompatible paths, a null set by `ae_compatiblePaths` (documented) |
| `BouRabeeGwynne.WalkSkeletonPrefix` | 02 | NOTE | `actualWalkStage_times` uses `untopD 0`; every statement assumes `hfinite` |
| `BouRabeeGwynne.WalkStoppedReconstruction` | 02 | NOTE | `reconstructedVertexStoppedCurve` inherits the `untopD 0` totalization; guarded by `hexit` |
| `BouRabeeGwynne.SubcouplingCompletion` | 02 | NOTE | `completeSubcoupling` uses truncated measure subtraction; correct only under the dominance hypotheses the theorems carry |
| `BouRabeeGwynne.MatchedCellCoupling` | 02 | OK | Masses and supports correct; `c / μE` junk is unreachable since `c ≤ μE` |
| `BouRabeeGwynne.FinitePartitionCoupling` | 02 | OK | Exact marginals and bad-event bound `1 - Σ min` are correct; disjointness is used |
| `BouRabeeGwynne.PartitionCouplingDistance` | 02 | OK | Coupling-to-Lévy–Prokhorov bounds are standard; ENNReal subtraction harmless |
| `BouRabeeGwynne.ReconstructedLawComparison` | 02 | OK | LP ≤ r from a.e. agreement off a set of mass ≤ r |
| `BouRabeeGwynne.WalkReconstructionLaw` | 02 | OK | Stopped vs reconstructed LP ≤ P(still active); junk on the bad event is absorbed by the bound |
| `BouRabeeGwynne.BoundaryStoppingComparison` | 02 | OK | Oscillation / time-change comparison of stopped curves is correct |
| `BouRabeeGwynne.StoppedCurvePrefixes` | 02 | OK | Constant padding equals the normalized prefix in the Fréchet class, including `a = 0` |
| `BouRabeeGwynne.MonotoneStoppedPrefixes` | 02 | OK | Stopping at corresponding points of a monotone clock preserves the class, including `b = 0` |
| `BouRabeeGwynne.PolygonalVertexExitGeometry` | 02 | NOTE | Pre-exit containment holds only in the ε-thickening (polygon edges may leave U); docstring's "first vertex" is not a continuous first exit |
| `BouRabeeGwynne.StoppedBrownianMeasurable` | 03 | OK | Exit time, representative, curve and law are measurable for every path; the τ=∞ totalization only affects a null set (documented). |
| `BouRabeeGwynne.ContinuousExitProperties` | 03 | OK | Finite exit is attained, the endpoint lies on the frontier; hypotheses (open U, finite exit, start inside) are the needed ones. |
| `BouRabeeGwynne.UnitCurveExit` | 03 | OK | `min _ 1` removes the ⊤ junk; capped exit time, representative and measurability are correct. |
| `BouRabeeGwynne.IndependentCoordinatePairs` | 03 | OK | Standard regrouping lemma; hypotheses are jointly satisfiable by i.i.d. coordinates. |
| `BouRabeeGwynne.BrownianWeakMarkov` | 03 | OK | Deterministic-time future increments are independent of the whole past; matches docstring. |
| `BouRabeeGwynne.BrownianLawUniqueness` | 03 | OK | `IsStandardBrownianLaw` = Mathlib pre-Brownian coordinates + a.s. continuity + coordinate independence; uniqueness correct. |
| `BouRabeeGwynne.BrownianScaling` | 03 | OK | `r⁻¹ • ω(r²·)` is the correct parabolic scaling; `0⁻¹ = 0` junk at r = 0 is guarded by `0 < r` in every theorem. |
| `BouRabeeGwynne.BrownianExitStoppingTime` | 03 | OK | First exit is a stopping time for the (non-augmented) natural filtration; matches docstring. |
| `BouRabeeGwynne.BrownianFiniteStopping` | 03 | OK | Strong Markov factorization for finitely valued stopping times; docstring says so explicitly. |
| `BouRabeeGwynne.BrownianGaussianReference` | 03 | OK | Translated marginals are N(z, tI) and are ≪ N(0, I) for t > 0; matches. |
| `BouRabeeGwynne.BrownianUniformLanding` | 03 | OK | Uniform positive landing probability over ‖c‖ ≤ 2; open-positive marginal, d = 0 included. |
| `BouRabeeGwynne.BrownianScaledLanding` | 03 | OK | Parabolic rescaling of the landing bound with dist(c, x) ≤ 2r; correct. |
| `BouRabeeGwynne.ContinuousPathRange` | 03 | OK | Range events are closed, increasing and exhaust the paths; tightness statement correct. |
| `BouRabeeGwynne.BrownianLandingRange` | 03 | NOTE | Range bound is on the displacement ‖ω t‖ from the start x (walk x + ω), not from the origin; the docstring is accurate only in that reading. |
| `BouRabeeGwynne.BrownianExcursionRange` | 03 | OK | Time/range links via `toNNReal` with the needed finite-exit hypotheses; matches docstring. |
| `BouRabeeGwynne.BrownianMoments` | 03 | OK | Fourth moments 3v² and 3\\|s−t\\|² are correct, including v = 0. |
| `BouRabeeGwynne.GaussianIncrementBounds` | 03 | OK | Markov bound 3v²/r⁴ with r > 0 required and given. |
| `BouRabeeGwynne.BrownianQuadraticMoments` | 03 | OK | E[ω_t^i ω_t^j] = tδ_ij, E‖B_t‖⁴ ≤ 3d²t², and ‖x‖⁴ ≤ d Σ x_i⁴ are correct. |
| `BouRabeeGwynne.BrownianPredictableMoments` | 03 | NOTE | Predictable linear/quadratic identities carry no integrability hypothesis on C; the Bochner integral is junk 0 when C is not integrable, so "= 0" holds in Lean but is meaningful only for integrable C. |
| `BouRabeeGwynne.Harmonic` | 03 | NOTE | `IsHarmonicOn` is documented for open sets but accepts arbitrary U; for non-open U the Δ clause at boundary points uses global Fréchet derivatives (junk 0 where h is not C²). Every caller that matters is open or globally C². |
| `BouRabeeGwynne.BrownianHessianGenerator` | 03 | NOTE | Both statements hold without a C²-at-x hypothesis; where f is not twice differentiable at x both sides are Lean junk 0, so the content requires C² at x. |
| `BouRabeeGwynne.BrownianTaylorBound` | 03 | NOTE | Remainder hypothesis hR is global in y, although the docstring describes a compact neighbourhood; satisfiable for compactly supported C² f (checked). |
| `BouRabeeGwynne.BrownianPredictableTaylor` | 03 | OK | Integrability of F is derived, and the linear/quadratic terms carry integrability hypotheses; matches docstring. |
| `BouRabeeGwynne.HessianTaylorRemainder` | 03 | OK | Oscillation remainder bound with constant ε (weaker than the true ε/2, so sound); uniform and compact-support versions match docstrings; nonvacuity compiled. |
| `BouRabeeGwynne.BrownianStoppedStep` | 03 | OK | Uniform one-step bound with C independent of t, s, X, A; f is globally C², so Δ is classical; nonvacuity compiled with a nonzero f. |
| `BouRabeeGwynne.DyadicExitApprox` | 03 | OK | `nnrealApproxSeq τ n ω = ⌈τ ω · 2ⁿ⌉ / 2ⁿ` with no truncation junk; matches the docstring formula. The vendored upstream source is not in the repo, so provenance is not diffable here. |
| `BouRabeeGwynne.BrownianStoppingApprox` | 03 | OK | Ceiling dyadic times; the range is finite and covers all dyadic values ≤ N; matches docstring. |
| `BouRabeeGwynne.BrownianStoppedSum` | 03 | OK | Telescoping identity is right, including the upper-approximation endpoint and the crossing step; C is uniform over σ, N, z, n. |
| `BouRabeeGwynne.BrownianStoppedLimit` | 04 | OK | Bounded stopped harmonic identity; hypothesis bundle satisfiable (see nonvacuity witness 2). |
| `BouRabeeGwynne.BrownianFiniteExit` | 04 | OK | A.s. finite exit from bounded sets, Gaussian tail lemmas; `1 ≤ d` is essential and assumed. |
| `BouRabeeGwynne.BrownianHarmonicExit` | 04 | NOTE | Harmonic exit identity; `toNNReal` of exit time in the integrand is junk only on a μ-null set. |
| `BouRabeeGwynne.BrownianExcursionKernel` | 04 | NOTE | Kernel `μ.map (stoppedBrownianRepresentative U)` is the excursion law only when P(exit = ∞) = 0; all uses in this batch are bounded balls. |
| `BouRabeeGwynne.LipschitzDomain` | 04 | NOTE | Chart definition is the standard local strict-epigraph definition; `d - 1` truncation is harmless (d = 0 has no frontier). |
| `BouRabeeGwynne.LipschitzExteriorGeometry` | 04 | OK | Coordinate projections and norm bounds; correct. |
| `BouRabeeGwynne.LipschitzExteriorBalls` | 04 | OK | Ball of radius ρ below a K-Lipschitz graph when (K+1)ρ ≤ a; correct. |
| `BouRabeeGwynne.LipschitzChartExteriorBalls` | 04 | OK | Exterior ball inside one rigid chart; cylinder margins are exactly what is needed. |
| `BouRabeeGwynne.LipschitzLocalExteriorBalls` | 04 | OK | Local exterior balls with κ = 1/(2(K+1)); correct. |
| `BouRabeeGwynne.LipschitzUniformExteriorBalls` | 04 | OK | Uniform s, κ by compactness of the frontier; empty-frontier case vacuous; correct. |
| `BouRabeeGwynne.ExteriorBallBuffer` | 04 | OK | Half-radius ball lies outside the δ-collar for δ < R/2; correct by triangle inequality. |
| `BouRabeeGwynne.BrownianBoundaryExcursion` | 04 | OK | Uniform boundary survival contraction, ∃ q < 1, R > 1 before ∀ U, p, c, r; statement and bound are correct. |
| `BouRabeeGwynne.WalkCanonicalStopping` | 04 | NOTE | `untopD 0` makes a no-exit prefix have exit index 0; excluded by `f a ∉ U`. The Bool flag is not used by the support set. |
| `BouRabeeGwynne.BoundaryStoppingGeometry` | 04 | OK | Vertex-exit time lies in [l, u] under the stated collar conditions; both bounds verified. |
| `BouRabeeGwynne.BrownianInnerExit` | 04 | NOTE | `innerDomain` uses `infDist x Uᶜ`, which is 0 when U = univ; such U are excluded by every caller. |
| `BouRabeeGwynne.UnitCurveOscillation` | 04 | OK | Affine reparametrization onto [a, b], closed diameter bound, measurable bad set; correct. |
| `BouRabeeGwynne.FiniteStoppedCurveComparison` | 04 | OK | Deterministic comparison; hypotheses consistent; conclusion `ofReal (ε + η)` is correct. |
| `BouRabeeGwynne.UnitCurveExitMonotone` | 04 | OK | Capped exit time commutes with monotone surjective reparametrization; correct. |
| `BouRabeeGwynne.PhysicalExcursionRecovery` | 04 | OK | Monotone knots allow zero durations as documented; zero total duration handled. |
| `BouRabeeGwynne.BrownianExitRestart` | 04 | OK | Restart identity holds including the ∞ case; no hidden premise. |
| `BouRabeeGwynne.BrownianPathFreezing` | 04 | NOTE | Measurability of the frozen path at a stopping time; `toNNReal` totalization on {τ = ∞} is explicit and harmless. |
| `BouRabeeGwynne.BrownianStoppingLimit` | 04 | OK | `map_eq_of_ae_tendsto_of_map_eq` is a correct dominated-convergence law identification. |
| `BouRabeeGwynne.BoundedBrownianMarkov` | 04 | OK | Strong Markov at bounded stopping times; statement correct. |
| `BouRabeeGwynne.BrownianStrongMarkov` | 04 | NOTE | Strong Markov at a.s. finite times; `toNNReal` junk only on {τ = ∞}, a μ-null set excluded by `hfinite`. |
| `BouRabeeGwynne.BrownianStoppingHistory` | 04 | NOTE | Joint history/future law; same `toNNReal` totalization on a μ-null set guarded by `hfinite`. |
| `BouRabeeGwynne.BrownianNextExit` | 04 | OK | `brownianNextExitTime = τ + η`; ⊤ absorbs the junk; a.s. finiteness correct. |
| `BouRabeeGwynne.BrownianPhysicalSegments` | 04 | OK | Stopped representative equals the physical-time segment as maps; hypotheses present. |
| `BouRabeeGwynne.PhysicalPrefixExit` | 04 | OK | Exit parameter times T equals the exit time when τ ≤ T; premise present. |
| `BouRabeeGwynne.BrownianSelectedExit` | 04 | OK | `none` retains τ; the frozen-choice hypothesis is satisfiable (constant choice). |
| `BouRabeeGwynne.BrownianSkeletonClock` | 05 | NOTE | Clock/flag/time definitions match the intended semantics; ∞-time junk only on a null set; selector index 0 unused; z ∉ U j₀ gives a zero-length active excursion (harmless convention). |
| `BouRabeeGwynne.BrownianObservedHistory` | 05 | OK | Freezing-based stopping-time measurability and endpoint lemmas; hypotheses are exactly the stopping-time freezing identities. |
| `BouRabeeGwynne.BrownianExcursionSampler` | 05 | OK | Sampler matches the selected/absorbing excursion kernels; terminated flag is absorbing. |
| `BouRabeeGwynne.BrownianSkeletonExcursion` | 05 | OK | Successive excursions use the original clock and the shifted path at it; endpoint and flag identities consistent. |
| `BouRabeeGwynne.BrownianSkeletonLaw` | 05 | OK | Full excursion-sequence law equals the Markov trajectory law; premises satisfied by the Wiener law (Nonvacuity 1). |
| `BouRabeeGwynne.BrownianSkeletonPrefix` | 05 | OK | Physical knots (0, τ₀,…,τₙ) give n+1 pieces matching excursions 0..n; duration equals the clock; no junk (finiteness hypothesis carried). |
| `BouRabeeGwynne.BrownianUniformModulus` | 05 | NOTE | Modulus event and its ε-oscillation meaning are right; docstring mentions translation invariance and "uniform over translated starts", which the file does not state or prove. |
| `BouRabeeGwynne.BrownianSkeletonTail` | 05 | OK | Pigeonhole short-step lemma and uniform skeleton-count tail; quantifier order ∃K ∀z∈U is correct. |
| `BouRabeeGwynne.BrownianNestedExit` | 05 | OK | Exit times are monotone in the domain; nested restart identity holds including ∞. |
| `BouRabeeGwynne.BrownianActiveSkeletonTail` | 05 | OK | Uniform active-tail bound with K depending only on V, ε, η, μ; margin hypothesis satisfiable (Nonvacuity 2). |
| `BouRabeeGwynne.BrownianStoppedSkeleton` | 05 | OK | Stopped-curve reconstruction under the target-exit hypothesis; Lévy–Prokhorov bound by bad-event mass; hypotheses consistent. |
| `BouRabeeGwynne.FinitePartitionCouplingKernel` | 05 | NOTE | Exact marginals and failure bound are right; `(κ a univ)⁻¹ = ⊤` at zero mass is harmless (⊤ • 0 = 0). |
| `BouRabeeGwynne.FiniteCellCouplingError` | 05 | OK | Cell-error bound with ENNReal truncated subtraction used only as an upper bound; covering hypothesis ν(⋃F)=1 is the right one. |
| `BouRabeeGwynne.SkeletonCoupling` | 05 | OK | Adaptive first-failure bound uses the one-step estimate only on good histories; joint path law has the stated marginals. |
| `BouRabeeGwynne.WalkBrownianCoupling` | 05 | NOTE | Matching cells exclude terminated states; `brownianSelectorForWalk` at n=0 is unused junk; joint-law marginal lemma does not link z to pos v (downstream supplies dist ≤ a). |
| `BouRabeeGwynne.WalkBrownianCellMeasures` | 05 | NOTE | Cell masses and finite-cell bad bound are right; m = 0 is vacuous (hcover with z ∈ U is contradictory); herror is automatic when b ≥ m+1. |
| `BouRabeeGwynne.FixedBallCover` | 05 | OK | Fixed-ball cover, inner-ball containment (strict) and exit displacement r/2 are correct. |
| `BouRabeeGwynne.FiniteCellSelector` | 05 | NOTE | Label/selector definitions correct under the disjointness hypotheses; `exists_cell_ball_choices` demands diameter bounds for every cell although only cells meeting K need them. |
| `BouRabeeGwynne.WalkBrownianGoodEvent` | 05 | OK | Success set = same active cell, or both terminated with endpoint distance ≤ a; mixed flags never succeed. |
| `BouRabeeGwynne.WalkBrownianStep` | 05 | OK | Row identities and one-step bad-mass bounds (active, terminated, initial) match the intended coupling; herror is a per-history hypothesis. |
| `BouRabeeGwynne.WalkBrownianFailure` | 06 | NOTE | Bound `(k+1)b` matches docstring; `herror`/`hinit` use `discreteHarmonicMeasure`, whose exit vertex is junk for never-exiting walks, and no `BoundaryAccessible` hypothesis is assumed |
| `BouRabeeGwynne.WalkBrownianActiveTransfer` | 06 | OK | Truncation inequality; flag convention (`false` = active) is consistent with the rest of the batch |
| `BouRabeeGwynne.FiniteStoppedLawComparison` | 06 | NOTE | `ρ` need not be a probability measure; `innerDomain` (out of batch) is ∅ when `Uᶜ = ∅`, so `hosc` is a different event for `U = univ`; harmless for bounded `U` |
| `BouRabeeGwynne.BrownianStoppedEndpoint` | 06 | NOTE | Non-a.e. lemma uses `toNNReal ∞ = 0` on never-exiting paths; consistent because the selector sees the same position; a.e. lemma is clean |
| `BouRabeeGwynne.ExcursionOscillation` | 06 | OK | Oscillation bounds (`2r`, `R + a + S`) match their statements |
| `BouRabeeGwynne.TilingWalkRegionEmbedding` | 06 | OK | Region enlargement preserves absorbed walk law under `neighbors v ⊆ R` for active `v` |
| `BouRabeeGwynne.TilingClockedExcursion` | 06 | OK | Clocked excursion law is region-independent; statements match docstrings |
| `BouRabeeGwynne.Section3LocalMaximum` | 06 | OK | `externalBoundary` is the graph boundary; clamping argument is correct |
| `BouRabeeGwynne.Section3Iteration` | 06 | OK | Trimming rule and `\|replacement − h\| ≤ κ + δ` are as documented |
| `BouRabeeGwynne.Section3Boxes` | 06 | OK | Box/cell-cut lemmas; `mesh ≠ ∞` is assumed where `toReal` is used |
| `BouRabeeGwynne.HalfspaceBoundary` | 06 | OK | Interior and frontier characterizations are correct without irredundancy |
| `BouRabeeGwynne.HalfspaceFibers` | 06 | NOTE | `planeParameter` divides by zero for constraints parallel to `e`; the junk is never used (filtered) |
| `BouRabeeGwynne.FiberEndpoints` | 06 | OK | Active-constraint and frontier statements are correct |
| `BouRabeeGwynne.ProjectedBase` | 06 | NOTE | `hyperplaneProjection e` is `id` when `e = 0` (not a hyperplane projection); all uses that matter have `e ≠ 0` |
| `BouRabeeGwynne.Section3Projection` | 06 | OK | Orthogonal projection is 1-Lipschitz; facet measure does not increase |
| `BouRabeeGwynne.Section3GoodLines` | 06 | OK | Strict-margin good-parameter lemma is correct |
| `BouRabeeGwynne.PolytopeBoundary` | 06 | OK | Closure of interior and facet-in-frontier lemmas are correct |
| `BouRabeeGwynne.LocalFacetCoverage` | 06 | OK | Frontier equals union of contacts; lower-dimensional contacts are included as documented |
| `BouRabeeGwynne.Section3ColumnTraversal` | 06 | OK | Strict increase of fiber endpoints across touching cells |
| `BouRabeeGwynne.Section3GraphPaths` | 06 | OK | Telescoping and boundary-path lemmas are correct |
| `BouRabeeGwynne.FacetNormals` | 06 | OK | Separation signs (outward from `v`, inward to `w`) are correct |
| `BouRabeeGwynne.FacetNull` | 06 | OK | Non-adjacent contacts have zero `facetVolume` |
| `BouRabeeGwynne.Section3ColumnPaths` | 06 | OK | Almost every column has boundary-reaching paths in the column graph |
| `BouRabeeGwynne.Section3WeightedEnergy` | 06 | NOTE | Lemma 3.5 is stated in facet form (`facetVolume · length`), equal to `d·vol(Q_e)` only via Lemma 2.4; `1/2` normalizes unordered edges |
| `BouRabeeGwynne.Section3ColumnEnergy` | 06 | OK | Integral and Cauchy–Schwarz bounds are correct |
| `BouRabeeGwynne.Section3ColumnEdgeIndex` | 06 | OK | Oriented edges are counted once; column graph edges match the filter |
| `BouRabeeGwynne.Section3ColumnEstimate` | 06 | NOTE | Lemma 3.1 bound matches the printed threshold with undirected sums; the printed directed sums give a threshold twice as large, so the Lean statement is stronger |
| `BouRabeeGwynne.GraphMeasure` | 07 | OK | Graph area factor sqrt(1+‖b‖²) and affine-graph measure/integral transport are the standard ones. |
| `BouRabeeGwynne.HyperplaneGraph` | 07 | NOTE | Slope/intercept divide by `a none` (x/0 = 0 at `a none = 0`); every parametrization statement carries `a none ≠ 0`. |
| `BouRabeeGwynne.CoordinateHyperplane` | 07 | OK | Coordinate deletion/reparametrization of `a·x=c` and its area/flux formulas match the hyperplane formulas. |
| `BouRabeeGwynne.Section3PlanarEstimate` | 07 | OK | Planar good-box and column-measure estimates; `mesh ≠ ⊤` is an explicit hypothesis wherever `mesh.toReal` is used. |
| `BouRabeeGwynne.Approximation` | 07 | NOTE | (1.3) encoded faithfully; `NearestVertexData` presupposes minimizers exist for all z ∈ D, which the paper also presupposes but does not prove (see below). |
| `BouRabeeGwynne.ApproximationGeometry` | 07 | OK | Consequences of (1.3): eventual finite mesh, uniform nearest-vertex error, eventual cell inclusion. |
| `BouRabeeGwynne.NearestVertexExistence` | 07 | OK | Nearest vertex exists when `closedBall z r ⊆ D` with `mesh.toReal ≤ r`; hypotheses as stated. |
| `BouRabeeGwynne.EventualLocalRegion` | 07 | NOTE | Docstring says "external" vertices, but the statement covers all of `closedVertices U` (stronger, true). |
| `BouRabeeGwynne.Section3CompactCollar` | 07 | OK | Compact collar Q, Hessian bound M, continuity modulus; each conjunct matches the docstring. |
| `BouRabeeGwynne.Section3EdgeSums` | 07 | OK | Handshaking identity for ordered vs. unordered edge sums. |
| `BouRabeeGwynne.Section3EnergyNormalization` | 07 | OK | Oriented-edge sums, `incidentEnergy` = network energy when exterior values vanish, mass = Σ facetVolume·edgeLength. |
| `BouRabeeGwynne.DualDirichlet` | 07 | NOTE | `dualEnergy` divides by `a w v`, so off-edge θ contributes 0; all uses force θ = 0 where a = 0. Lemma 2.3 statement matches. |
| `BouRabeeGwynne.FiniteFluxEnergy` | 07 | OK | Energy = ½ dual energy of gradient; Dirichlet argument order checked against the definition. |
| `BouRabeeGwynne.FluxResidual` | 07 | OK | Pointwise Taylor residual on balls, uniform over short pairs near U; constants depend only on h, U, W. |
| `BouRabeeGwynne.FacetFlux` | 07 | OK | Surface flux v→w is the outward normal flux of cell v; residual bound and integrability as stated. |
| `BouRabeeGwynne.SupportedSurfaceField` | 07 | OK | Index convention `(w,v)` gives discrete divergence at v = outward flux from v; residual-to-energy bound correct. |
| `BouRabeeGwynne.SupportFaceProjection` | 07 | OK | Actual face slices and upper/lower active regions; projection identities as stated. |
| `BouRabeeGwynne.FacetProjection` | 07 | OK | Projection of contact facets to upper/lower endpoints; overlap projection statements correct. |
| `BouRabeeGwynne.ContactCoordinateFlux` | 07 | OK | Coordinate-normal contact flux equals ± integral over upper/lower endpoint projection. |
| `BouRabeeGwynne.TripleContact` | 07 | OK | Triple contacts have rank < d−1; pairwise contact overlaps are surface-null. |
| `BouRabeeGwynne.FacetPartition` | 07 | OK | Boundary of a cell is the surface-disjoint union of its (possibly partial) contacts. |
| `BouRabeeGwynne.Section3ParallelFacetProjection` | 07 | OK | Contacts parallel to the column direction project to a surface-null set. |
| `BouRabeeGwynne.ProjectedContactPartition` | 07 | OK | a.e. decomposition of projected bases into upper/lower contact projections. |
| `BouRabeeGwynne.CoordinateVolume` | 08 | OK | Coordinate splitting is measure-preserving with Euclidean normalization; Fubini statement is the standard one. |
| `BouRabeeGwynne.FiberCalculus` | 08 | OK | FTC along a fiber; fiber endpoints are inf'/sup' over nonempty constraint sets, so no junk value enters. |
| `BouRabeeGwynne.CoordinateFiberFubini` | 08 | OK | Coordinate divergence identity over a cell, with upper endpoint signed +, lower endpoint −, as printed. |
| `BouRabeeGwynne.CoordinateLaplacian` | 08 | OK | Σᵢ ∂²ᵢᵢ h equals Mathlib's Δ (trace of Hessian, standard sign). |
| `BouRabeeGwynne.PolytopeGaussGreen` | 08 | OK | Sum over contacts of outward flux equals ∫Δh; (pos w − pos v) is outward for P_v by orthogonality. |
| `BouRabeeGwynne.SurfaceEnergyEstimate` | 08 | NOTE | Hessian estimate has the PARTIAL Prop 2.6 hypotheses (2·mesh balls, global mesh), not flagged in the docstring; `mesh ≠ ⊤` guards the `toReal`. |
| `BouRabeeGwynne.Section3HarmonicInput` | 08 | ISSUE | Docstring calls `harmonic_error_energy_le_incidentMass` "Proposition 2.6", but the statement is the weaker PARTIAL variant (Hessian bound on 2·mesh balls around all of R, global mesh). |
| `BouRabeeGwynne.Section3MassTrimming` | 08 | NOTE | Unscaled trimming lemma uses one δ both as edge-length cap and trimming threshold; correct but narrower; the scaled lemma (used downstream) has independent L, ℓ. |
| `BouRabeeGwynne.DualCells` | 08 | OK | `cellPyramid`, `dualPolytope`, `dualVolume` match the paper's Q_e = conv(w, P_w∩P_v) ∪ conv(v, P_w∩P_v) (rw-spheres.tex:725–728). |
| `BouRabeeGwynne.PyramidSlices` | 08 | OK | Perpendicular slices and homothety are correct; the `t ≠ 0` hypothesis of the slice-measure formula is genuinely needed. |
| `BouRabeeGwynne.Section3CylinderVolume` | 08 | NOTE | `orthogonalCylinder` is junk for e = 0 (x/0 = 0); harmless since every lemma takes `e ≠ 0`. Volume formula is correct. |
| `BouRabeeGwynne.ConeIntegrals` | 08 | OK | ∫₀ʳ (t/r)ᵏ dt = r/(k+1) and its lintegral/nnnorm variants; all need and have r > 0. |
| `BouRabeeGwynne.PyramidVolume` | 08 | OK | Cone volume ‖e‖·(r/d)·area(base), i.e. base × height / d, with height r‖e‖. |
| `BouRabeeGwynne.FacetPyramidHeights` | 08 | OK | Each contact lies in the slice at a height r ∈ (0,1) from its apex, from orthogonality. |
| `BouRabeeGwynne.DualAdditivity` | 08 | OK | The two halves of a dual cell meet exactly in the facet; dual volume is the sum of the two pyramid volumes. |
| `BouRabeeGwynne.DualVolume` | 08 | OK | dualVolume = ‖e‖·vol_{d−1}(F)/d, matching the paper's ‖w−v‖·vol_{d−1}(H_e) = d·vol_d(Q_e) (rw-spheres.tex:741–743). |
| `BouRabeeGwynne.DualNull` | 08 | OK | Non-adjacent contacts have affine rank < d−1, so their dual cells are null; `IsCodimOneFacet` used correctly. |
| `BouRabeeGwynne.PyramidOverlap` | 08 | OK | Two pyramids from one apex overlap only over the cone on the common base; the overlap is null. |
| `BouRabeeGwynne.DualVolumeSums` | 08 | OK | Dual cells of distinct oriented edges have null overlap; the sum of dual volumes equals the volume of the union. |
| `BouRabeeGwynne.Section3InternalMass` | 08 | OK | Bad-column cylinder bounds, dual-volume identity and once-oriented mass convention are consistent. |
| `BouRabeeGwynne.Section3Accessibility` | 08 | OK | Positive projected-base measure gives positive-conductance exit paths; `BoundaryAccessible` matches its definition. |
| `BouRabeeGwynne.TilingDirichlet` | 08 | OK | The selected Dirichlet solution is unique on the closed region; values elsewhere are documented as unconstrained. |
| `BouRabeeGwynne.BoundarySampling` | 08 | OK | `Classical.choose` is used only through spec lemmas; the nearest closure point exists for nonempty U in a proper space. |
| `BouRabeeGwynne.BoundaryGeometry` | 08 | OK | Minimizing boundary samples lie on the frontier and within 2·mesh of the external vertex. |
| `BouRabeeGwynne.TheoremBStatement` | 08 | NOTE | Branch statements match the paper's (a)/(b); the ∀S clause is non-vacuous (checked); `toReal ⊤ = 0` in PaperRegularity clause (II) is harmless given `ApproximationCondition`. |
| `BouRabeeGwynne.Section3WellPosed` | 08 | OK | An accessible vertex forces a positive mesh; eventual unique Dirichlet extension as stated. |
| `BouRabeeGwynne.Section3PlanarTarget` | 08 | NOTE | Proves only the d = 2 instance of Theorem B(a), as its docstring says; premises are weaker than `TheoremBPartAStatement` at d = 2, so it is a stronger planar instance, not the general target. |
| `BouRabeeGwynne.Section3HarmonicIteration` | 09 | NOTE | Recursion trims with the newest replacement (region_{n+1} from value_n), not the printed one-step-lagged recursion h_{i+1}=H(S_i), S_{i+1}=trim(h_i); bounds are proved for the Lean recursion. |
| `BouRabeeGwynne.Section3MassDecay` | 09 | NOTE | Docstring says the contraction is "not supplied as a premise", but the energy bound `henergy` and `hfactor` are premises. |
| `BouRabeeGwynne.RadialBoundary` | 09 | OK | Ray-to-frontier witness; statement is what the docstring says, no junk values. |
| `BouRabeeGwynne.DualCoverage` | 09 | OK | Cone cover from interior apex; `cellPyramid`/`dualPolytope` match paper Q_e (rw-spheres.tex:728). |
| `BouRabeeGwynne.CellVolumeBound` | 09 | OK | vol(P_v) ≤ Σ dualVolume over all contacts and over adjacent contacts; nonadjacent contacts have zero dual volume. |
| `BouRabeeGwynne.Section3CellMass` | 09 | OK | Cell volume ≤ 2·incidentMass; `incidentMass` = Σ_e \|F_e\|\|e\| = Σ_e d·vol_d(Q_e) (matches rw-spheres.tex:742). |
| `BouRabeeGwynne.Section3GeometricCutoff` | 09 | NOTE | `geometricVolumeCutoff` uses ⌈·⌉₊ (0 for negative arguments); every lemma assumes 0 ≤ q and 1 ≤ K, so harmless. |
| `BouRabeeGwynne.Section3CaseII` | 09 | NOTE | `hvolume` uses `minTileVolume.toReal`, which is 0 for an empty tiling, so the hypothesis is false there (harmless); the general lemma takes `henergy` as a premise, which its docstring calls "upstream energy estimate". |
| `BouRabeeGwynne.Section3CaseIITarget` | 09 | NOTE | Conclusion is the qualitative convergence under (II), no rate (documented PARTIAL in README); `RegularityII` uses `mesh.toReal`, which is junk when mesh = ⊤, harmless given `happrox`. |
| `BouRabeeGwynne.BoundaryEdgeResponse` | 09 | OK | Responses are the exit probabilities for p(x,y)=a(x,y)/Σ_z a(x,z); they sum to 1 on A. |
| `BouRabeeGwynne.BoundaryTaylorCorrection` | 09 | NOTE | `dualEnergy` (DualDirichlet.lean:14) has junk x²/0 = 0; harmless because the corrected flux vanishes where a = 0 and `hsupport` is assumed. |
| `BouRabeeGwynne.FacetAffineResidual` | 09 | OK | Gradient variation controlled on the source cell only, as the docstring says. |
| `BouRabeeGwynne.LocalFacetResidual` | 09 | OK | Residual 3Mδ·area uses only the two endpoint diameters, as the docstring says. |
| `BouRabeeGwynne.CorrectedSurfaceField` | 09 | OK | Corrected flux = residual + Taylor reward, with consistent antisymmetry and support. |
| `BouRabeeGwynne.BoundaryCorrectedSurfaceEnergy` | 09 | OK | Energy ≤ 9M²δ²·incidentMass, the form of rw-spheres.tex:842. |
| `BouRabeeGwynne.BoundaryCorrectedIteration` | 09 | OK | Telescoping of the corrected error; hypotheses consistent. |
| `BouRabeeGwynne.HypIIICorrectedTrimming` | 09 | OK | Threshold KMδ, cutoff √(εδ); `hwidth` and `hsmall` give contraction 1/2; `hlength` uses 2ε as the docstring says. |
| `BouRabeeGwynne.RegionDiameter` | 09 | OK | `regionDiameter` is the max of cell diameters over A (0 on ∅); no junk. |
| `BouRabeeGwynne.HypIIICorrectedRegions` | 09 | OK | Each step uses the current region's corrected Dirichlet error and its actual maximum diameter. |
| `BouRabeeGwynne.HypIIIGeometricScale` | 09 | OK | `incidentScale` = sup over incident edges of (\|e\|·\|F\|)^α, the max in hypothesis (III) (rw-spheres.tex:271). |
| `BouRabeeGwynne.HypIIIRegionScale` | 09 | OK | Needs 0 < α, matching `RegularityIII`; conclusion is eventual emptiness, as stated. |
| `BouRabeeGwynne.HypIIITaylorCost` | 09 | OK | Constant 6 is documented as sufficient, not sharp. |
| `BouRabeeGwynne.HypIIICostSeries` | 09 | NOTE | `hypIIICost` uses `tsum`, which is 0 when not summable; every use carries `hypIIICost_summable` hypotheses, so no junk is reached. |
| `BouRabeeGwynne.HypIIICostBound` | 09 | OK | Finite partial sums ≤ `hypIIICost A (3M)`; the 6M → 2·(3M) rewrite is correct. |
| `BouRabeeGwynne.HypIIIErrorBound` | 09 | OK | `_of_mass_decay` takes `hmass` as a premise (documented); the main theorem discharges it via `correctedRegions_mass_le_geometric`. |
| `BouRabeeGwynne.Section3CaseIIITarget` | 09 | OK | Statement is the Dirichlet convergence claim under (III); `RegularityIII` matches rw-spheres.tex:271 (item diam). No nonvacuity example compiled for (III). |
| `BouRabeeGwynne.Section3TheoremBPartA` | 10 | OK | `theoremB_part_a` proves the Theorem B(a) target `TheoremBPartAStatement`; the statement is faithful to paper Theorem A (Dirichlet), item (a). |
| `BouRabeeGwynne.Section4BallHarmonicMeasure` | 10 | NOTE | Exit-measure lemmas are correct; `hcont : Continuous h` is an extra hypothesis the paper does not need (harmless for the collar-lemma user, which passes a polynomial `h`). |
| `BouRabeeGwynne.ClockedExcursionRange` | 10 | NOTE | `curveOscillationLe R` means "distance from the start is ≤ R", not pairwise oscillation; the stated constants `2r+2·mesh` are correct for that meaning. |
| `BouRabeeGwynne.SelectedExcursionOscillation` | 10 | NOTE | Same naming point (`curveOscillationLe`); Brownian `2r` and walk `2r+2·mesh` bounds are correct. |
| `BouRabeeGwynne.JointExcursionPasting` | 10 | NOTE | Same naming point; the `R + a + S` pasted-distance bound follows by the triangle inequality through start points. |
| `BouRabeeGwynne.ActualStoppedLawComparison` | 10 | NOTE | Statement is non-vacuous; junk values for non-exiting paths and `innerDomain U = univ` are harmless; the `mesh` parameter is a step bound (downstream instantiates it with `2·T.mesh`), not the tile mesh. |
| `BouRabeeGwynne.BrownianExitReference` | 10 | OK | Reference law, its probability property, and the absolute-continuity theorem match the docstrings. |
| `BouRabeeGwynne.ContinuityCells` | 10 | OK | Disjoint bounded measurable cells with null frontier and diameter `< ε` covering a compact set; no junk. |
| `BouRabeeGwynne.BrownianContinuityCells` | 10 | OK | One common cell family gives null exit-law mass on every cell frontier for every start in every `U j`; non-vacuous. |
| `BouRabeeGwynne.HarmonicCutoff` | 10 | OK | Compactly supported `C²` cutoff agreeing with `h` on an open neighbourhood of `K`; harmonicity transfers by locality. |
| `BouRabeeGwynne.HarmonicNearClosureBrownianExit` | 10 | OK | `HarmonicNearClosure` (`closure U ⊆ W`, `W` open) gives the Brownian harmonic exit representation; matches paper's Theorem A(a) mechanism. |
| `BouRabeeGwynne.Section4BrownianBallHarmonicMeasure` | 10 | NOTE | `brownianSpatialHarmonicMeasure` is total: for `z ∉ U` it is `δ_z` (harmless, all lemmas take `z ∈ U`); `hcont` is an extra global-continuity hypothesis. |
| `BouRabeeGwynne.PolynomialLaplacian` | 10 | OK | `polynomialLaplacian = ∑ ∂ᵢ∂ᵢ`, `polynomialSquaredNorm = ∑ Xᵢ²`; Euler-type identity for `Δ(\|x\|²p)` is the standard one. |
| `BouRabeeGwynne.PolynomialAnalyticLaplacian` | 10 | OK | `polynomialEval` is evaluation at coordinates; `Δ` is Mathlib's `InnerProductSpace.laplacian` (as in `IsHarmonicOn`), so the algebraic and analytic Laplacians agree. |
| `BouRabeeGwynne.PolynomialBoundaryApproximation` | 10 | OK | Stone–Weierstrass density of polynomials in `C(K)` for compact `K`; statement is `∀ x : K, \|p x − f x\| < ε`. |
| `BouRabeeGwynne.PolynomialDegree` | 10 | OK | Degree lowering and degree preservation of `q ↦ Δ(Aq)` for `deg A ≤ 2`; faithful. |
| `BouRabeeGwynne.PolynomialBallIdentity` | 10 | OK | A polynomial vanishing on a nonempty open ball is zero; `0 < r` is hypothesised and needed. |
| `BouRabeeGwynne.Upstream.KolmogorovExtension` | 10 | OK | Vendored Degenne–Pfaffelhuber projective limit; standard Kolmogorov extension, probability instance needs `Nonempty ι` (present). |
| `BouRabeeGwynne.BrownianProjectiveLaw` | 10 | OK | `brownianProjectiveLaw` is the projective limit of Mathlib's `BrownianReal.projectiveFamily` (centred Gaussian, covariance `min(s,t)`); `IsPreBrownianReal` is Mathlib's notion; continuity is not claimed. |
| `BouRabeeGwynne.Upstream.BrownianMotion.Continuity.KolmogorovChentsov` | 10 | NOTE | Statements and the `holderSet`/`holderModification` definitions match Kolmogorov–Chentsov; `holderModification` takes the junk value `hE.some` off `U` (harmless, only `t ∈ U` is asserted). Proofs skimmed, not read. |
| `BouRabeeGwynne.BrownianContinuousLaw` | 11 | NOTE | Continuous modification is `Exists.choose`; only `choose_spec` is used, so the choice is harmless. |
| `BouRabeeGwynne.EuclideanWienerLaw` | 11 | OK | `euclideanWienerLaw d` is the image of the product of d real Wiener laws; `isStandardBrownianLaw_euclideanWienerLaw` is the Brownian nonvacuity witness. |
| `BouRabeeGwynne.PolynomialDirichlet` | 11 | OK | Ball factor evaluates to r^2 - ‖x-c‖^2, Dirichlet operator is Δ(A·q); the standard-law premise of injectivity is witnessed. |
| `BouRabeeGwynne.HarmonicPolynomialApproximation` | 11 | OK | Continuous sphere data approximated by globally harmonic polynomials, plus a closed δ-collar; statements match docstrings. |
| `BouRabeeGwynne.Section4BallExitConvergence` | 11 | NOTE | Main ball-exit estimate is correct and jointly satisfiable; `hreg` carries the `toReal` junk of `RegularityII` (PaperObjects.lean:207-213), harmless here because `ApproximationCondition` forces finite mesh. |
| `BouRabeeGwynne.Section4BrownianBallKernel` | 11 | OK | Weak continuity of z ↦ Brownian ball-exit law on the ball, from harmonic approximants. |
| `BouRabeeGwynne.Section4UniformExitTopology` | 11 | OK | Uniform bounded-test convergence plus a continuous kernel on a compact space gives uniform Lévy–Prokhorov convergence; matches docstring. |
| `BouRabeeGwynne.Section4BallExitLevyProkhorov` | 11 | NOTE | LP convergence is stated only for starting points in a compact K ⊆ ball (as the docstring says), not for the full-ball claim of Prop 4.2; `hreg` junk as above. |
| `BouRabeeGwynne.Section4UniformExitCells` | 11 | OK | Mass comparison on common null-frontier cells; the nearby-start modulus is chosen before the eventual index. |
| `BouRabeeGwynne.Section4BallExitCouplingInputs` | 11 | NOTE | Quantifier order is correct (δ before the eventual index); compact-K restriction and `hreg` junk as above. |
| `BouRabeeGwynne.BackwardExitPartitions` | 11 | NOTE | Backward choice of cells and moduli, one eventual index for all stages and balls, is correct; `hreg` junk as above. |
| `BouRabeeGwynne.AmbientExitPartitions` | 11 | NOTE | Transfer to one ambient network is correct; `hreg` junk as above. |
| `BouRabeeGwynne.StoppedTilingWalkLaw` | 11 | OK | Existence of the stopped tiling walk law, and Dirac at the constant curve when the start is outside U; matches `IsStoppedTilingWalkLaw`. |
| `BouRabeeGwynne.AmbientStoppedWalkLaw` | 11 | OK | Stopped-curve law equals the ambient walk law; curve stops at the U-set, which is the intended convention. |
| `BouRabeeGwynne.BoundarySurvivalScales` | 11 | OK | Scalar selection with concrete satisfying instance (compiled). |
| `BouRabeeGwynne.BrownianNestedClock` | 11 | OK | Nested clock equals the first exits of the nested sets, including infinite exit times; range inclusions correct. |
| `BouRabeeGwynne.SkeletonSurvival` | 11 | OK | Multiplicative survival bound on good histories; `survivalUpTo` is the intended event. |
| `BouRabeeGwynne.BrownianNestedSurvival` | 11 | NOTE | `uniform_brownian_nested_survival` also quantifies over δ ≤ 0, where `cthickening δ U` is `closure U`; these instances are implied by δ > 0 and the bound stays true. |
| `BouRabeeGwynne.BrownianExitRangeComparison` | 11 | OK | Exit-time comparisons and closed-collar inclusion; matches docstring. |
| `BouRabeeGwynne.BrownianNestedConfinement` | 11 | OK | Nested survival controls the whole outer-stopped path; `N - 1` is guarded by `0 < N`. |
| `BouRabeeGwynne.BrownianStoppingEvent` | 11 | OK | Strong-Markov transfer bound; finiteness is a.s., so the ⊤ totalization is null. |
| `BouRabeeGwynne.BrownianExitInterval` | 11 | OK | Both endpoints of [τ, next exit] lie in the excursion range; 2η bound correct. |
| `BouRabeeGwynne.BrownianStoppingOscillation` | 11 | OK | η-confinement of a fresh path gives 2η-oscillation on [τ, next exit] except on probability ≤ ε. |
| `BouRabeeGwynne.BrownianBoundaryOscillation` | 11 | NOTE | `innerDomain` is junk (`infDist x ∅ = 0`) when Uᶜ = ∅; excluded by the bounded-U hypothesis; ⊤ exit times are μ-null. |
| `BouRabeeGwynne.BrownianSkeletonOscillation` | 11 | OK | Transfer of the oscillation bound to the skeleton representation; bound ε + r is correct. |
| `BouRabeeGwynne.BrownianFiniteProbability` | 11 | OK | Quantifier order matches docstring: boundary cutoff a, then (ε, δ, W, r), then stage count K, then G, z, j₀, selector, P. |
| `BouRabeeGwynne.BrownianUniformFiniteProbability` | 11 | OK | Same statement with the label type J quantified after a; a stronger form. |
| `BouRabeeGwynne.CouplingErrorBudget` | 12 | NOTE | Arithmetic budget lemmas are correct; `hr : 0 < r` in `exists_coupling_stopped_error_budget` is unused (harmless). |
| `BouRabeeGwynne.CouplingNeighborhoods` | 12 | OK | Finite r/4-cover of the δ-thickening inside a compact Q with balls inside W, as intended; satisfiable. |
| `BouRabeeGwynne.CouplingPartitions` | 12 | NOTE | Index-`⊤` σ-algebra is the discrete one (finite `centers`); docstring "selectors are total" holds only on `C` (statement: `∀ x ∈ C, select i x ≠ none`). |
| `BouRabeeGwynne.NearestCouplingStarts` | 12 | OK | Eventual nearest-start approximation in the fixed inner ball, uniform in the start; matches docstring. |
| `BouRabeeGwynne.StandardBrownianProbabilityMeasure` | 12 | OK | Bundles `euclideanWienerLaw` as a `ProbabilityMeasure` that is a standard Brownian law; nonvacuous (compiled). |
| `BouRabeeGwynne.TheoremACouplingSetup` | 12 | NOTE | Bounds hold for all `z ∈ U` and all `j₀` (no `z ∈ ball j₀` hypothesis): stronger than the one use; `μ.map` is of a measurable map, so no junk 0. |
| `BouRabeeGwynne.TheoremAProcessLaws` | 12 | OK | Standard BM with a.s. finite exit and probability stopped laws; `IsStoppedTilingWalkLaw` pins the walk law (no junk satisfier). |
| `BouRabeeGwynne.TheoremAStatement` | 12 | NOTE | Matches paper Thm A (lines 259–277) except the ambient collar `closure U ⊆ interior D` (strictly stronger hypothesis; README correction 1 gives the counterexample refuting the printed `closure U ⊆ D`). |
| `BouRabeeGwynne.WalkEdgeSupport` | 12 | OK | Step bound `2·mesh.toReal` is guarded by `mesh ≠ ∞`; positive-conductance step lemma correct. |
| `BouRabeeGwynne.TilingStoppedLawComparison` | 12 | NOTE | `innerDomain U ε` is `∅` (not `univ`) when `Uᶜ = ∅` (Mathlib `infDist _ ∅ = 0`); harmless since every use has bounded `U`. |
| `BouRabeeGwynne.UniformStoppedWalkConvergence` | 12 | OK | Final uniform Lévy–Prokhorov estimate over every ν satisfying `IsStoppedTilingWalkLaw`; matches Thm A's uniform-in-z claim. |
| `BouRabeeGwynne.TheoremAProved` | 12 | OK | `theoremA_proved : TheoremAStatement`; axioms are only `propext`, `Classical.choice`, `Quot.sound`; premises jointly satisfiable (compiled instance). |
| `BouRabeeGwynne.Upstream.BrownianMotion.Auxiliary.Algebra` | 12 | OK | Generic monotonicity and finrank lemmas; side conditions (`0 ≤ c`, `c ≠ 0`, `Nontrivial`) present. |
| `BouRabeeGwynne.Upstream.BrownianMotion.Auxiliary.DenseCountable` | 12 | NOTE | `denseCountable` is an `Exists.choose` countable dense set; only density and countability are used. |
| `BouRabeeGwynne.Upstream.BrownianMotion.Auxiliary.ENNReal` | 12 | OK | Statements hold at the `0`/`⊤` junk points; side conditions (`p ≠ ⊤`, `0 < x`) present. |
| `BouRabeeGwynne.Upstream.BrownianMotion.Auxiliary.FiniteInf` | 12 | OK | Every `max'`/`min'`/`⨆`/`⨅` lemma that fails on `∅` carries nonemptiness. |
| `BouRabeeGwynne.Upstream.BrownianMotion.Auxiliary.MeanInequalities` | 12 | OK | Jensen/Hölder and Minkowski bounds, ENNReal corners (`μ univ = ⊤`, `∫f^r = 0`) checked. |
| `BouRabeeGwynne.Upstream.BrownianMotion.Auxiliary.MeasureTheory` | 12 | NOTE | Junk-0 conventions for `condExp` and variance are harmless (statements stay true); `measure_closeBall_const` has a typo in two names. |
| `BouRabeeGwynne.Upstream.BrownianMotion.Auxiliary.Metric` | 12 | OK | `IsSeparated` is strict in Mathlib, so `disjoint_closedBall` is correct, including `ε = ⊤`. |
| `BouRabeeGwynne.Upstream.BrownianMotion.Auxiliary.Nat` | 12 | OK | Single lemma `pow_two_mul_abs`, true for all `n`; file name is misleading. |
| `BouRabeeGwynne.Upstream.BrownianMotion.Auxiliary.Topology` | 12 | OK | Hölder lemmas carry the needed side conditions (`0 < r`, bounded space, bounded set). |
| `BouRabeeGwynne.Upstream.BrownianMotion.Continuity.Chaining` | 12 | NOTE | Junk branches of `nearestPt` and the truncated `k - (n+1)` index are never reached by the lemmas that use them. |
| `BouRabeeGwynne.Upstream.BrownianMotion.Continuity.CoveringNumber` | 12 | NOTE | Uses Mathlib's `coveringNumber`; `EMetric.isCover_iff_subset_iUnion_closedBall` is misnamed (it is about `closedEBall`); the ε ≤ 1 bound needs `ε ≤ 1`. |
| `BouRabeeGwynne.Upstream.BrownianMotion.Continuity.HasBoundedInternalCoveringNumber` | 12 | NOTE | `HasBoundedCoveringNumber` quantifies over `ε ∈ ℝ≥0` including `0` (docstring says `(0, diam]`); the extra clause is stronger only for finite sets with `d ≤ 0`. |
| `BouRabeeGwynne.Upstream.BrownianMotion.Continuity.IsKolmogorovProcess` | 12 | NOTE | Only `Cp` is defined here (a max of two positive constants for `d < q`, `⊤` otherwise); the Kolmogorov notions are Mathlib's, and the estimates are conservative. |
| `BouRabeeGwynne.Upstream.BrownianMotion.Continuity.KolmogorovChentsovInequality` | 13 | NOTE | `constL` junk values (`ofReal` truncation, `c.toReal` at `c = ⊤`/`c = 0`, ENNReal `∑'`) all harmless; statements match the Kolmogorov–Chentsov bound; depends on `HasBoundedCoveringNumber` whose `ε = 0` clause is harmless only for `0 < d` (all batch statements assume it). |
| `BouRabeeGwynne.Upstream.BrownianMotion.Continuity.LimitModification` | 13 | OK | `indicatorProcess` and `IsLimitOfIndicator` mean what their docstrings say; all `limUnder` uses sit under existence hypotheses or are measurability-only; nonvacuity compiled. Header copyright year (2026) differs from the other files (2023/2025); cannot be checked offline. |
| `BouRabeeGwynne.Upstream.BrownianMotion.Gaussian.StochasticProcesses` | 13 | OK | Four standard modification/indistinguishability lemmas with the right hypotheses (separability, continuity a.s., open `U`); no junk values. |
| `BouRabeeGwynne.Upstream.KolmogorovExtension.CompactSystem` | 13 | OK | `IsCompactSystem` (Mathlib `dissipate` form), `allProj`, `indexProj`, `projCylinder`, `piCylinderSet` match their docstrings; `isCompactSystem_closedCompactCylinders` is the stated theorem; `Classical.choose` only picks representations that are used consistently. |
| `BouRabeeGwynne.Upstream.KolmogorovExtension.RegularContent` | 13 | OK | Standard regular-content lemmas (decreasing sets with empty intersection tend to 0; σ-additivity under finiteness and inner regularity); no finiteness needed for the first; hypotheses satisfiable on paper, not instantiated in Lean. |
| `SpherePackings.Support.Section4.AmbientExitPartitions` | 14 | OK | One statement; quantifiers and the ambient/Brownian comparison match the docstring; hypotheses are only the documented ambient collar and localized Assumption D. |
| `SpherePackings.Support.Section4.AssumptionD` | 14 | NOTE | `TilingAssumptionD` is the documented localization of Assumption D and is satisfiable (Example 1); two out-of-batch docstrings are stale. |
| `SpherePackings.Support.Section4.BackwardExitPartitions` | 14 | OK | Partitions and moduli are chosen before the eventual index; ℕ-subtractions are exact because indices are bounded; matches docstring. |
| `SpherePackings.Support.Section4.BallExitConvergence` | 14 | OK | Test-function convergence is uniform over all interior vertices; the integrals are not junk. |
| `SpherePackings.Support.Section4.BallExitCouplingInputs` | 14 | OK | Modulus δ is quantified before `∀ᶠ n` in both lemmas, as the docstrings say; the cell lemma's modulus is not partition-independent, as documented. |
| `SpherePackings.Support.Section4.BallExitLevyProkhorov` | 14 | NOTE | Compact-K LP lemma matches its docstring (this is the weaker lemma behind Prop 4.2(b)); the `toReal` in `levyProkhorovDist` cannot see `⊤` for probability measures. |
| `SpherePackings.Support.Section4.CouplingPartitions` | 14 | OK | Partitions, selectors and δ₀ precede `∀ᶠ n`; starts are uniform; margin and non-termination conditions match the docstring; the `⊤` instance on `Option` is correct for a finite index set. |
| `SpherePackings.Support.Section4.HarmonicMeasure` | 14 | NOTE | Both statements match their docstrings; `hDomain` is an unused hypothesis in the first lemma (harmless). |
| `SpherePackings.Support.Section4.Prop42` | 14 | ISSUE | `prop42_assumptionD` is labelled Proposition 4.2, but part (b) is uniform only over compact `K ⊂ ball`; the paper claims `sup` over the open unit ball. |
| `SpherePackings.Support.Section4.Theorem41` | 14 | OK | Conclusion is Theorem A's conclusion with `TilingAssumptionD`; the restriction to orthogonal tilings is stated in the header and registered as weakened; `theoremA_of_theorem41` discharges the hypothesis via Theorem B(a). |
| `SpherePackings.Support.Section4.UniformStoppedWalkConvergence` | 14 | NOTE | Statement is faithful (uniform over `z ∈ U` and over all walk laws satisfying the predicate); the main lemma has no docstring; ℕ-subtraction in `brownianSelectorForWalk` aliases index 0 (proof-only, harmless). |
| `SpherePackings.General.MarkovChain.Basic` | 15 | OK | Chain law, Markov property and first-step decomposition mean what they say; no junk values. |
| `SpherePackings.General.MarkovChain.Absorbed` | 15 | NOTE | `absorbedKernel` and the strong Markov property are as intended; `observedHistory`/`futureAt` junk values sit only on `{τ = ⊤}`, excluded by `hfin`. |
| `SpherePackings.General.MarkovChain.Dirichlet` | 15 | NOTE | `exitValue`, `survival`, `SolvesDirichlet` mean what they say; uniqueness hypotheses quantify over all of `V`, so they are stronger than they look; `exitVertex` junk is guarded. |
| `SpherePackings.General.NearestNeighbourWalk` | 15 | NOTE | `inner`/`boundary` match `V_n[S]`/`∂V_n[S]`; the kernel is arbitrary (paper's walk is the conductance walk); `harmonicMeasure` is a sub-probability measure and is `δ_a` for `a ∉ inner S`. |
| `SpherePackings.General.NearestNeighbourWalkHarmonic` | 15 | NOTE | Identity with the absorbed-chain harmonic measure is correct under the a.s.-exit hypothesis; the outside-batch `MarkovChain.discreteHarmonicMeasure` puts non-exit mass on the start vertex, which `hexit` excludes. |
| `SpherePackings.General.LevyProkhorovTest` | 15 | NOTE | Test-family statement matches its docstring and is satisfiable; `tent`/`farCutoff` have `x/0 = 0` junk for `ρ ≤ 0` and `farCutoff ≡ 0` on `∅`, all excluded by hypotheses. |
| `SpherePackings.Support.LevyProkhorovIntegral` | 15 | OK | Oscillation bound `δ + 2ε‖f‖` under `levyProkhorovEDist < ε` for bounded continuous `f`; constants and strictness correct. |
| `SpherePackings.Support.MeasureOverlap` | 15 | OK | Bounded-overlap union bound; the `ncard` set is a subset of a `Finset`, so there is no infinite-set `ncard = 0` junk. |
| `SpherePackings.General.Walk.ActualStoppedLawComparison` | 16 | NOTE | Comparison is true as stated; `η` unconstrained (harmless); no finite-exit hypothesis for `U`, so stopped laws are totalized on the never-exit event |
| `SpherePackings.General.Walk.ActualWalkSkeleton` | 16 | OK | Stage/clock measurability and a.s. finiteness of all clocks (derived from `hexit`); lemmas only |
| `SpherePackings.General.Walk.BallStoppedLawComparison` | 16 | OK | Inner-margin selector hypothesis is exactly `dist x c_j ≤ r/2`; shape and Brownian bounds match docstring; instantiated by Theorem41 |
| `SpherePackings.General.Walk.CanonicalStoppingRange` | 16 | OK | Range-to-canonical-support lemma matches its docstring; `hselect` has the right direction |
| `SpherePackings.General.Walk.ClockedWalkExcursion` | 16 | OK | Clocked-excursion kernel identities; junk `untopD 0` is consistent on both sides |
| `SpherePackings.General.Walk.DiscreteHarmonicMeasure` | 16 | NOTE | `discreteHarmonicMeasure` equals the harmonic measure only under the a.s. exit hypothesis (junk `ω 0` on never-exit); all theorems carry `hexit` |
| `SpherePackings.General.Walk.ExcursionEndpointExtension` | 16 | NOTE | Unused lemma `measurableEmbedding_finite_positions` is misnamed; `nextVertexExcursionKernel` is unused in the repo; `finiteVertexKernelExtension` name says "finite" but is general |
| `SpherePackings.General.Walk.ExcursionSteps` | 16 | NOTE | `curveOscillationLe R` means radius about the start, not oscillation/diameter; the 2R step bound uses that reading correctly |
| `SpherePackings.General.Walk.FiniteStoppedLawComparisonGood` | 16 | OK | Walk-support hypothesis required only on the good event, as documented; `η` unconstrained as in ActualStoppedLawComparison |
| `SpherePackings.General.Walk.FreeAbsorbed` | 16 | OK | Free-chain and absorbed-chain identities; hypotheses are the right ones (`B ⊆ A`, stop-invariance) |
| `SpherePackings.General.Walk.GoodRange` | 16 | OK | Good-pair range bound `max R₀ (2a+S)` and ball-shape bound match docstrings |
| `SpherePackings.General.Walk.HarmonicMeasureBridge` | 16 | OK | Endpoint law equals harmonic measure (unconditional); Dirichlet error bounds (`≤` and strict `<`) are correct |
| `SpherePackings.General.Walk.JointExcursionPasting` | 16 | OK | Almost-sure structure, walk-range and pasting statements match docstrings |
| `SpherePackings.General.Walk.SkeletonKernels` | 16 | NOTE | `vertexKernelExtension` is an unused duplicate of `finiteVertexKernelExtension`; the module docstring points at it as the one in use |
| `SpherePackings.General.Walk.StoppedCurveMeasurable` | 16 | NOTE | `untopD 0` gives duration 0 on never-exit paths; every law statement using it carries `hexit`, so the value is on a null set; measurability unaffected |
| `SpherePackings.General.Walk.WalkAbsorption` | 17 | OK | Absorption locality and clocked-excursion identity; statements match docstrings, and the `⊤`-exit convention is shared by both sides. |
| `SpherePackings.General.Walk.WalkAdaptiveStopping` | 17 | OK | Prefix-invariance criterion gives a stopping time; the measurability hypothesis for adaptive exits is explicit and documented. |
| `SpherePackings.General.Walk.WalkBrownianActiveTransfer` | 17 | OK | Pure coupling inequality P(walk active at K) ≤ P(Brownian active at K) + P(first failure); matches docstring; `hexit` present. |
| `SpherePackings.General.Walk.WalkBrownianCellMeasures` | 17 | NOTE | Cell masses equal harmonic/Brownian masses; `discreteHarmonicMeasure` puts escape mass on the start vertex, so it equals the hitting law only under `hexit`. |
| `SpherePackings.General.Walk.WalkBrownianCoupling` | 17 | NOTE | Coupling objects are genuine finite-partition couplings; the `brownianSelectorForWalk 0` ℕ-subtraction value is never read; marginal identification needs `hexit`. |
| `SpherePackings.General.Walk.WalkBrownianFailure` | 17 | NOTE | The `(k+1)b` first-failure bound is true as stated, but `herror` quantifies over every cell vertex (including vertices outside `B j`, where it is false), with no `hexit` and no `B`/`U` link. |
| `SpherePackings.General.Walk.WalkBrownianStep` | 17 | NOTE | One-step bad-mass bounds are correct; `herror` at the walk's current vertex is satisfiable only when that vertex lies in `B j` (same caveat as WalkBrownianFailure). |
| `SpherePackings.General.Walk.WalkCanonicalStopping` | 17 | NOTE | Docstring says the support is "measurable on the rich walk marginal"; the theorem is an a.e. membership statement. |
| `SpherePackings.General.Walk.WalkExcursionKernel` | 17 | NOTE | Escaping paths totalize to the constant path at the start (duration 0), giving an atom of mass `P_v(exit = ⊤)`; statements are unconditional and consistent, and match the paper's stopped law only under `hexit`. |
| `SpherePackings.General.Walk.WalkPathStopping` | 17 | OK | Measurability of the stopped path and stopped history; no new definitions. |
| `SpherePackings.General.Walk.WalkReconstructionLaw` | 17 | OK | Lévy–Prokhorov bound between the actual stopped curve law and the reconstructed law, by `P(active at n) ≤ r`; `hexit` and `hselect` present. |
| `SpherePackings.General.Walk.WalkSelectedRestart` | 17 | OK | Restart kernel is the selected kernel pulled back to the observed terminal vertex; the joint-law identity matches its docstring. |
| `SpherePackings.General.Walk.WalkSkeletonKernel` | 17 | NOTE | Off-graph values of `spatialClockedExcursionKernel` are constant placeholders; walk histories never reach them. |
| `SpherePackings.General.Walk.WalkSkeletonLaw` | 17 | OK | The actual rich excursion sequence has the trajectory law of the skeleton kernel (`hexit` present); definitions match the walk stages. |
| `SpherePackings.General.Walk.WalkSkeletonObservation` | 17 | OK | Recovery of the observed past from the stage prefix; hypotheses explicit. |
| `SpherePackings.General.Walk.WalkSkeletonPrefix` | 17 | NOTE | Clock and knot identities hold; the ℕ-subtraction duration in `clockedWalkSegment` is the true duration only under the monotonicity that the `hfinite` hypothesis supplies. |
| `SpherePackings.Support.Section4General.AssumptionD` | 18 | NOTE | Matches Assumption D (paper 1438–1462); (4.2) quantifies over every discrete solution, so it is vacuous at an index with no solution (the paper presupposes existence). Not a defect of the theorems. |
| `SpherePackings.Support.Section4General.BallExitInputs` | 18 | OK | Quantifier order and the LP/exit-law statements match their docstrings; LP correctly compares sub-probability harmonic measures. |
| `SpherePackings.Support.Section4General.CouplingPartitions` | 18 | NOTE | Bound `(K+1) * ofReal b` matches its docstring; file-local `⊤` σ-algebra on `Option` is harmless on the finite codomain. |
| `SpherePackings.Support.Section4General.ExitPartitions` | 18 | OK | Backward stage construction and the uniform eventual comparison match the docstring; no junk values. |
| `SpherePackings.Support.Section4General.NearestStarts` | 18 | OK | (4.1) consequence and the nearby-start statement match their docstrings; `≤ δ₀` with `δ₀ > 0`. |
| `SpherePackings.Support.Section4General.Prop42` | 18 | NOTE | Matches paper Prop 4.2 (1511–1516); the explicit hypothesis `closedBall c r ⊆ cthickening δ D` is the correct reading of the unit-ball claim, which the printed statement leaves implicit. |
| `SpherePackings.Support.Section4General.StoppedWalkLaw` | 18 | NOTE | Stopped walk law matches the paper; never-exit paths use a constant-curve convention, harmless given `eventually_ae_exit`; docstring says `U ⊆ D`, statement assumes `U ⊆ cthickening δ D`. |
| `SpherePackings.Support.Section4General.Theorem41` | 18 | NOTE | Theorem 4.1 (1481–1488) matches the paper; the Brownian stopped law has a μ-null junk value (`toNNReal ⊤ = 0`) that cannot change the law for bounded `U`. |
| `SpherePackings.Support.Guards.TilingWalk` | 18 | NOTE | Conductance walk matches paper 233–236 on active vertices; the absorbing convention for inactive vertices is not proved unused for the witness; `walkWeight` junk `0` is unreachable. |
| `SpherePackings.Support.Guards.AssumptionDLattice` | 18 | NOTE | Witnesses are sequences of finite graphs on `ball 0 2`; the Theorem 4.1, Prop 4.2 and coupling bundles are nonvacuous (compiled examples below). |
| `SpherePackings.Support.Section2.DualVariational` | 19 | OK | `IsIncidentEdge` is `E[Ā]`; Lemma 2.3 matches (`f = 0` off `A` is WLOG). |
| `SpherePackings.Support.Section3.ComponentArith` | 19 | OK | Pure real arithmetic for the component case analysis; no junk values, hypotheses satisfiable. |
| `SpherePackings.Support.Section3.ComponentChain` | 19 | OK | `adjGraphIn` is facet adjacency inside `S`; the chain bound is an upper bound by the list sum of diameters. |
| `SpherePackings.Support.Section3.ComponentLaplacian` | 19 | OK | `Δ|·−z|²` and the Taylor bound for `C²` functions on edge segments; neighbours of `V[U]` lie in `V̄[U]`, so the restricted network is faithful. |
| `SpherePackings.Support.Section3.DecayRateArith` | 19 | OK | `hypIIIRateConstant` is junk-free for `0 < r < 1`; `1 ≤ M` is the paper's `M := sup|∇²h_C| ∨ 1` (tex 1328). |
| `SpherePackings.Support.Section3.DecaySegment` | 19 | NOTE | `hypIIICost` is a `tsum` (0 if not summable); summability follows from the hypotheses, so the statements are meaningful. |
| `SpherePackings.Support.Section3.EnergyMinimal` | 19 | NOTE | Corrected Proposition 2.6 and Proposition 3.2 match the paper; sums use one consistent undirected convention, and the Prop 3.2 threshold is at least as strong as printed. |
| `SpherePackings.Support.Section3.GeneralDecayRate` | 19 | OK | Theorem 3.7 with rate matches the paper; `M ≥ 1` is the paper's `∨ 1`; decay hypothesis is the paper's up to the `d^α` rescaling of `F` (documented). |
| `SpherePackings.Support.Section3.GeneralRateFull` | 19 | OK | Theorem 3.6 matches the paper (`M ≥ 1`, `K ≥ 1`, `D` as sup over connected sets of small cells); smallness is an explicit `C`. |
| `SpherePackings.Support.Section3.PlanarCuts` | 19 | ISSUE | Docstring says "Y meets the line in measure ≤ ℓ", but the hypothesis is `μHE[1] Y ≤ ℓ` on the whole set `Y`; strictly stronger, no effect on the use site. |
| `SpherePackings.Support.Section3.PlanarRateFull` | 19 | ISSUE | Theorem 3.3 carries the extra vertex-Lipschitz hypothesis `hLip`, which the printed `L = sup|∇h_C|` does not imply; this is open and disclosed (frozen statement, README PARTIAL). |
| `SpherePackings.Support.Section3.PlanarQuadratic` | 20 | NOTE | No `def`s. The box lemma and both Theorem 3.3 statements match their docstrings and the corrected Proposition 2.6 hypotheses; the paper's `V[U]`, `Û`, `ε`, `M`, `h_D` are reproduced; the bundle of both theorems is satisfiable on a lattice tiling (compiled). Notes: `ε ≤ 1/2` restriction, extra `Fintype` hypothesis, `V[U]` read as `{pos ∈ U}`, exponent 1/2 not sharp for this bound. |
| `SpherePackings.Support.Poisson.Basic` | 21 | NOTE | `IsPoissonPointProcess` admits Lebesgue intensity (by reasoning); `ncard` junk on unbounded sets (docstring overclaims, harmless); unsatisfiable for atomic intensities (compiled).  *Action:* the definition now also asks that sets of finite intensity carry almost surely finitely many points (`ae_finite`), and the atom-free scope of Proposition 1.1 is documented in `CORRESPONDENCE.md` |
| `SpherePackings.Support.Poisson.Tails` | 21 | OK | Poisson tail estimates match display (5.2); only bounded sets used |
| `SpherePackings.Support.Voronoi.PoissonCells` | 21 | NOTE | `voronoi_cells_between_balls` matches corrected Prop 1.1; vacuous for an intensity with an atom outside `W` (documented in `CORRESPONDENCE.md`) |
| `SpherePackings.Support.Counterexample.Construction` | 21 | OK | `SpherePacking`, `Tangent`, `tangentHalfspace`, `Covered`, centres, radii, `levelValue` mean what they say; the `d ≥ 4` parity restriction is documented and checked |
| `SpherePackings.Support.Counterexample.Covering` | 21 | OK | `packing_covered`: every sphere of the dimension-3 packing is covered; non-vacuous (a lone sphere is not covered, compiled) |
| `SpherePackings.Support.Section2.DualCoverage` | 21 | NOTE | corrected Lemma 2.5 as documented; `interiorVertices` is `pos ∈ U`, not `pos ∈ interior U`; reading of `E[Ū]` |
| `SpherePackings.Frozen.Lemma51Inner` | 21 | NOTE | corrected 5.1(a): hypothesis on every grid cube meeting `U`, closed-ball conclusion; both documented |
| `SpherePackings.Frozen.Theorem61Counterexample` | 21 | OK | existential statement as printed; non-vacuous: Wiener measure is a standard Brownian law (compiled), and the Brownian target is a genuine probability measure |
| `SpherePackings.Support.Complete.Basic` | 22 | NOTE | `CompleteCell` and `dual_coverage_complete` match corrected Corr. 4 and Lemma 2.5; `V[U] = {pos ∈ U}` equals the paper's interior convention only for open `U` |
| `SpherePackings.Support.Complete.Fibers` | 22 | OK | statements only; a.e. nondegenerate fibres over the projected base, as used by Columns/GaussGreen |
| `SpherePackings.Support.Complete.GaussGreen` | 22 | OK | upper/lower neighbour finsets are strict-sign filters; Gauss–Green for complete cells (statements) |
| `SpherePackings.Support.Complete.Columns` | 22 | NOTE | column bad set uses projected cells `y ∈ π(P_v)` instead of the paper's `L_y^{(j)}` (contact projections); equal up to a null set, Lean set larger; `π_j(U)` restriction absent |
| `SpherePackings.Support.Complete.Section3` | 22 | OK | statements only; hypotheses are quantitative and jointly satisfiable (small `ε`, large `K`); no junk values reached |
| `SpherePackings.Support.Section2.AffineKernel` | 22 | OK | `discreteLaplacian_affine_eq_zero_of_complete` matches corrected Lemma 2.2 ("at every vertex with a complete cell") |
| `SpherePackings.Support.Section3.TaylorEnergy` | 22 | OK | `taylor_of_segment` (sharp `M/2`) and flux residual bounds (`3Mε`) check out by hand; interior-cell versions are intermediate, documented as such |
| `SpherePackings.Support.Section3.EnergyComplete` | 22 | NOTE | Props 2.6/3.2 match corrected Taylor/Hessian hypotheses but are sharper (harmonicity and Hessian only on `V[U]` cells); header's "half the printed (stronger)" is relative to printed sums, not to corrected Corr. 4; `Fintype` extra |
| `SpherePackings.Support.Section3.InternalTaylor` | 22 | OK | internal-edge Taylor bounds (`2Mδ²`, `9M²δ²`) and comparison principle `abs_le_of_abs_laplacian_le` (checked by hand) |
| `SpherePackings.Support.Section3.DecayInternal` | 22 | OK | `generaldim_decay_rate_internal` matches corrected `theorem:generaldim-decay` (M = M_U°∨1, internal Taylor, decay hypothesis up to `F ↦ F d^α`) |
| `SpherePackings.Support.Voronoi.GeometricConstraint` | 22 | NOTE | (a) and (b) match corrected Lemma 5.1; closed thickenings and closed balls (absorbed by `∃ R`; closed balls strengthen (a)); arbitrary `U`, `S` |
| `SpherePackings.Support.Voronoi.CountsToCells` | 22 | OK | composition of Lemma 5.1 with cube counts; hypothesis `min δ (1/4) k ≤ δ k` used correctly |
| `SpherePackings.Support.Voronoi.PoissonLocal` | 22 | NOTE | Prop 1.1 local statements match corrected; `hlf` (sure local finiteness) and `IsDomain` are extra hypotheses; no Poisson process exists in the repo |
| `SpherePackings.Frozen.Lemma22AffineKernel` | 22 | OK | matches corrected Lemma 2.2; the compiled instance on `GT` (Nonvacuity) typechecks |
| `SpherePackings.Frozen.Lemma25DualCoverage` | 22 | NOTE | matches corrected Lemma 2.5; `.olean` (10:59) predates source (11:56), current source elaborates (checked) |
| `SpherePackings.Frozen.Lemma31Poincare` | 22 | NOTE | matches corrected Lemma 3.1 except `π_j(U)` dropped and projected-cell column set (both give a stronger claim); undirected sums per corrected Corr. 4 |
| `SpherePackings.Frozen.Prop26Energy` | 22 | NOTE | matches corrected Prop 2.6 hypotheses but harmonicity and Hessian bound only on `V[U]` cells (corrected: `Ĝ_U`), so stronger; header does not say so; `Fintype` extra |
| `SpherePackings.Frozen.Prop32Columns` | 22 | NOTE | as Prop 2.6 plus the column-set and `π_j(U)` points; threshold equals corrected Prop 3.2 (undirected sums) |
| `SpherePackings.Frozen.Theorem37Rate` | 22 | NOTE | matches corrected `theorem:generaldim-decay`; smallness `12Mε ≤ 1, ε ≤ 1/2` is implied by the paper's `ε < (CM)⁻¹` with C = 12; `Fintype` extra; G4 not re-verified |
| `SpherePackings.Frozen.Lemma51Outer` | 22 | OK | matches corrected Lemma 5.1(b); printed-radius counterexample checked by hand (holds iff d ≥ 13); compiled nonvacuity instance (`δℤ²`) |
| `SpherePackings.Frozen.Prop11Cells` | 22 | OK | matches corrected Prop 1.1 first part; exponents `βp = β⁺`, `βm = β⁻`; `HolderMassBounds` on open `W ⊇ closure U`; no PPP exhibited (see nonvacuity) |
| `SpherePackings.Frozen.Prop11TheoremAB` | 22 | NOTE | Theorem B(a)/(b) and Theorem A gated as in corrected Thm A/B; extra `hlf`; `IsDomain` kept (Prop 1.1 header's "U need not be connected" holds only for the first part); ambient `D` not required to be bounded or inside `W` |
| `SpherePackings.Support.Section3.PlanarInternal` | 23 | NOTE | Theorem 3.3 (bound and rate) matches the corrected paper; hypotheses are satisfiable (example below). Differences are safe: harmonicity only on the cells of `V[U]`, `V[U]` defined as `{pos ∈ U}`, explicit rate constant. |
| `SpherePackings.Support.Section3.GeneralInternal` | 23 | NOTE | Theorem 3.6 matches the corrected paper with an explicit constant; the smallness condition is `12 M ε ≤ 1` (at least as strong as the paper's); extra `hR₀`, `hε2` are harmless; harmonicity only on the cells of `V[U]`. |
| `SpherePackings.Support.Section3.InternalTaylor` | 23 | NOTE | Statements match the internal-edge comparison. The header says the Laplacian bound sums over internal edges only, but the statement sums over all neighbours in `V̄[U]` (a weaker, correct statement). |
| `SpherePackings.Frozen.Theorem33Planar` | 23 | NOTE | Statement identical to `planar_dirichlet_bound_internal`. The header cites "Corrections 4, 8 and 10" (no Correction 10 exists) and quotes the corrected hypothesis as "harmonic on the cells of V[U]" where the paper says "harmonic on Û". |
| `SpherePackings.Frozen.Theorem33Rate` | 23 | NOTE | Statement identical to `planar_rate_internal`. Same wrong cross-reference. The "published rate is false" remark is informal (no ledger or GAP-CHECKS entry). |
| `SpherePackings.Frozen.Theorem36Rate` | 23 | NOTE | Statement identical to `generaldim_full_internal`. The header writes "ε < (CM)⁻¹ is 12Mε ≤ 1", which conflates the paper's unspecified C with the explicit 12; the Lean statement is at least as strong as the paper's. |
