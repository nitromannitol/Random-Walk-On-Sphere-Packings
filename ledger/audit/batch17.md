# Audit batch 17
| Module | Verdict | Summary |
|---|---|---|
| SpherePackings.General.Walk.WalkAbsorption | OK | Absorption locality and clocked-excursion identity; statements match docstrings, and the `⊤`-exit convention is shared by both sides. |
| SpherePackings.General.Walk.WalkAdaptiveStopping | OK | Prefix-invariance criterion gives a stopping time; the measurability hypothesis for adaptive exits is explicit and documented. |
| SpherePackings.General.Walk.WalkBrownianActiveTransfer | OK | Pure coupling inequality P(walk active at K) ≤ P(Brownian active at K) + P(first failure); matches docstring; `hexit` present. |
| SpherePackings.General.Walk.WalkBrownianCellMeasures | NOTE | Cell masses equal harmonic/Brownian masses; `discreteHarmonicMeasure` puts escape mass on the start vertex, so it equals the hitting law only under `hexit`. |
| SpherePackings.General.Walk.WalkBrownianCoupling | NOTE | Coupling objects are genuine finite-partition couplings; the `brownianSelectorForWalk 0` ℕ-subtraction value is never read; marginal identification needs `hexit`. |
| SpherePackings.General.Walk.WalkBrownianFailure | NOTE | The `(k+1)b` first-failure bound is true as stated, but `herror` quantifies over every cell vertex (including vertices outside `B j`, where it is false), with no `hexit` and no `B`/`U` link. |
| SpherePackings.General.Walk.WalkBrownianStep | NOTE | One-step bad-mass bounds are correct; `herror` at the walk's current vertex is satisfiable only when that vertex lies in `B j` (same caveat as WalkBrownianFailure). |
| SpherePackings.General.Walk.WalkCanonicalStopping | NOTE | Docstring says the support is "measurable on the rich walk marginal"; the theorem is an a.e. membership statement. |
| SpherePackings.General.Walk.WalkExcursionKernel | NOTE | Escaping paths totalize to the constant path at the start (duration 0), giving an atom of mass `P_v(exit = ⊤)`; statements are unconditional and consistent, and match the paper's stopped law only under `hexit`. |
| SpherePackings.General.Walk.WalkPathStopping | OK | Measurability of the stopped path and stopped history; no new definitions. |
| SpherePackings.General.Walk.WalkReconstructionLaw | OK | Lévy–Prokhorov bound between the actual stopped curve law and the reconstructed law, by `P(active at n) ≤ r`; `hexit` and `hselect` present. |
| SpherePackings.General.Walk.WalkSelectedRestart | OK | Restart kernel is the selected kernel pulled back to the observed terminal vertex; the joint-law identity matches its docstring. |
| SpherePackings.General.Walk.WalkSkeletonKernel | NOTE | Off-graph values of `spatialClockedExcursionKernel` are constant placeholders; walk histories never reach them. |
| SpherePackings.General.Walk.WalkSkeletonLaw | OK | The actual rich excursion sequence has the trajectory law of the skeleton kernel (`hexit` present); definitions match the walk stages. |
| SpherePackings.General.Walk.WalkSkeletonObservation | OK | Recovery of the observed past from the stage prefix; hypotheses explicit. |
| SpherePackings.General.Walk.WalkSkeletonPrefix | NOTE | Clock and knot identities hold; the ℕ-subtraction duration in `clockedWalkSegment` is the true duration only under the monotonicity that the `hfinite` hypothesis supplies. |

Verdict counts: OK 8, NOTE 8, ISSUE 0.

Shared convention, referenced below as "⊤-totalization": `exitTime A ω = ⊤` on never-exiting paths (`BouRabeeGwynne/StoppedWalk.lean:117`) is replaced by index/duration 0 via `untopD 0` in `ofWalk` (`BouRabeeGwynne/ClockedWalkExcursion.lean:75`), `stoppedPolygonalRepresentative` (`BouRabeeGwynne/WalkExcursionKernel.lean:56`) and `exitVertex` (`BouRabeeGwynne/DiscreteHarmonicMeasure.lean:25`). On such paths the walk is "stopped at its start vertex", so the escape mass sits on the start vertex. Equalities between two objects built with the same convention hold unconditionally. Identifications with the paper's objects need `hexit`, which is the paper's a.s. finite-exit property (paper l. 1484–1486, 1505–1508: the walk is stopped at its first exit from `V_n[U]`, and the harmonic measure is the exit distribution).

## SpherePackings.General.Walk.WalkAbsorption
- `historyKernel_map_stopStep` (line 23): the stopped one-step history kernel of the A-absorbed chain equals the B-absorbed one; checks by case split on `stopHistory B n h ∈ B`. No definitions here.
- `trajectoryLaw_map_stopHistory` (line 44): stopping at `B ⊆ A` reproduces the B-absorbed prefix law; no exit-time claim, so no `hexit` needed.
- `trajectoryLaw_map_stoppedWalkPath` (line 76): matches "absorption locality, including paths whose first exit is infinite". After a B-exit both chains stay put (the stopped path does not move off B), so the statement is true without `hexit`.
- `trajectoryLaw_map_clockedExcursion` (line 92): the clocked excursion of the A-absorbed chain equals `clockedWalkExcursionKernel` (`SpherePackings/General/Walk/SkeletonKernels.lean:41`). Both sides use `ofWalk`, so the ⊤-totalization cancels and `hexit` is not needed.

## SpherePackings.General.Walk.WalkAdaptiveStopping
- `isStoppingTime_of_prefix_invariant` (line 23): prefix invariance of `{τ ≤ n}` plus global measurability gives `IsStoppingTime (Filtration.piLE) τ`. Correct; the proof transfers prefix equality through `frestrictLe`.
- `isStoppingTime_nextSelectedExitTime` (line 43): `nextSelectedExitTime` (`BouRabeeGwynne/WalkAdaptiveStopping.lean:100`) is `τ + exitTime (B j) (future)` with `⊤` absorbing. The extra hypothesis `hmeas` on the adaptive exit events replaces finiteness; this is a real hypothesis (the statement does not give it, since `select` has no measurability assumption), and the docstring says so.

## SpherePackings.General.Walk.WalkBrownianActiveTransfer
- `trajectoryLaw_walkActive_le_brownianActive_add_failure` (line 25): the event {walk active at K} is contained in {Brownian active at K} ∪ {some i ≤ K with `(p.1 i, p.2 i) ∉ goodExcursionPair`}, because good pairs have equal flags (`BouRabeeGwynne/WalkBrownianGoodEvent.lean:20`). The inequality direction and the sets match the docstring. `hexit` (line 36) is present, and the bundle is inhabited (see Nonvacuity examples).

## SpherePackings.General.Walk.WalkBrownianCellMeasures
- `measurableSet_walkEndpointCell` (line 27): correct; uses `hpos.measurableSet_range`.
- `walkEndpointCell_mass` (line 32): the active-cell mass of the walk excursion equals the harmonic mass of `E` on the `pos`-image. Holds unconditionally via `endPoint_ofWalk` (`pos (exitVertex)`).
- NOTE: `discreteHarmonicMeasure` (`SpherePackings/General/Walk/DiscreteHarmonicMeasure.lean:67`) is `(law (absorbedKernel κ hA) v).map exitVertex`. For an escaping walk the mass is placed on `v`. It is a probability measure for every `v`, but it equals the hitting law only under `hexit`. The paper's harmonic measure (l. 1505–1508) is the exit law, so this matters only when `hexit` fails.
- `finite_walkBrownian_excursion_bad_le` (line 52): conclusion `≤ ofReal b`, with the bound `m·(b/(m+1)) ≤ b`. Correct. It has no `hexit`, but the conclusion concerns the constructed `finitePartitionCoupling` (`BouRabeeGwynne/FinitePartitionCoupling.lean:79`), which is internally consistent; its link to the paper's cell error needs `hexit`. `herror` is at the fixed start `v`, so it does not quantify over cell vertices.

## SpherePackings.General.Walk.WalkBrownianCoupling
- `walkBrownianCouplingKernel` (line 34): cell-matched coupling of the walk step kernel and the Brownian step kernel, with cells at level `n+1`. Consistent with `walkBrownianCouplingKernel_active_bad_le` and the other step lemmas.
- `walkBrownianCouplingKernel_isMarkov` (line 52), `walkBrownianCouplingKernel_marginals` (line 58): correct; marginals come from `finitePartitionCouplingKernel_spec`.
- `walkBrownianInitialCoupling` (line 67), `_isProbability` (line 76), `_marginals` (line 87): correct; level-0 cells; the `finitePartitionCoupling` spec gives probability and marginals.
- `walkBrownianJointLaw` (line 101): a genuine probability measure (`SkeletonCoupling.jointPathLaw` of a probability initial coupling and a Markov kernel). Its docstring "actual joint measure" is accurate about the construction; the marginal identification is below.
- `walkBrownianJointLaw_marginals` (line 110): the marginals are the actual walk excursion law and the standard Brownian skeleton law. `hexit` (line 114) is present, so this holds.
- NOTE: `brownianSelectorForWalk select n = select (n - 1)` (`BouRabeeGwynne/WalkBrownianCoupling.lean:41`) uses ℕ-subtraction, so index 0 gives `select 0`. The value is never read: the Brownian clock and excursion use the selector only at indices `n+1 ≥ 1` (`BouRabeeGwynne/BrownianSkeletonClock.lean:35`; `BouRabeeGwynne/BrownianSkeletonExcursion.lean`, zero case has no selector). Harmless.

## SpherePackings.General.Walk.WalkBrownianFailure
- `measurableSet_goodExcursionPair_of_embedding` (line 27): measurability of the good set, using `hpos` for the range. Correct.
- `walkBrownianJointLaw_firstFailure_le` (line 49): the bound `(k+1 : ℝ≥0∞) * ofReal b` matches the docstring's "(k+1)b" and the step budget `ε n = ofReal b` for `n < k`, `1` otherwise. Two caveats:
  - (a) No `hexit` and no `hBA`-type relation between `B j` and `U j`. The statement is a true bound on the constructed `walkBrownianJointLaw`. The docstring says "actual coupled excursions", which is accurate only where the walk marginal is identified with the actual walk, i.e. under `hexit` (`walkBrownianJointLaw_marginals`, `WalkBrownianCoupling.lean:110`).
  - (b) `herror` (lines 64–68) quantifies over every `v` with `pos v ∈ E n i` (line 65) and every `y ∈ E n i`. If such a `v` lies outside `B j`, then `discreteHarmonicMeasure κ (B j) v = dirac v`, since the walk exits at time 0. Then `herror` requires the Brownian exit law from `y` to put mass ≈ 1 on the level-`(n+1)` cell of `pos v`. That fails whenever this cell does not meet `∂U j`, because Brownian exit points lie on `∂U j`. So the hypothesis is satisfiable only when cell vertices lie in `B j`. The statement does not assume this, while the Section 4 path supplies it through the inclusion `{w | pos w ∈ ball} ⊆ inner` (`hBA` in `SpherePackings/Support/Section4General/Theorem41.lean`; not re-checked here). Suggested fix if the lemma should stand alone: add `∀ n < k, ∀ i j, choice n i = some j → ∀ v, pos v ∈ E n i → v ∈ B j` or `pos⁻¹' (U j) ⊆ B j`.

## SpherePackings.General.Walk.WalkBrownianStep
- `walkSkeletonHistoryKernel_active_row` (line 31), `walkSkeletonHistoryKernel_constant_row` (line 48): correct identifications of the skeleton rows with the clocked excursion kernel and with the Dirac at the terminated excursion.
- `walkBrownianCouplingKernel_apply` (line 73): unfolds the coupling kernel to `finitePartitionCoupling` of the two row kernels. Correct.
- `walkBrownianCouplingKernel_active_bad_le` (line 86): bad mass `≤ ofReal b`. `herror` is at the walk's current vertex `v` (lines 97–99). The same caveat as WalkBrownianFailure (b) applies: if `v ∉ B j`, the hypothesis fails for interior cells, so the step bound is applicable only at vertices of `B j`. The conclusion is true as stated. `(a : ℝ)` (line 99) enters only via `goodExcursionPair`.
- `walkBrownianCouplingKernel_constant_bad_zero` (line 112): two terminated rows give zero bad mass. Correct: the terminated copies keep the same endpoints, so the `dist ≤ a` clause persists.
- `walkBrownianInitialCoupling_bad_le` (line 131): level-0 analogue. `herror` is at the start `v` (line 135), with the same caveat when `v ∉ B initial`.

## SpherePackings.General.Walk.WalkCanonicalStopping
- `pastedWalkCurve_actual_eq_comp_canonical` (line 37): identity of the pasted walk curve with the polygonal curve composed with the clock. Correct.
- `canonicalWalkStoppingSupport_actual` (line 76): the actual rich sequence lies in `canonicalWalkStoppingSupport` (`BouRabeeGwynne/WalkCanonicalStopping.lean:33`) when the clock is finite, the exit precedes it, and steps before exit are ≤ δ. The three conditions of that definition (projection equality, `f a ∉ U`, `a = 0 ∨ prefix ∈ cthickening`) are consistent with this. Uses only the stated exit bound, not `hexit`.
- `trajectoryLaw_map_ae_canonicalWalkStoppingSupport` (line 166): the statement is `∀ᵐ e, (e n).1 = false ∨ e ∈ canonicalWalkStoppingSupport U δ P`. NOTE: the docstring says "The support needed by the joint comparison is measurable on the rich walk marginal", but the theorem states only a.e. membership. Measurability (`measurableSet_canonicalWalkStoppingSupport`, `BouRabeeGwynne/WalkCanonicalStopping.lean`) is used internally and not stated here. The docstring overstates. Hypotheses `hexit` (line 170), `hsteps` (line 175), `hselect` (line 173) are explicit and satisfiable (e.g. `select = fun _ _ => some j`).

## SpherePackings.General.Walk.WalkExcursionKernel
- `measurable_polygonalCurve` (line 25), `measurable_stoppedPolygonalRepresentative` (line 37): correct.
- `walkExcursionKernel` (line 47): the kernel `v ↦ (law (absorbedKernel κ hA) v).map (stoppedPolygonalRepresentative pos A)`. It is a probability kernel for every `v`. NOTE: on escaping paths the representative is `polygonalCurve pos ω 0`, the constant path at `pos (ω 0)`. So for a start `v` with `P_v(exit = ⊤) > 0` the kernel has an atom at the constant path at `pos v`. The paper's stopped curve law (l. 1484–1486) has no such atom. The kernel agrees with the stopped law only under `hexit`.
- `walkExcursionKernel_ae_start` (line 70), `walkExcursionKernel_ae_mem_convex` (line 81): correct.
- `walkExcursionKernel_project` (line 96), `walkExcursionKernel_endPoint` (line 107): unconditional and correct. Both sides carry the same `untopD 0` convention, so no content on escaping paths.

## SpherePackings.General.Walk.WalkPathStopping
- `measurable_stoppedWalkPath` (line 19), `measurable_stopHistory` (line 30): correct. The underlying definition (`BouRabeeGwynne/WalkPathStopping.lean:20`) stops at the first exit and leaves never-exiting paths unchanged, as its docstring says.

## SpherePackings.General.Walk.WalkReconstructionLaw
- `actualWalkStage_exit_le_of_stopped` (line 23): a stage with flag `true` has exit time ≤ its clock. Correct; uses `hselect`.
- `trajectoryLaw_reconstructedStopped_le` (line 60): Lévy–Prokhorov distance `≤ r` given `P(flag n = false) ≤ r`. Correct: off the active event, the reconstructed curve equals the stopped curve. `hexit` (line 63), `hselect` (line 65) present; `0 < r` (line 66) is technical and not vacuous.

## SpherePackings.General.Walk.WalkSelectedRestart
- `measurable_selectedClockedExcursion` (line 22): correct.
- `selectedClockedRestartKernel` (line 40): the selected kernel of the coupled skeleton, pulled back to `(select h, h.2 h.1)` (lines 40–47). Matches its docstring.
- `selectedClockedRestartKernel_isMarkov` (line 49): correct.
- `observedRestartKernel_map_selectedClockedExcursion` (line 58): pushes the restart law to the selected excursion. Correct; uses `trajectoryLaw_map_clockedExcursion`.
- `trajectoryLaw_observed_selectedExcursion` (line 95): the joint law of (observed history, selected excursion) equals observed-history law ⊗ restart kernel. Needs `hfin` (a.s. finite τ, line 102), which is present. Matches docstring.

## SpherePackings.General.Walk.WalkSkeletonKernel
- `spatialClockedExcursionKernel` (line 21): the clocked excursion kernel extended to `Euc d` by constant excursions off `range pos` (`finiteVertexKernelExtension`, `SpherePackings/General/Walk/ExcursionEndpointExtension.lean:30`). Correct on the graph (`spatialClockedExcursionKernel_vertex`, line 36). NOTE: off-graph values are the placeholder `constant z = (0, fun _ => z)`. Walk histories only have endpoints `pos v` (`endPoint_ofWalk`), so they never reach that branch and cannot change the walk laws.
- `spatialClockedExcursionKernel_isMarkov` (line 27), `spatialClockedExcursionKernel_ae_start` (line 43): correct.
- `walkSkeletonHistoryKernel` (line 60): absorbing excursion kernel on the last state of a history, with selector `select n` applied to the Euclidean endpoint. Matches the stage rule of `actualWalkStage`.
- `walkSkeletonHistoryKernel_isMarkov` (line 70): correct.

## SpherePackings.General.Walk.WalkSkeletonLaw
- `measurable_actualWalkExcursionSequence` (line 26): correct.
- `walkSkeletonInitialLaw` (line 36): the first excursion is active from `v` in `B initial` (clocked kernel with flag `false`). Matches stage 0 of `actualWalkStage` (`BouRabeeGwynne/ActualWalkSkeleton.lean:78`).
- `walkSkeletonInitialLaw_isProbability` (line 43), `trajectoryLaw_walkSkeleton_initial` (line 51): correct.
- `selectedClockedRestartKernel_eq_walkHistory` (line 66): correct; the flag-`true` and flag-`false` branches match.
- `trajectoryLaw_walkSkeleton_history_next` (line 115): the one-step own-history law of the rich sequence. Correct.
- `trajectoryLaw_walkSkeleton_map` (line 201): the law of the rich excursion sequence is `Kernel.trajMeasure` of the initial law and the history kernel. Matches its docstring ("including permanent flags"); `hexit` (line 205) present.

## SpherePackings.General.Walk.WalkSkeletonObservation
- `measurable_walkSkeletonPrefixOfPast` (line 22): correct; the stage-wise measurability hypothesis `hselect` is explicit.
- `walkSkeletonPrefixOfPast_observed` (line 32): recovery of the observed prefix from the observed past. `hfin` present. Matches docstring.

## SpherePackings.General.Walk.WalkSkeletonPrefix
- `actualWalkStage_clock_eq_coe` (private, line 22): correct.
- `actualWalkStage_eq_segment_times` (line 31): stage excursions equal `clockedWalkSegment`s over the integer stage times. NOTE: `clockedWalkSegment` (`BouRabeeGwynne/ActualWalkSkeleton.lean:22`) takes the duration as `b - a` in ℕ. That is the true duration only when stage times are monotone, which `actualWalkStage_times_monotone` gives under the `hfinite` hypothesis carried by the statement. Harmless.
- `actualWalkStage_compatiblePaths` (line 46): correct.
- `actualWalkStage_concatenate_eq_comp` (line 67): the pasted prefix equals a polygonal curve composed with a monotone clock; the docstring's claim about repeated and zero times is accurate, since the clock `Q` is existential with the stated knot identities.
- `actualWalkExcursionSequence_concatenate_eq_comp` (line 98): the same identity for the rich sequence with selectors through `pos`. Correct.

## Nonvacuity examples

Compiled from the repository root with `lake env lean Nonvacuity.lean`. The run exited 0 with no messages (no errors, warnings or `sorry`). The scratch file is `Nonvacuity.lean`.

What it shows:
1. `SpherePackings.Audit17.hexit_two_point` proves the exit hypothesis `∀ v, ∀ᵐ ω ∂law (absorbedKernel κ2 A2_meas) v, exitTime A2 ω ≠ ⊤` for the two-point chain `κ2 x = dirac 1` on `Fin 2` with absorbing set `{0}`.
2. `pos2_measurableEmbedding` gives an injective `MeasurableEmbedding` of `Fin 2` into `Euc 1`.
3. The `example` elaborates `SpherePackings.MarkovChain.trajectoryLaw_walkActive_le_brownianActive_add_failure` with every hypothesis discharged: the Markov kernel, `hexit`, the measurable embedding, open bounded balls for `U`, `IsStandardBrownianLaw (euclideanWienerLaw 1)` (from `isStandardBrownianLaw_euclideanWienerLaw`), a measurable selector, one trivial cell `univ` per level, and `B = A`. So this batch's headline bundle is jointly satisfiable, and the conclusion is a real instance.

Not attempted: the cell-error hypothesis `herror` of `walkBrownianJointLaw_firstFailure_le` and `walkBrownianCouplingKernel_active_bad_le`. It needs quantitative harmonic-versus-Brownian cell estimates. A finite-network analogue of the first-failure bundle is in `SpherePackings/Audit/Nonvacuity/Batch06.lean`; I did not re-check it. Cited and not recompiled: `SpherePackings.exists_walks_assumptionD` (`SpherePackings/Support/Guards/AssumptionDLattice.lean:49`) and `SpherePackings.theorem41_hypotheses_satisfiable` (same file, line 130), which cover the Section 4 bundle. The `hexit` of Theorem 4.1 is derived from `MarkovChain.ae_exit_absorbed_of_free` (`SpherePackings/Support/Section4General/Theorem41.lean:87`) rather than assumed; that file is outside this batch.

The compiled file, verbatim:

```lean
import SpherePackings.General.Walk.WalkBrownianActiveTransfer
import BouRabeeGwynne.EuclideanWienerLaw

/-! Nonvacuity for the General-chain hypothesis bundle of
`SpherePackings.MarkovChain.trajectoryLaw_walkActive_le_brownianActive_add_failure`:
the two-point chain `κ x = dirac 1` on `Fin 2`, absorbing set `A = {0}`, one ball `B = A`,
`d = 1`, the standard Wiener law, and the single trivial cell `univ` at every level. -/

open MeasureTheory ProbabilityTheory Set Metric
open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork
open SpherePackings.MarkovChain

namespace SpherePackings.Audit17

/-- Every step of the chain goes to `1`. -/
noncomputable def κ2 : Kernel (Fin 2) (Fin 2) := Kernel.const (Fin 2) (Measure.dirac 1)

instance : IsMarkovKernel κ2 := by
  unfold κ2
  infer_instance

/-- The absorbing set. -/
def A2 : Set (Fin 2) := {0}

lemma A2_meas : MeasurableSet A2 := (Set.toFinite _).measurableSet

/-- `hexit` for the absorbed two-point chain: it leaves `A2` at time one, almost surely. -/
theorem hexit_two_point : ∀ v : Fin 2, ∀ᵐ ω ∂law (absorbedKernel κ2 A2_meas) v,
    exitTime A2 ω ≠ ⊤ := by
  intro v
  have hdirac : absorbedKernel κ2 A2_meas v = Measure.dirac 1 := by
    by_cases hv : v ∈ A2
    · rw [absorbedKernel_of_mem κ2 A2_meas hv]
      rfl
    · rw [absorbedKernel_of_not_mem κ2 A2_meas hv]
      have hv1 : v = 1 := by
        fin_cases v
        · exact absurd (by simp [A2]) hv
        · rfl
      rw [hv1]
  have hone : ∀ᵐ ω ∂law (absorbedKernel κ2 A2_meas) v, ω 1 = 1 := by
    have h := law_map_eval_one (absorbedKernel κ2 A2_meas) v
    rw [hdirac] at h
    have hy : ∀ᵐ y ∂((law (absorbedKernel κ2 A2_meas) v).map (fun ω => ω 1)), y = 1 := by
      rw [h, ae_dirac_eq]
      exact Filter.eventually_pure.mpr rfl
    exact (ae_map_iff (measurable_pi_apply 1).aemeasurable (measurableSet_singleton 1)).mp hy
  filter_upwards [hone] with ω hω
  intro htop
  have h1 : exitTime A2 ω ≤ ((1 : ℕ) : WithTop ℕ) :=
    (exitTime_le_iff A2 ω 1).mpr ⟨1, le_rfl, by simp [A2, hω]⟩
  rw [htop] at h1
  simp at h1

/-- The embedding of the two vertices into `ℝ¹`. -/
noncomputable def pos2 : Fin 2 → Euc 1 := fun i => EuclideanSpace.single 0 ((i : ℕ) : ℝ)

lemma pos2_injective : Function.Injective pos2 := by
  intro a b h
  have h0 : ((a : ℕ) : ℝ) = ((b : ℕ) : ℝ) := by
    have := congrArg (fun x : Euc 1 => x 0) h
    simpa [pos2, PiLp.single_apply] using this
  have : (a : ℕ) = (b : ℕ) := by exact_mod_cast h0
  exact Fin.ext this

lemma pos2_measurableEmbedding : MeasurableEmbedding pos2 where
  injective := pos2_injective
  measurable := measurable_from_top
  measurableSet_image' := by
    intro s _
    exact (s.toFinite.image pos2).measurableSet

/-- The discrete σ-algebra on `Option Unit` (every subset is countable). -/
instance : MeasurableSpace (Option Unit) := ⊤

instance : MeasurableSingletonClass (Option Unit) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- The concrete instance of the headline bundle of `WalkBrownianActiveTransfer`. -/
example : True := by
  have h := SpherePackings.MarkovChain.trajectoryLaw_walkActive_le_brownianActive_add_failure
    κ2 (le_refl 1) pos2
    pos2_measurableEmbedding (B := fun _ : Unit => A2) (fun _ => A2_meas)
    (U := fun _ : Unit => Metric.ball (0 : Euc 1) 1) (fun _ => Metric.isOpen_ball)
    (fun _ => Metric.isBounded_ball) (euclideanWienerLaw 1)
    (isStandardBrownianLaw_euclideanWienerLaw 1) (fun _ _ => some ())
    (fun _ => measurable_const) (fun _ => 1) (fun _ _ => Set.univ)
    (fun _ _ => MeasurableSet.univ) (fun _ => fun i j hij => absurd (Subsingleton.elim i j) hij)
    (fun _ => subset_rfl) A2_meas hexit_two_point () 0 0 1 2
  trivial

end SpherePackings.Audit17
```

Compile result: exit status 0, no output.
