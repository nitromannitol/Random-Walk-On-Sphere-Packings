# Audit batch 2
| Module | Verdict | Summary |
|---|---|---|
| BouRabeeGwynne.ClockedWalkStopping | NOTE | `vertexStoppedCurve` totalizes a never-exiting trajectory to the start curve; every lemma assumes `exitTime ≤ M` |
| BouRabeeGwynne.WalkSegmentRestriction | OK | Scaled-time restriction identities are correct; `b - a` (ℕ) only used under `a ≤ b` |
| BouRabeeGwynne.CurvePauses | NOTE | Pause invariance matches the paper's inf over increasing homeomorphisms; `terminalPauseClock a` is junk for `a ≤ 0`, all uses have `0 < a` |
| BouRabeeGwynne.WeakExcursionClock | OK | Weak knots and `weakClock` are genuine continuous monotone clocks from 0 to 1 |
| BouRabeeGwynne.WeakExcursionRecovery | OK | Restriction chains recover the Fréchet class; statements match |
| BouRabeeGwynne.WalkExcursionRecovery | OK | Pasted actual segments recover the original polygonal class; hypotheses satisfiable |
| BouRabeeGwynne.ClockedWalkExitParameter | NOTE | `concatenatedExitIndex` is 0 when the pasted walk never leaves U (silent); harmless, the consumer requires `f a ∉ U` |
| BouRabeeGwynne.WalkSkeletonObservation | OK | Observed past recovers the whole prefix; `hfin` is the needed finiteness hypothesis |
| BouRabeeGwynne.ExcursionEndpointExtension | OK | Constant off-graph extension agrees with the vertex kernel at every vertex |
| BouRabeeGwynne.WalkSkeletonKernel | OK | Stage-n history kernel uses `select n` at the current endpoint, as `actualWalkStage` does |
| BouRabeeGwynne.DependentKernelMapAE | OK | Standard a.e.-intertwining lemma; hypotheses are the needed ones |
| BouRabeeGwynne.TrajectoryIdentification | OK | Law of a sequence determined by initial law and one-step conditionals; no hidden contradictions |
| BouRabeeGwynne.WalkSkeletonLaw | OK | Main law identity; bundle is nonvacuous (Example 1); `ofWalk` junk excluded by `haccess` |
| BouRabeeGwynne.ExcursionTrajectory | NOTE | `zeroChain` fallback is junk on incompatible paths, a null set by `ae_compatiblePaths` (documented) |
| BouRabeeGwynne.WalkSkeletonPrefix | NOTE | `actualWalkStage_times` uses `untopD 0`; every statement assumes `hfinite` |
| BouRabeeGwynne.WalkStoppedReconstruction | NOTE | `reconstructedVertexStoppedCurve` inherits the `untopD 0` totalization; guarded by `hexit` |
| BouRabeeGwynne.SubcouplingCompletion | NOTE | `completeSubcoupling` uses truncated measure subtraction; correct only under the dominance hypotheses the theorems carry |
| BouRabeeGwynne.MatchedCellCoupling | OK | Masses and supports correct; `c / μE` junk is unreachable since `c ≤ μE` |
| BouRabeeGwynne.FinitePartitionCoupling | OK | Exact marginals and bad-event bound `1 - Σ min` are correct; disjointness is used |
| BouRabeeGwynne.PartitionCouplingDistance | OK | Coupling-to-Lévy–Prokhorov bounds are standard; ENNReal subtraction harmless |
| BouRabeeGwynne.ReconstructedLawComparison | OK | LP ≤ r from a.e. agreement off a set of mass ≤ r |
| BouRabeeGwynne.WalkReconstructionLaw | OK | Stopped vs reconstructed LP ≤ P(still active); junk on the bad event is absorbed by the bound |
| BouRabeeGwynne.BoundaryStoppingComparison | OK | Oscillation / time-change comparison of stopped curves is correct |
| BouRabeeGwynne.StoppedCurvePrefixes | OK | Constant padding equals the normalized prefix in the Fréchet class, including `a = 0` |
| BouRabeeGwynne.MonotoneStoppedPrefixes | OK | Stopping at corresponding points of a monotone clock preserves the class, including `b = 0` |
| BouRabeeGwynne.PolygonalVertexExitGeometry | NOTE | Pre-exit containment holds only in the ε-thickening (polygon edges may leave U); docstring's "first vertex" is not a continuous first exit |

Verdict counts: OK 18, NOTE 8, ISSUE 0. No `Upstream/` modules are in this batch.

Scope: all 26 modules read in full; definitions cross-checked against `CurveSpace.lean`, `StoppedWalk.lean`, `StoppedCurveLaws.lean`, `ClockedWalkExcursion.lean`, `ClockedWalkConcatenation.lean`, `ActualWalkSkeleton.lean`, `WalkStoppedHistory.lean`, `AbsorbingExcursionKernel.lean`, `WalkSelectedRestart.lean`, `FiniteDirichlet.lean`, `TimePartition.lean`, `ExcursionConcatenation.lean`, and the consumer `WalkCanonicalStopping.lean`. Proofs not reviewed. Junk-value grep (`toReal`, `sSup`/`iSup`, `tsum`, `ncard`, `choose`, `/`, `untopD`, ℕ-subtraction, `sqrt`) over the batch: every hit is classified below.

Paper references: Fréchet metric `eq:cmp-topology` at `paper/rw-spheres.tex:251–254` (inf over increasing homeomorphisms); stopped walk and linear interpolation at lines 274–276; piecewise-linear interpolation and Prokhorov statement at lines 1484–1487.

## BouRabeeGwynne.ClockedWalkStopping
- `ClockedWalkExcursion.vertexStoppedCurve` (line 49): `stoppedPolygonalCurve id U e.2`, i.e. the walk stopped at `exitTime U e.2`. The padded trajectory makes the exit faithful. Junk: if `U` is never left, `untopD 0` gives the constant curve at `e.2 0`. Harmless: `vertexStoppedCurve_clockedWalkSegment` (line 62) assumes `exitTime ≤ M`.
- `measurable_vertexStoppedCurve` (line 52): measurability via `hU.compl`; correct.
- `exitTime_congr_prefix_of_le` (line 15), `exitTime_map` (line 36): proof lemmas whose statements match `exitTime` (first time outside A, `StoppedWalk.lean:117,124`).

## BouRabeeGwynne.WalkSegmentRestriction
- `polygonalCurve_shift_of_scaled_time` (line 14): restriction identity. I checked the clamp terms: for k < a the clamp is 1, for k ≥ a+m it is 0, and the shifted index matches. Matches the paper's uniform-time polygon (lines 274, 1485).
- `clockedWalkSegment_curve_of_scaled_time` (line 64): `(b - a : ℕ)` is guarded by `hab : a ≤ b` (line 65). Fine.

## BouRabeeGwynne.CurvePauses
- `blend` (line 24), `blend_strictMono` (line 38), `blend_surjective` (line 57), `blendTimeChange` (line 67): the explicit strictly increasing approximations match the docstring. `blendTimeChange` is an actual `unitInterval ≃o unitInterval`.
- `blend_dist_le` (line 72): sup-distance ≤ ε, correct.
- `curveSpace_project_comp_monotone` (line 88): `project (f ∘ φ) = project f` for continuous monotone φ with φ 0 = 0, φ 1 = 1. Matches the Fréchet quotient of paper lines 251–254 (`CurveSpace.lean:44–46,181–182`). Both boundary conditions are needed. Consistent hypotheses.
- `terminalPauseClock` (line 123): NOTE. `t / a` with `a ≤ 0` gives a clock ≡ 0, which is not a path completion. Every use (lines 126, 145, `StoppedCurvePrefixes.lean:20`) requires `0 < a`, so this cannot matter.
- `curveSpace_project_terminalPause` (line 145): needs `0 < a ≤ 1`; satisfiable.

## BouRabeeGwynne.WeakExcursionClock
- `WeakTimeKnots` (line 15): monotone knots from 0 to 1 with `n+2` entries, zero-length pieces allowed. Matches the docstring.
- `TimePartition.weakClockReal` (line 73), `weakClock` (line 91): `Σ_i increment_i · localTime_i(t)` is a continuous monotone map from 0 to 1. `localTime` is clamped (`ExcursionConcatenation.lean:48`). Correct.
- `weakClock_apply` (line 117): on piece i it equals `knots_i + localTime · increment_i`. Correct.

## BouRabeeGwynne.WeakExcursionRecovery
- `intervalParam` (line 15), `restrictChain` (line 40): restriction of f to the pieces of Q. Correct.
- `concatenate_restrictChain` (line 48), `project_concatenate_restrictChain` (line 62): equality of Fréchet classes via `curveSpace_project_comp_monotone`. Statements match the docstring ("including all constant pieces").

## BouRabeeGwynne.WalkExcursionRecovery
- `exists_weakWalkTimeKnots` (line 14): the M = 0 branch reuses `P.knots`. Correct.
- `clockedWalkSegments_eq_restrictChain` (line 44), `project_concatenate_clockedWalkSegments` (line 69): pasted actual segments recover `polygonalCurve pos ω M` as a class. Hypotheses (monotone times, endpoints) are the defining ones and are satisfiable.

## BouRabeeGwynne.ClockedWalkExitParameter
- `WalkPrefixTimeData` (line 16): monotone integer cumulative times with `t 0 = 0`. Correct.
- `vertexTime` (line 33): `min m D / D`, the normalized time of vertex m. For `D = 0` it is `0/0 = 0` by Lean convention, which is the intended value (numerator is 0).
- `exitParameter` (line 65): `Classical.choose` of an intermediate-value preimage. Any preimage works (monotone clock), so the choice is harmless.
- `prefixTimes` (line 90), `prefixTimeData` (line 103): `concatenate` is inclusive (`ClockedWalkConcatenation.lean:33–35`), so `prefixTimes (i+1)` is the end of piece i. Correct.
- `concatenatedExitIndex` (lines 119–122): NOTE. `min (untopD 0 (exitTime U (concatenate e n).2)) duration`. If the pasted trajectory never leaves U, the value is 0 and `pastedVertexExitParameter` silently returns 0. The docstring "Defined on every rich sequence" does not disclose this. Harmless downstream: `canonicalWalkStoppingSupport` (`WalkCanonicalStopping.lean:32–37`) requires `f a ∉ U`, which fails at `a = 0` when all pasted vertices lie in U.
- `pastedVertexExitParameter_clock` (line 144): correct.

## BouRabeeGwynne.WalkSkeletonObservation
- `walkSkeletonPrefixOfPast` (line 50): recomputes earlier stages from the observed past. Correct.
- `actualWalkStage_endPoint_observed` (line 38), `walkSkeletonPrefixOfPast_observed` (line 63): hypothesis `hfin` (stage-n clock finite) is the needed one, since `observedHistory` totalizes ⊤ (`WalkStoppedHistory.lean:51`). Holds a.s. under `BoundaryAccessible`. Statement matches the docstring.

## BouRabeeGwynne.ExcursionEndpointExtension
- `finiteVertexKernelExtension` (line 27): `Function.extend pos κ (dirac ∘ constantState)`. Agrees with κ at every vertex (`finiteVertexKernelExtension_apply_vertex`, line 34). Off-graph starts are constant excursions, as the docstring says.
- `vertexExcursionExtension` (line 69), `nextVertexExcursionKernel` (line 113): comap by endpoint `c 1`. Matches the docstring.
- `extended_walkExcursionKernel_ae_start` (line 133): correct.

## BouRabeeGwynne.WalkSkeletonKernel
- `spatialClockedExcursionKernel` (line 18): extension of the vertex kernel with `ClockedWalkExcursion.constant` (duration 0). Correct.
- `spatialClockedExcursionKernel_ae_start` (line 38): correct.
- `walkSkeletonHistoryKernel` (line 56): `absorbingExcursionKernel` with selector `select n` at the current endpoint, comapped to stage n. Matches `actualWalkStage` (`ActualWalkSkeleton.lean:75–85`, stage n+1 uses `select n`).

## BouRabeeGwynne.DependentKernelMapAE
- `compProd_map_dependent_of_kernel_map_ae` (line 13): standard a.e.-intertwining identity. Hypothesis `hmap` is the weakest needed.

## BouRabeeGwynne.TrajectoryIdentification
- `eq_trajMeasure_of_history_next` (line 16), `map_eq_trajMeasure_of_history_next` (line 43): the law of an actual sequence is determined by the initial law and the one-step conditional laws given the full finite past (Ionescu-Tulcea uniqueness). Correct. `IsFiniteMeasure ρ` is implied by `hinit` (no hidden contradiction).

## BouRabeeGwynne.WalkSkeletonLaw
- `actualWalkExcursionSequence` (line 22), `walkSkeletonInitialLaw` (line 35): stage 0 is unflagged. Correct.
- `trajectoryLaw_walkSkeleton_initial` (line 46): correct.
- `trajectoryLaw_walkSkeleton_history_next` (line 108): correct.
- `trajectoryLaw_walkSkeleton_map` (line 190): the whole skeleton law equals `Kernel.trajMeasure` of initial and history kernels. Bundle nonvacuous (Example 1 below). Junk: `ofWalk` (`ClockedWalkExcursion.lean:74–77`) totalizes never-exiting paths to duration 0; the theorem's `haccess` and `hBA` make this a null event (`actualWalkStage_ae_all_clocks_finite`).

## BouRabeeGwynne.ExcursionTrajectory
- `ae_next_relation` (line 21), `ae_compatiblePaths` (line 83): correct. `hstart` is satisfiable, e.g. by `κ n h := dirac (constant (h ⟨n,_⟩ 1))`.
- `compatiblePaths` (line 42): consecutive-endpoint condition for indices ≤ n. Correct.
- `zeroChain` (line 58), `prefixChain` (line 62): NOTE. The fallback is the zero path on incompatible sequences. Junk, but a null set by `ae_compatiblePaths`, as the docstring says.
- `concatenatedCurve` (line 108): correct.

## BouRabeeGwynne.WalkSkeletonPrefix
- `actualWalkStage_times` (lines 21–24): NOTE. `Fin.cases 0 (untopD 0 of stage clocks)`. Junk on ⊤, but `actualWalkStage_times_monotone` and `actualWalkStage_concatenate_eq_comp` (line 89) assume `hfinite`, and `actualWalkStage_clock_finite_of_le` supplies it.
- `actualWalkStage_concatenate_eq_comp` (line 89): `P.concatenate (prefix) = (polygonalCurve pos ω M).comp (P.weakClock Q)` as continuous maps, with knots scaled by M. Correct and stronger than the class statement.
- `actualWalkExcursionSequence_concatenate_eq_comp` (line 120): same identity with spatial selectors. Correct.

## BouRabeeGwynne.WalkStoppedReconstruction
- `reconstructedVertexStoppedCurve` (lines 14–17): NOTE. `vertexStoppedCurve` applied to the concatenation of stages 0..n. Inherits the totalization; the only lemma using it (`reconstructedVertexStoppedCurve_actual`, line 56) assumes `hexit`.
- `concatenate_actualWalkStage` (line 32): inductive identity. Correct.
- `reconstructedVertexStoppedCurve_actual` (line 56): `hexit : exitTime (pos⁻¹' U) ω ≤ clock_n`. Non-vacuous (⊤ ≤ finite fails, and it holds on the stopped event by `actualWalkStage_exit_le_of_stopped`). Matches `stoppedPolygonalCurve` (paper lines 274–276).

## BouRabeeGwynne.SubcouplingCompletion
- `balancedProduct` (line 22): `(α univ)⁻¹ • α.prod β`. With equal masses its marginals are α and β; zero masses give 0. Correct.
- `completeSubcoupling` (line 46): NOTE. `ρ + balancedProduct (μ - ρ.fst) (ν - ρ.snd)` uses truncated measure subtraction, so for ρ not dominated by μ, ν the marginals are not μ, ν. Documented ("dominated marginals"), and every lemma carries `hfst`/`hsnd`.
- `completeSubcoupling_bad_event_le` (line 93): `≤ 1 - ρ univ`. Correct.

## BouRabeeGwynne.MatchedCellCoupling
- `cappedRestrict` (line 18): `(c / μE) • μ|E`. The `c/μE` junk (μE = 0 with c > 0) is unreachable since `matchedCellCoupling` uses `c = min(μE, νF) ≤ μE`.
- `matchedCellCoupling` (line 47): mass `min(μE, νF)` (`matchedCellCoupling_univ`, line 75), supported on E×F (`matchedCellCoupling_compl_prod_eq_zero`, line 92). Correct.

## BouRabeeGwynne.FinitePartitionCoupling
- `finiteMatchedCoupling` (line 20): `Measure.sum` over cells. Correct.
- `finitePartitionCoupling` (line 79): `completeSubcoupling` of the matched part. Correct.
- `finitePartitionCoupling_spec` (line 86): exact marginals, probability measure, and `∀ B, (∀ i, Disjoint B (E i ×ˢ F i)) → coupling B ≤ 1 - Σ min`. Correct. `1 - Σ min` is ENNReal truncated subtraction, harmless because disjointness gives `Σ min ≤ 1`.

## BouRabeeGwynne.PartitionCouplingDistance
- `levyProkhorovEDist_le_of_coupling` (line 19): coupling with `ρ{edist ≥ r} ≤ r` gives LP ≤ r. Standard.
- `levyProkhorovEDist_le_of_finite_cells` (line 57): `hclose` (strict) and `hmass : 1 - Σ min ≤ r` are satisfiable and sufficient. Correct.

## BouRabeeGwynne.ReconstructedLawComparison
- `levyProkhorov_curveLaws_le_of_ae_good` (line 15), `levyProkhorov_curveLaws_le_of_ae_reconstruction` (line 43): LP between laws of f and g is ≤ r when `μ E ≤ r` and f, g are r-close off E. Correct; `hr` needed for the equality case.

## BouRabeeGwynne.WalkReconstructionLaw
- `actualWalkStage_exit_le_of_stopped` (line 20): stopping only outside A gives `exitTime A ≤ clock`. Correct.
- `trajectoryLaw_reconstructedStopped_le` (line 55): LP(stopped law, reconstructed law) ≤ r whenever P(stage n still active) ≤ r. Matches the docstring. The stopped law may totalize on the bad event (e.g. absorbed at a vertex of U \ A), but the bad event contains those ω (a stop only occurs outside U), so the bound absorbs it. Bundle nonvacuous at r = 1 (Example 2); a sharper r would need probability estimates.

## BouRabeeGwynne.BoundaryStoppingComparison
- `stoppedUnitCurve` (line 16): `f (min t a)`, held after `a`. Correct.
- `stoppedUnitCurve_dist_timeChange_le` (line 23): sup-distance ≤ ε + η, with both stopping parameters in one oscillation interval [l,u]. I checked the `min` cases by hand. Correct.
- `curveSpace_edist_stoppedUnitCurve_le` (line 48): edist of stopped classes ≤ `ofReal (ε+η)` via `iInf_le` for the given increasing e. Correct.

## BouRabeeGwynne.StoppedCurvePrefixes
- `prefixUnitCurve` (line 15), `prefixUnitCurve_comp_terminalPause` (line 20): correct with `0 < a`.
- `curveSpace_project_stoppedUnitCurve_eq_prefix` (line 40): equality of classes for all `a`, including `a = 0`. Matches the docstring.

## BouRabeeGwynne.MonotoneStoppedPrefixes
- `restrictedPrefixClock` (line 19): `φ(a t) / b` with `b = φ a > 0`, a clock from [0,1] to [0,1]. Correct.
- `curveSpace_project_prefix_comp_monotone` (line 72), `curveSpace_project_stopped_comp_monotone` (line 98): correct, including `b = 0`.

## BouRabeeGwynne.PolygonalVertexExitGeometry
- `polygonalCurve_at_scaled_vertex` (line 17): correct.
- `polygonalCurve_mem_cthickening_before_vertex` (line 43): correct, checked on the interior edge cases.
- `exists_vertexExit_parameter_comp_monotone` (line 74): NOTE. Gives `a` with `f a = pos (ω m)`, `f a ∉ U`, and `∀ t < a, f t ∈ cthickening ε U`. The pre-exit part is only the ε-thickening, which is the correct form because polygon edges between interior vertices may leave U. The docstring's "first outside vertex" means the first vertex, not a continuous first exit from U. Not misleading, but worth recording.
- `exists_vertexExit_parameter_of_exitTime` (line 120): correct, with `hτ` realized by an actual exit at m.

## Nonvacuity examples
Scratch file: `Nonvacuity.lean`. Compiled from the repository root with
`lake env lean Nonvacuity.lean`.
Result: exit code 0, no errors, no warnings, no `sorry`. Output captured in `nonvacuity.out` (empty).

What they show:
- Example 1 (`trajectoryLaw_walkSkeleton_map`, WalkSkeletonLaw): the hypothesis bundle (injective positions, `B j ⊆ A`, positive total conductance on A and on each `B j`, `BoundaryAccessible A`, measurable selectors) is jointly satisfiable on a two-vertex path network with A = B = {0}, and the law identity applies there.
- Example 2 (`trajectoryLaw_reconstructedStopped_le`, WalkReconstructionLaw): the reconstruction bundle with a selector that genuinely stops at `toyPos 1 ∉ U`, with `U = {toyPos 0}`, is satisfiable. The conclusion at `r = 1` is trivial (LP ≤ 1 always), so this shows the hypotheses hold, not the content of the bound.

```lean
import BouRabeeGwynne.WalkSkeletonLaw
import BouRabeeGwynne.WalkReconstructionLaw

/-! Nonvacuity for the hypothesis bundle of
`FiniteConductanceNetwork.trajectoryLaw_walkSkeleton_map`
(pos injective, `B j ⊆ A`, positive total conductance on `A` and on each `B j`,
`BoundaryAccessible A`, measurable selectors) on a concrete two-vertex network. -/

open MeasureTheory ProbabilityTheory Set
open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork

/-- Two-vertex path `0 — 1` with unit conductance and no loops. -/
def toyNet : FiniteConductanceNetwork (Fin 2) where
  a := fun v w => if v = w then 0 else 1
  symm := by
    intro v w
    by_cases h : v = w
    · subst h; rfl
    · simp [h, Ne.symm h]
  nonneg := by
    intro v w
    by_cases h : v = w <;> simp [h]
  loop_zero := by intro v; simp

/-- Injective positions on the line. -/
noncomputable def toyPos : Fin 2 → Euc 1 := fun i => EuclideanSpace.single 0 ((i : ℕ) : ℝ)

lemma toyPos_injective : Function.Injective toyPos := by
  intro i j h
  have h0 := congrArg (fun x : Euc 1 => x 0) h
  simp [toyPos] at h0
  exact Fin.ext (by exact_mod_cast h0)

/-- The `Option` measurable structure is not in Mathlib; use the discrete one. -/
instance toyOptionMeasurableSpace : MeasurableSpace (Option Unit) := ⊤

instance toyOptionSingleton : MeasurableSingletonClass (Option Unit) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- Interior set `A = {0}`; vertex `1` is outside. -/
def toyA : Set (Fin 2) := {0}

lemma toyA_pos : ∀ v ∈ toyA, 0 < toyNet.totalConductance v := by
  intro v hv
  rw [toyA, mem_singleton_iff] at hv
  subst hv
  simp [FiniteConductanceNetwork.totalConductance, toyNet, Fin.sum_univ_two]

lemma toyA_access : toyNet.BoundaryAccessible toyA := by
  intro v hv
  rw [toyA, mem_singleton_iff] at hv
  subst hv
  refine ⟨1, by simp [toyA], Relation.ReflTransGen.single ?_⟩
  simp [toyNet]

/-- One ball, equal to `{0} ⊆ A`. -/
def toyB : Unit → Set (Fin 2) := fun _ => {0}

lemma toyB_subset : ∀ j, toyB j ⊆ toyA := fun _ => subset_rfl

lemma toyB_pos : ∀ j v, v ∈ toyB j → 0 < toyNet.totalConductance v := by
  intro j v hv
  exact toyA_pos v hv

/-- The constant selector always continues from an arbitrary position. -/
def toySelect : ℕ → Euc 1 → Option Unit := fun _ _ => some ()

lemma toySelect_measurable : ∀ n, Measurable (toySelect n) := fun _ => measurable_const

/-- The hypothesis bundle is jointly satisfiable, so the law identity applies here
(not vacuously). -/
example (v : Fin 2) :
    (toyNet.trajectoryLaw toyA toyA_pos v).map
        (actualWalkExcursionSequence toyPos toyB () toySelect) =
      Kernel.trajMeasure (X := fun _ => Bool × ClockedWalkExcursion 1)
        (toyNet.walkSkeletonInitialLaw toyPos toyB toyB_pos () v)
        (toyNet.walkSkeletonHistoryKernel toyPos toyPos_injective toyB toyB_pos
          toySelect toySelect_measurable) :=
  toyNet.trajectoryLaw_walkSkeleton_map toyPos toyPos_injective toyB toyB_subset
    toyA_pos toyB_pos toyA_access () toySelect toySelect_measurable v

open Classical in
/-- A selector that stops exactly at the outside vertex position `toyPos 1`. -/
noncomputable def toyStopSelect : ℕ → Euc 1 → Option Unit :=
  fun _ x => if x = toyPos 1 then none else some ()

lemma toyStopSelect_measurable : ∀ n, Measurable (toyStopSelect n) := by
  intro n
  apply measurable_to_countable'
  intro x
  rcases x with _ | u
  · have h : toyStopSelect n ⁻¹' {none} = {toyPos 1} := by
      ext y
      by_cases hy : y = toyPos 1 <;> simp [toyStopSelect, hy]
    rw [h]
    exact measurableSet_singleton _
  · have h : toyStopSelect n ⁻¹' {some u} = {toyPos 1}ᶜ := by
      ext y
      by_cases hy : y = toyPos 1 <;> simp [toyStopSelect, hy]
    rw [h]
    exact (measurableSet_singleton _).compl

/-- Stopping set `U = {toyPos 0}`: the selector stops only outside `U`. -/
def toyU : Set (Euc 1) := {toyPos 0}

lemma toyU_measurable : MeasurableSet toyU := measurableSet_singleton _

lemma toyStop_select : ∀ i x, toyStopSelect i x = none → x ∉ toyU := by
  intro i x hx hxU
  simp only [toyStopSelect] at hx
  split_ifs at hx with h
  rw [toyU, mem_singleton_iff] at hxU
  exact absurd (toyPos_injective (h.symm.trans hxU)) (by decide)

/-- The reconstruction bundle at `r = 1`: `hselect` and `hU` are nontrivial here. -/
example (n : ℕ) (v : Fin 2) :
    levyProkhorovEDist
      ((toyNet.trajectoryLaw toyA toyA_pos v).map
        (stoppedPolygonalCurve toyPos (toyPos ⁻¹' toyU)))
      (((toyNet.trajectoryLaw toyA toyA_pos v).map
        (actualWalkExcursionSequence toyPos toyB () toyStopSelect)).map
        (reconstructedVertexStoppedCurve toyU n)) ≤ 1 :=
  toyNet.trajectoryLaw_reconstructedStopped_le toyPos toyB toyB_subset toyA_pos
    toyA_access () toyStopSelect toyU toyU_measurable toyStop_select v n 1 one_pos
    (by simpa using prob_le_one)
```
