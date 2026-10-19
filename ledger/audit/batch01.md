# Audit batch 1
| Module | Verdict | Summary |
|---|---|---|
| BouRabeeGwynne.WalkRestart | OK | Shift and exit-time/exit-vertex restart identities are correct. |
| BouRabeeGwynne.WalkMemoryless | OK | Continuation law is the fresh walk from the last vertex; prefix shift is correct. |
| BouRabeeGwynne.WalkJointRestart | OK | Walk kernel and restart kernel are the genuine trajectory law; joint prefix/future factorisation is correct. |
| BouRabeeGwynne.WalkStoppedHistory | NOTE | `observedHistory`/`futureAt` totalise `τ = ⊤` to time 0; harmless because all uses are a.s. finite or absorbed by `⊤`. |
| BouRabeeGwynne.WalkStrongMarkov | OK | Strong Markov factorisation at an a.s. finite stopping time; restart depends only on the terminal vertex; `hfin` is satisfiable. |
| BouRabeeGwynne.WalkAdaptiveStopping | OK | Adaptive next-exit time is a stopping time; `⊤` and `none` cases are correct; inclusion direction of `exitTime_le_of_subset` is correct. |
| BouRabeeGwynne.WalkPathStopping | OK | `stoppedWalkPath B` freezes at the first vertex outside `B`; `≤` at the exit time is correct. |
| BouRabeeGwynne.StoppedCurveProperties | NOTE | Interpolation identities are correct; endpoint on never-exiting paths is `pos (ω 0)` (same totalisation as `exitVertex`), harmless. |
| BouRabeeGwynne.LevyProkhorovMaps | OK | 1-Lipschitz measurable maps contract Mathlib's Lévy–Prokhorov edistance; endpoint map is 1-Lipschitz on `CurveSpace`. |
| BouRabeeGwynne.HarmonicMeasureBridge | NOTE | Endpoint identity is correct without `BoundaryAccessible` only because both sides share the `⊤` totalisation; `discreteHarmonicMeasure` is the true harmonic measure only under a.s. finite exit, which the docstring omits. |
| BouRabeeGwynne.TimePartition | OK | `n+1` nondegenerate intervals from 0 to 1; piecewise-affine increasing homeomorphism is correct; `Classical.choose` is harmless. |
| BouRabeeGwynne.SkeletonCurveComparison | OK | Segment-oscillation bounds give Fréchet bound `α+β+γ` in the paper's inf-over-increasing-homeomorphisms metric; constant-curve distance is correct. |
| BouRabeeGwynne.ExcursionConcatenation | OK | Adjacent-endpoint chain condition, 1-Lipschitz concatenation and exact `concatenate ∘ restrictChain` are correct. |
| BouRabeeGwynne.WalkExcursionKernel | NOTE | `stoppedPolygonalRepresentative` totalises `⊤` to a constant curve at `ω 0`; harmless (a.s. excluded), identities are correct. |
| BouRabeeGwynne.ClockedWalkExcursion | NOTE | `ofWalk` totalises `⊤` to duration 0; the pair type is not quotiented, so entries beyond the duration are representation-dependent, but kernels only produce canonically padded values. |
| BouRabeeGwynne.DependentKernelMap | OK | Dependent-kernel pushforward identity is correct; hypothesis `hmap` is satisfiable. |
| BouRabeeGwynne.WalkAbsorption | OK | Absorption locality (stopping an `A`-walk at first exit from `B ⊆ A` gives the `B`-absorbed walk) is correct, including infinite-exit paths. |
| BouRabeeGwynne.WalkSelectedRestart | NOTE | Selected-excursion kernel and joint-law theorem are correct; `[MeasurableSpace (Option J)]` is a free parameter that is forced to be `⊤` for countable `J`, harmless. |
| BouRabeeGwynne.ActualWalkSkeleton | NOTE | Stage recursion is correct and `actualWalkStage_ae_all_clocks_finite` matches its docstring; selector is memoryless (stage and current vertex, as in the paper), and `clockedWalkSegment` uses truncated subtraction (valid only for `a ≤ b`). |
| BouRabeeGwynne.ClockedWalkConcatenation | NOTE | `append` has no docstring and no endpoint-compatibility precondition (junction taken from `e`, `f.2 0` dropped); correct for the segments actually used. |

Verdict counts: OK 12, NOTE 8, ISSUE 0.

Scope notes:
- No `Upstream/` module is in this batch.
- Definitions used from outside the batch and checked for meaning: `StoppedWalk.lean` (`totalConductance`, `transitionProbability`, `stepPMF`, `exitTime` at line 117, `historyKernel` at 195, `trajectoryLaw` at 208); `DiscreteHarmonicMeasure.lean` (`exitVertex` at 24, `discreteHarmonicMeasure` at 114); `DiscretePDEAlgebra.lean` (`FiniteConductanceNetwork`, line 98); `FiniteDirichlet.lean` (`BoundaryAccessible` at 18, `SolvesDirichlet` at 23); `StoppedCurveLaws.lean` (`polygonalCurve` at 45, `stoppedPolygonalCurve` at 60); `CurveSpace.lean` (`NormalizedCurve.frechetEDist` at 49, `CurveSpace.endPoint` at 201, `endPoint_lipschitz` at 209); `AbsorbingExcursionKernel.lean` (`selectedExcursionKernel` at 21); `FiniteExit.lean` (`trajectoryLaw_ae_finiteExit` at 260).
- Mathlib: `Filtration.piLE` (`Mathlib/Probability/Process/Filtration.lean:491`) is the coordinate filtration `σ(ω_0,…,ω_i)`; `levyProkhorovEDist` (`Mathlib/MeasureTheory/Measure/LevyProkhorovMetric.lean:53`) is the standard Lévy–Prokhorov infimum over all measurable `B` with open thickenings.
- Paper cross-checks: the Fréchet metric matches paper eq. `cmp-topology` (`paper/rw-spheres.tex` l.251–260); the selector matches the Section 4 construction (ball centred at the grid point nearest the current position; stop when it leaves `B_δ(U)`, `paper/rw-spheres.tex` l.1568–1571); the strong Markov use matches l.1500.
- None of the 20 modules states the paper's main Section 4 theorem (`theorem:general-clt`, l.1480); these are its infrastructure. The batch's statements are not weaker than their docstrings, except for the caveat on `discreteHarmonicMeasure` noted in `HarmonicMeasureBridge`.

## BouRabeeGwynne.WalkRestart
- `walkShift` (line 17): matches the shift `k ↦ ω (n + k)`.
- `exitTime_walkShift_of_eq` (line 34): matches; for `n ≤ τ` the exit time of the shifted path is `τ - n`. `exitTime` is the first vertex outside `A` (StoppedWalk.lean:117).
- `exitVertex_walkShift_of_eq` (line 65): matches; the restarted path has the same exit vertex.

## BouRabeeGwynne.WalkMemoryless
- `shiftPrefix` (line 41): the suffix of a finite history, with the restart vertex at index 0; matches the docstring.
- `continuation_shiftPrefix_law` (line 75) and `continuation_walkShift_law` (line 111): the continuation of `historyKernel` (StoppedWalk.lean:195) after a deterministic time has the law of `trajectoryLaw` from the last vertex. This is the Markov property, with no junk values.

## BouRabeeGwynne.WalkJointRestart
- `walkPathKernel` (line 38): the genuine trajectory law as a kernel from `V`; measurable since `V` is finite. Matches.
- `restartKernel` (line 49): the future law given a finite history depends only on its terminal vertex. Matches the chain.
- `trajectoryLaw_prefix_future` (line 71): the deterministic-time Markov factorisation. Matches.

## BouRabeeGwynne.WalkStoppedHistory
- `paddedHistory` (line 45): encodes a finite history as (length, path padded by its terminal value). Matches the docstring.
- `observedHistory` (line 51), NOTE: `(τ ω).untopD 0` gives the length-0 history at `ω 0` on `{τ = ⊤}`. This is a junk value, but it cannot matter: `trajectoryLaw_observed_future` (WalkStrongMarkov.lean:91) and the selected-excursion theorem assume `τ < ⊤` a.s., and `nextSelectedExitTime` is `⊤` whenever `τ = ⊤` (WalkAdaptiveStopping.lean:94).
- `futureAt` (line 54), NOTE: the same totalisation (shift by 0 on `⊤`), harmless for the same reason.
- `measure_eq_sum_stopping_slices` (line 91): correct decomposition of a measure by finite stopping values; `hfin` is a genuine a.s. condition, not a contradiction.

## BouRabeeGwynne.WalkStrongMarkov
- `observedRestartKernel` (line 22): a fresh genuine walk started at `h.2 h.1`, the terminal vertex. Matches the strong Markov property.
- `trajectoryLaw_observed_future` (line 91): the strong Markov joint law of the observed history and the future. Its hypothesis `hfin` is satisfiable: for `τ = exitTime A`, `trajectoryLaw_ae_finiteExit` (FiniteExit.lean:260) supplies it under `BoundaryAccessible` (see the compiled example below). Matches the docstring; the paper uses this at l.1500.

## BouRabeeGwynne.WalkAdaptiveStopping
- `isStoppingTime_of_prefix_invariant` (line 52): the correct criterion on the finite-state path space; no hidden measurability assumption.
- `nextSelectedExitTime` (line 94): `τ ω + (none ↦ 0 | some j ↦ exitTime (B j) (future))`. Correct; `⊤` absorbs in `WithTop ℕ`.
- `isStoppingTime_nextSelectedExitTime` (line 107): correct and not vacuous; the selector may be an arbitrary function of the observed history, because the path space is finite-state.
- `exitTime_le_of_subset` (line 143): correct direction: `B ⊆ A` implies exit from `B` no later than exit from `A`.
- `nextSelectedExitTime_le_exitTime` (line 155): correct pointwise bound.

## BouRabeeGwynne.WalkPathStopping
- `stoppedWalkPath` (line 19): keeps `ω` until the first vertex outside `B` and then freezes there. `B` is the continuation set. Matches the docstring.
- `stoppedWalkPath_eq_of_le_exitTime` (line 53): uses `≤` correctly; at the exit time itself the path is still `ω τ`.
- `stopHistory` (line 86): the finite-history version. Correct.

## BouRabeeGwynne.StoppedCurveProperties
- `polygonalCurve_on_segment_scaled` (line 65) and `polygonalCurve_on_segment` (line 106): correct affine formula on `[j/m, (j+1)/m]`; `j < m` gives `m > 0`.
- `stoppedPolygonalCurve_of_exitTime_zero` (line 118): a duration-zero exit gives the constant curve at `pos (ω 0)`. Correct.
- `stoppedPolygonalCurve_endPoint` (line 132), NOTE: the endpoint is `pos (ω ((exitTime A ω).untopD 0))`. On never-exiting paths this is `pos (ω 0)`, the same totalisation as `exitVertex`, so it is consistent and harmless.

## BouRabeeGwynne.LevyProkhorovMaps
- `levyProkhorovEDist_map_le_of_lipschitz_one` (line 33): correct and standard. Mathlib's `levyProkhorovEDist` (LevyProkhorovMetric.lean:53) is an infimum over `ε` with `μ B ≤ ν (thickening ε B) + ε` for all measurable `B`. The `⊤` junk of `toReal` is harmless, since `ε = ⊤` is always in the set.
- `levyProkhorovEDist_endpoint_map_le` (line 53): correct; `CurveSpace.endPoint` is 1-Lipschitz (CurveSpace.lean:209) because every increasing homeomorphism fixes `1`.

## BouRabeeGwynne.HarmonicMeasureBridge
- `stoppedPolygonalCurve_map_endPoint` (line 26), NOTE: correct as stated, with no `BoundaryAccessible` hypothesis. Both sides use the same totalisation of `⊤` (the constant curve at `ω 0`, and `exitVertex = ω 0`). But `discreteHarmonicMeasure` (DiscreteHarmonicMeasure.lean:114) equals the true first-exit harmonic measure only when exit is a.s. finite. For a trapped walk it puts mass on the starting vertex. The docstring "is its first-exit harmonic measure" should carry this caveat.
- `abs_integral_discreteHarmonicMeasure_sub_le` (line 42): correct. `hboundary` forces `η ≥ 0` whenever the complement of `A` is nonempty, which `BoundaryAccessible` guarantees for nonempty `A`; so no negative-`η` vacuity.
- `abs_integral_discreteHarmonicMeasure_sub_lt` (line 56): correct strict version.

## BouRabeeGwynne.TimePartition
- `TimePartition` (line 29): `n+1` nondegenerate consecutive intervals with strictly increasing knots from `0` to `1`. Matches the docstring.
- `interval` (line 60): `Classical.choose` of an interval containing `x`. Harmless: `map_eq_affine` (line 135) shows the value is independent of the choice.
- `affine` (line 68): the affine map between corresponding intervals. Correct; denominators are positive by `gap_pos` (line 46).
- `map` (line 129) and `timeChange` (line 175): the increasing order isomorphism of `[0,1]` matching knots (`timeChange_left`/`timeChange_right`, lines 193/198). Correct.

## BouRabeeGwynne.SkeletonCurveComparison
- `dist_timeChange_le_of_segment_bounds` (line 24): correct triangle inequality through the left knot of the interval containing `t`.
- `frechetEDist_le_of_segment_bounds` (line 50): bounds `NormalizedCurve.frechetEDist` (CurveSpace.lean:49), the infimum over increasing homeomorphisms of the supremal error. This matches paper eq. `cmp-topology`.
- `curveSpace_edist_le_of_segment_bounds` (line 66): correct transfer to the quotient metric.
- `frechetEDist_const_const` (line 80): the Fréchet distance of constant curves equals the distance of their positions. Correct.

## BouRabeeGwynne.ExcursionConcatenation
- `ExcursionChain` (line 19): the adjacent-endpoint condition `i.succ = j.castSucc → c i 1 = c j 0`. Matches the docstring.
- `uniform` (line 30): knots `i/(n+1)`, `i = 0,…,n+1`. Correct canonical partition.
- `localTime` (line 48): clamped normalized local time. Denominators are positive.
- `concatenate` (line 121) and `dist_concatenate_le` (line 139): correct; 1-Lipschitz for fixed partitions.
- `concatenate_curveSpace_edist_le` (line 161): correct bound `α+β+γ`. Its hypotheses quantify over all `t` (stronger than needed, harmless).
- `restrictChain` (line 216) and `concatenate_restrictChain` (line 227): the round trip is exact. Correct.

## BouRabeeGwynne.WalkExcursionKernel
- `polygonalCurve_mem_of_convex` (line 34): correct.
- `stoppedPolygonalRepresentative` (line 54), NOTE: the `untopD 0` totalisation makes never-exiting paths constant at `ω 0`. Harmless: they are a.s. excluded under `BoundaryAccessible`, and the identities hold unconditionally because both sides use the same representative.
- `walkExcursionKernel` (line 74): the kernel is the law of the representative, and it is Markov (line 84). Correct.
- `walkExcursionKernel_ae_mem_convex` (line 103): not vacuous (`S = univ` works); conclusion matches the docstring.
- `walkExcursionKernel_endPoint` (line 127): the endpoint law equals `discreteHarmonicMeasure`; same caveat as `HarmonicMeasureBridge`.

## BouRabeeGwynne.ClockedWalkExcursion
- `ClockedWalkExcursion` (line 16), NOTE: `ℕ × (ℕ → Euc d)` is not quotiented, so entries beyond the duration are arbitrary. Distinct values can give the same curve. Every kernel here outputs canonically terminally padded values (`ofWalk`, `constant`), so the laws are unaffected.
- `start` (line 22), `endPoint` (line 24), `curve` (line 26): correct; `endPoint` is the vertex at index equal to the duration.
- `ofWalk` (line 74), NOTE: `m := untopD 0` totalises `⊤` to `(0, const pos (ω 0))`. Harmless for the same reason as `stoppedPolygonalRepresentative`.
- `clockedWalkExcursionKernel` (line 110): the law of `ofWalk` under `trajectoryLaw B`. Correct.
- `clockedWalkExcursionKernel_endPoint` (line 144): same caveat as `HarmonicMeasureBridge`.

## BouRabeeGwynne.DependentKernelMap
- `compProd_map_dependent_of_kernel_map` (line 12): correct. If the conditional law of the second coordinate depends only on `f a`, the joint pushforward is `μ.map f ⊗ η`. The hypothesis `hmap` for all `a` is satisfiable, so the lemma is not vacuous.

## BouRabeeGwynne.WalkAbsorption
- `exitTime_stoppedWalkPath` (line 24): correct.
- `trajectoryLaw_map_stoppedWalkPath` (line 156): correct absorption locality. Stopping the `A`-walk at its first exit from `B ⊆ A` gives the `B`-absorbed walk. Transition rows agree on `B` (`stepPMF_eq_of_mem_both`, line 105). Covers infinite-exit paths, as the docstring says.
- `trajectoryLaw_map_clockedExcursion` (line 172): correct.

## BouRabeeGwynne.WalkSelectedRestart
- `selectedClockedExcursion` (line 20): `none` gives the permanent flag `true` with a constant excursion at the current vertex. `some j` gives flag `false` with `ofWalk`. Matches the docstring.
- `selectedClockedRestartKernel` (line 41), NOTE: `[MeasurableSpace (Option J)]` is a free instance parameter, because Mathlib has no instance for `Option`. For countable `J` with `MeasurableSingletonClass` it is forced to be the discrete σ-algebra, so the parameter is harmless. `hs : Measurable select` is a real requirement.
- `trajectoryLaw_observed_selectedExcursion` (line 91): correct joint law. Not vacuous: see the compiled example below.

## BouRabeeGwynne.ActualWalkSkeleton
- `clockedWalkSegment` (line 21), NOTE: `b - a` is truncated, so the segment is the intended one only when `a ≤ b`. All uses have monotone clocks (`actualWalkStage_clock_mono`, line 157).
- `walkStageSelector` (line 69): recomputes the previous stopping flag from the observed past, as its comment says. Correct.
- `actualWalkStage` (line 75), NOTE: the selector is `ℕ → V → Option J` (stage index and current vertex only), not the full-history selector accepted by `nextSelectedExitTime`. This matches the paper (the ball is centred at the grid point nearest the current position, and the walk stops when that point leaves `B_δ(U)`; `paper/rw-spheres.tex` l.1568–1571). It is a deliberate restriction, not a defect. The stage recursion (clock, flag, excursion) is correct.
- `actualWalkStage_ae_all_clocks_finite` (line 272): matches its docstring. All clocks are a.s. finite, derived from ambient exit via `actualWalkStage_clock_le_ambientExit` (line 259). Not vacuous: see the compiled example below.

## BouRabeeGwynne.ClockedWalkConcatenation
- `append` (line 15), NOTE: no docstring and no endpoint-compatibility precondition. The junction vertex is taken from `e` (`e.2 e.1`) and `f.2 0` is silently dropped. Correct for the segments actually used: `append_clockedWalkSegment` (line 43) proves it for consecutive segments.
- `concatenate` (line 33): a left fold, correct.
- `concatenate_of_clockedWalkSegments` (line 60): correct under monotone `times` with `times 0 = 0`.

## Nonvacuity examples
Compiled from the repository root with `lake env lean Nonvacuity.lean`. Exit status 0, no errors, no warnings, no output. Nothing was built.

What it shows:
- The concrete network `twoVertexNet` (two vertices joined by unit conductance) with `interior0 = {0}` satisfies `hpos` and `BoundaryAccessible`. So the hypothesis bundle of `actualWalkStage_ae_all_clocks_finite` (`hBA`, `hA`, `haccess`) is jointly satisfiable, and the theorem's conclusion is obtained for it.
- The same network with `B = fun _ => interior0` and the constant selector `fun _ => some ()` satisfies every hypothesis of `trajectoryLaw_observed_selectedExcursion`, including `Measurable select` and the almost-sure finiteness `hfin`, which is derived from `trajectoryLaw_ae_finiteExit` for `τ = exitTime interior0`.
- Not attempted: a network with a trapped interior, which would show the `discreteHarmonicMeasure` caveat concretely. The caveat rests on the definition `exitVertex A ω = ω ((exitTime A ω).untopD 0)`.

```lean
import BouRabeeGwynne.ActualWalkSkeleton

/-! Scratch nonvacuity checks for batch-1 hypothesis bundles.
Not part of the repository. -/

open MeasureTheory ProbabilityTheory Set

namespace BouRabeeGwynne.FiniteConductanceNetwork

/-- Two vertices joined by one edge of unit conductance. -/
def twoVertexNet : FiniteConductanceNetwork (Fin 2) where
  a v w := if v = w then 0 else 1
  symm v w := by by_cases h : v = w <;> simp [h, eq_comm]
  nonneg v w := by by_cases h : v = w <;> simp [h]
  loop_zero v := by simp

/-- The interior set `{0}`; its only exit is the vertex `1`. -/
def interior0 : Set (Fin 2) := {0}

lemma twoVertexNet_hpos : ∀ v ∈ interior0, 0 < twoVertexNet.totalConductance v := by
  intro v hv
  rw [interior0, Set.mem_singleton_iff] at hv
  subst hv
  simp [totalConductance, twoVertexNet, Fin.sum_univ_two]

lemma twoVertexNet_access : twoVertexNet.BoundaryAccessible interior0 := by
  intro v hv
  rw [interior0, Set.mem_singleton_iff] at hv
  subst hv
  refine ⟨1, by simp [interior0], Relation.ReflTransGen.single ?_⟩
  simp [twoVertexNet]

instance : MeasurableSpace (Option Unit) := ⊤

instance : MeasurableSingletonClass (Option Unit) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- The hypothesis bundle of `actualWalkStage_ae_all_clocks_finite` is satisfiable, and the
conclusion is obtained for the concrete network. -/
example (pos : Fin 2 → Euc 1) :
    ∀ᵐ ω ∂twoVertexNet.trajectoryLaw interior0 twoVertexNet_hpos 0, ∀ n,
      (actualWalkStage pos (fun _ : Unit => interior0) () (fun _ _ => some ()) n ω).1 ≠ ⊤ :=
  actualWalkStage_ae_all_clocks_finite (A := interior0) twoVertexNet pos
    (fun _ : Unit => interior0) (fun _ => subset_rfl) twoVertexNet_hpos twoVertexNet_access
    () (fun _ _ => some ()) 0

/-- The hypothesis bundle of `trajectoryLaw_observed_selectedExcursion` (in particular the
almost-sure finiteness `hfin`, here derived from `BoundaryAccessible`) is satisfiable. -/
theorem nonvacuous_selectedExcursion (pos : Fin 2 → Euc 1) (v : Fin 2) :
    (twoVertexNet.trajectoryLaw interior0 twoVertexNet_hpos v).map (fun ω =>
        (observedHistory (exitTime interior0) ω,
          selectedClockedExcursion pos (fun _ : Unit => interior0)
            (some (), (observedHistory (exitTime interior0) ω).2 (observedHistory (exitTime interior0) ω).1)
            (futureAt (exitTime interior0) ω))) =
      (twoVertexNet.trajectoryLaw interior0 twoVertexNet_hpos v).map (observedHistory (exitTime interior0))
        ⊗ₘ twoVertexNet.selectedClockedRestartKernel pos (fun _ : Unit => interior0)
            (fun _ _ hv => twoVertexNet_hpos _ hv) (fun _ => some ()) measurable_const :=
  twoVertexNet.trajectoryLaw_observed_selectedExcursion pos (fun _ : Unit => interior0)
    (fun _ => subset_rfl) twoVertexNet_hpos (fun _ _ hv => twoVertexNet_hpos _ hv)
    (fun _ => some ()) measurable_const v (exitTime_isStoppingTime interior0)
    (twoVertexNet.trajectoryLaw_ae_finiteExit interior0 twoVertexNet_hpos twoVertexNet_access v)

end BouRabeeGwynne.FiniteConductanceNetwork
```
