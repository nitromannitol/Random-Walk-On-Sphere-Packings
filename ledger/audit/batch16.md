# Audit batch 16
| Module | Verdict | Summary |
|---|---|---|
| SpherePackings.General.Walk.ActualStoppedLawComparison | NOTE | Comparison is true as stated; `η` unconstrained (harmless); no finite-exit hypothesis for `U`, so stopped laws are totalized on the never-exit event |
| SpherePackings.General.Walk.ActualWalkSkeleton | OK | Stage/clock measurability and a.s. finiteness of all clocks (derived from `hexit`); lemmas only |
| SpherePackings.General.Walk.BallStoppedLawComparison | OK | Inner-margin selector hypothesis is exactly `dist x c_j ≤ r/2`; shape and Brownian bounds match docstring; instantiated by Theorem41 |
| SpherePackings.General.Walk.CanonicalStoppingRange | OK | Range-to-canonical-support lemma matches its docstring; `hselect` has the right direction |
| SpherePackings.General.Walk.ClockedWalkExcursion | OK | Clocked-excursion kernel identities; junk `untopD 0` is consistent on both sides |
| SpherePackings.General.Walk.DiscreteHarmonicMeasure | NOTE | `discreteHarmonicMeasure` equals the harmonic measure only under the a.s. exit hypothesis (junk `ω 0` on never-exit); all theorems carry `hexit` |
| SpherePackings.General.Walk.ExcursionEndpointExtension | NOTE | Unused lemma `measurableEmbedding_finite_positions` is misnamed; `nextVertexExcursionKernel` is unused in the repo; `finiteVertexKernelExtension` name says "finite" but is general |
| SpherePackings.General.Walk.ExcursionSteps | NOTE | `curveOscillationLe R` means radius about the start, not oscillation/diameter; the 2R step bound uses that reading correctly |
| SpherePackings.General.Walk.FiniteStoppedLawComparisonGood | OK | Walk-support hypothesis required only on the good event, as documented; `η` unconstrained as in ActualStoppedLawComparison |
| SpherePackings.General.Walk.FreeAbsorbed | OK | Free-chain and absorbed-chain identities; hypotheses are the right ones (`B ⊆ A`, stop-invariance) |
| SpherePackings.General.Walk.GoodRange | OK | Good-pair range bound `max R₀ (2a+S)` and ball-shape bound match docstrings |
| SpherePackings.General.Walk.HarmonicMeasureBridge | OK | Endpoint law equals harmonic measure (unconditional); Dirichlet error bounds (`≤` and strict `<`) are correct |
| SpherePackings.General.Walk.JointExcursionPasting | OK | Almost-sure structure, walk-range and pasting statements match docstrings |
| SpherePackings.General.Walk.SkeletonKernels | NOTE | `vertexKernelExtension` is an unused duplicate of `finiteVertexKernelExtension`; the module docstring points at it as the one in use |
| SpherePackings.General.Walk.StoppedCurveMeasurable | NOTE | `untopD 0` gives duration 0 on never-exit paths; every law statement using it carries `hexit`, so the value is on a null set; measurability unaffected |

Counts: OK 9, NOTE 6, ISSUE 0.

## SpherePackings.General.Walk.ActualStoppedLawComparison
- `levyProkhorov_actual_stopped_laws_le_of_shape` (line 29): NOTE. (a) `η` has no sign hypothesis (line 42; only `hε` at line 43). For `η < 0`, `unitCurveDiameterBound η` is empty (BouRabeeGwynne/UnitCurveOscillation.lean:66), so `unitCurveExitOscillationBad` (line 79) is all curves and `hosc` forces `o ≥ 1`; the conclusion is then trivially true. Harmless, no unsoundness. (b) `U` is only assumed open (line 42). Neither the walk's nor the Brownian exit from `U` is assumed a.s. finite, so both stopped laws are totalized on the never-exit event (`untopD 0` in `stoppedPolygonalCurve`; `⨅ ∅ = ⊤ ↦ 0` via `toNNReal` in `stoppedBrownianRepresentative`, BouRabeeGwynne/StoppedCurveLaws.lean). The statement is still true as written (kernel-checked), and it is stronger than needed in that regime, but the docstring of `stoppedBrownianRepresentative` says exit is "excluded almost surely in the main statement", which this lemma does not assume. The application at SpherePackings/Support/Section4General/Theorem41.lean:119 uses bounded (ball) domains. (c) Hypotheses are mutually consistent: `hbuffer` (line 43), `hpoint` (line 46), `hsmall` (line 69) and budgets (lines 66-68) can all hold.

## SpherePackings.General.Walk.ActualWalkSkeleton
- `measurable_nextSelectedExitTime` (line 26), `measurableSet_nextSelectedExitTime_le` (line 45), `measurable_walkStageSelector` (line 53): OK. Measurability of the adaptive exit time is taken as an explicit hypothesis (measurable `τ`, sets, selector).
- `actualWalkStage_measurable_and_isStoppingTime` (line 64), `actualWalkStage_clock_isStoppingTime` (line 94), `measurable_actualWalkStage` (line 101): OK.
- `actualWalkStage_flag_eq_of_prefix` (line 107), `actualWalkStage_eq_of_prefix` (line 137), `actualWalkStage_observedPast` (line 170), `actualWalkStage_stopped_permanent` (line 186): OK. The stop flag is permanent, which is the intended absorbing semantics.
- `actualWalkStage_ae_all_clocks_finite` (line 207): OK. All clocks are finite on one a.s. event derived from `hexit`, as the docstring says; nothing is postulated per stage.

## SpherePackings.General.Walk.BallStoppedLawComparison
- `law_ae_actualWalkExcursion_shape` (line 26): OK. Excursions from `B_r(c_j)` satisfy the shape bound `max (2r) |end − start|` almost surely.
- `levyProkhorov_ball_stopped_laws_le` (line 50): OK. The hypothesis `hselect` (line 56), `ball x (r/2) ⊆ ball (c_j) r`, is equivalent to `dist x c_j ≤ r/2`: selection is restricted to the inner half-ball, which is what gives `hinside` (lines 87-88). Consistent with `hbuffer` (line 63) and `hpoint` (line 67) for large `ε, δ`; `hsmall` (line 83) needs only `ε + η < rMiddle`; budgets can be small. Remark: the Lévy–Prokhorov distance is bounded by the maximum total mass (Mathlib LevyProkhorovMetric.lean:106), so the bound is informative only when `rWalk + rMiddle + rBrownian < 1`; the hypotheses allow that.

## SpherePackings.General.Walk.CanonicalStoppingRange
- `trajectoryLaw_map_ae_canonicalWalkStoppingSupport_of_range` (line 23): OK. If excursions `0..n` stay within `R` of their starts, then either the flag at `n` is still `false` or the path lies in `canonicalWalkStoppingSupport U (2R) P`. Matches the docstring. `hselect` (line 28, "selector none ⇒ `x ∉ U`") is the right direction for the exit argument. If `R < 0` the premise is false, which is harmless.

## SpherePackings.General.Walk.ClockedWalkExcursion
- `clockedWalkExcursionKernel_curve` (line 24): OK. The curve pushforward of the clocked excursion kernel is the walk excursion kernel.
- `clockedWalkExcursionKernel_endPoint` (line 34): OK. The endpoint law is the pushforward of `discreteHarmonicMeasure` by `pos`. Holds without `hexit`, since both sides use the same `untopD 0` totalization (`ofWalk` and `exitVertex`).

## SpherePackings.General.Walk.DiscreteHarmonicMeasure
- `measurable_exitVertex` (line 21): OK.
- `IsAbsorbedPath.eventually_eq_exitVertex` (line 29): OK.
- `integral_eval_of_isHarmonicAt` (line 46): OK. The hypothesis `hh` for all `a` is equivalent to harmonicity on `A`, because the absorbed kernel at `a ∉ A` is a Dirac mass (trivially harmonic).
- `discreteHarmonicMeasure` (line 67): NOTE. Defined as the pushforward of the absorbed law by `exitVertex A`, and `exitVertex A ω = ω ((exitTime A ω).untopD 0)` (BouRabeeGwynne/DiscreteHarmonicMeasure.lean:25-26). On `{exitTime = ⊤}` this is `ω 0`, so for a chain that may fail to exit the object is a probability measure (instance at line 71) but not the harmonic measure. Every theorem in the batch that uses it carries `hexit`, but the docstring does not say so. Matches the paper's discrete harmonic measure from `x^n` on `∂V_n[B]` (paper/rw-spheres.tex:1507-1508) once `hexit` holds.
- `discreteHarmonicMeasure_isProbabilityMeasure` (line 71): OK.
- `integral_discreteHarmonicMeasure_of_solvesDirichlet` (line 81): OK. `SolvesDirichlet` (SpherePackings/General/MarkovChain/Dirichlet.lean:188) is "harmonic on A, with integrability (so no Bochner junk value 0), and equal to the data on B"; here `B = Aᶜ`, which contains the exit vertex. Measurable `g` and bounded `f` suffice; `g` need not be bounded because it equals `f` on the support. Nonvacuity: `swap_harmonic_integral` below.

## SpherePackings.General.Walk.ExcursionEndpointExtension
- `measurableEmbedding_finite_positions` (line 20): NOTE. The name suggests a finiteness hypothesis; the lemma is the general fact that an injective measurable map whose images of measurable sets are measurable is a `MeasurableEmbedding`. No finiteness is used, and nothing in the repo references it.
- `finiteVertexKernelExtension` (line 30): OK in content. `Function.extend pos κ (dirac ∘ constantState)`; injectivity from the embedding means no `Classical.choice` junk, and off-graph points get constant excursions. The name "finite" is misleading (same point as above).
- `vertexExcursionExtension` (line 68): OK.
- `nextVertexExcursionKernel` (line 112): NOTE. Its meaning matches the docstring (next excursion starts at `c 1`; `nextVertexExcursionKernel_ae_start`, lines 124-128), but nothing outside this file references it, so it is dead code in the General tree.
- `extended_walkExcursionKernel_ae_start` (line 130): OK.

## SpherePackings.General.Walk.ExcursionSteps
- `ClockedWalkExcursion.exists_curve_eq_vertex` (line 27): OK. The duration-0 case is handled correctly: the curve is constant, so `t = 0` works.
- `ClockedWalkExcursion.dist_vertex_le` (line 39): OK.
- `actualWalkStage_step_le_of_range` (line 51): OK. Steps before the stage-`n` clock are at most `2R` when excursions `0..n` are `R`-close to their starts; the triangle inequality through the two vertices gives `2R`.
- NOTE on `curveOscillationLe` (BouRabeeGwynne/ExcursionOscillation.lean:18-19): it means `∀ t, dist (c t) (c 0) ≤ R`, a radius about the start, not the oscillation (diameter) of the curve. A diameter bound `≤ R` implies this predicate, not conversely (radius `≤ R` only gives diameter `≤ 2R`). The batch uses the radius reading consistently, so no statement is wrong, but the name is misleading.

## SpherePackings.General.Walk.FiniteStoppedLawComparisonGood
- `levyProkhorov_reconstructed_stopped_laws_le_of_good` (line 17): OK. The walk-support hypothesis (lines 24-25) is required only on the good event, as the docstring (lines 7-8) says. `η` (line 22) has no sign hypothesis, harmless as in ActualStoppedLawComparison.

## SpherePackings.General.Walk.FreeAbsorbed
- `absorbedKernel_univ` (line 23): OK.
- `law_map_stoppedWalkPath` (line 28): OK. The free chain stopped at its exit from `B` has the law of the chain absorbed outside `B`.
- `law_absorbed_map_eq_law_map` (line 39): OK. Needs `B ⊆ A` and stop-invariance of `F`; no finiteness.
- `exitVertex_stoppedWalkPath` (line 48), `stoppedPolygonalCurve_stoppedWalkPath` (line 54): OK.
- `discreteHarmonicMeasure_eq_law_map` (line 63): OK. Free-chain form of the harmonic measure; holds unconditionally because both sides totalize identically.
- `ae_exit_absorbed_of_free` (line 72): OK.

## SpherePackings.General.Walk.GoodRange
- `dist_endPoint_le_of_goodExcursionPair` (line 21): OK. For active pairs both endpoints lie in the same cell `E k` (diameter ≤ `a`); for stopped pairs the disjunct carries the bound.
- `walk_range_of_goodExcursionPairs` (line 34): OK. The range bound `max R₀ (2a+S)` follows from endpoint closeness, start closeness and the Brownian range `S`. Matches docstring (lines 8-11).
- `curve_ofWalk_shape` (line 84): OK. Vertices before the exit are in the ball (`hB`), the exit vertex is within the stated `R`, and the polygonal curve lies in the convex hull of its vertices (lines 120-123).

## SpherePackings.General.Walk.HarmonicMeasureBridge
- `stoppedPolygonalCurve_map_endPoint` (line 23): OK, unconditional.
- `abs_integral_discreteHarmonicMeasure_sub_le` (line 40): OK. `|E g − target| ≤ η + |f v − target|`. Uses `hexit` and the boundary error only on `Aᶜ`, where the harmonic measure lives almost surely (lines 50-54).
- `abs_integral_discreteHarmonicMeasure_sub_lt` (line 88): OK. Strict version `< η + ρ` from `|f v − target| < ρ`.

## SpherePackings.General.Walk.JointExcursionPasting
- `walkBrownianJointLaw_ae_structure` (line 33): OK. Compatible walk excursions starting at `pos v` with the shape bound; compatible Brownian excursions starting at `z` and within `S`. Matches docstring.
- `walkBrownianJointLaw_ae_walk_range` (line 159): OK.
- `walkBrownianJointLaw_ae_pasted_dist_le` (line 196): OK. Bound `max R₀ (2a+S) + a + S`, consistent with the `hpoint` hypothesis of ActualStoppedLawComparison (line 46).

## SpherePackings.General.Walk.SkeletonKernels
- `measurable_ofWalk` (line 29): OK.
- `clockedWalkExcursionKernel` (line 41): OK. Law of the chain absorbed outside `B`, recorded up to its exit, as documented.
- `clockedWalkExcursionKernel_apply` (line 46), `clockedWalkExcursionKernel_isMarkov` (line 53), `clockedWalkExcursionKernel_ae_start` (line 58): OK.
- `vertexKernelExtension` (line 68): NOTE. Same definition as `finiteVertexKernelExtension` (ExcursionEndpointExtension.lean:30-35). Not referenced anywhere in the repo. The module docstring (lines 10-17) presents this extension as the one the skeleton kernels use, but the copy actually used (WalkSkeletonKernel.lean) is the other one. Harmless duplicate.

## SpherePackings.General.Walk.StoppedCurveMeasurable
- `measurable_curveProjection_polygonalCurve` (line 22): OK.
- `measurable_discreteExitTime` (line 35): OK.
- `measurable_stoppedPolygonalDuration` (line 41): NOTE. `untopD 0` makes the stopped curve constant at `ω 0` on `{exitTime = ⊤}`. This is the totalization documented at `stoppedPolygonalCurve` (BouRabeeGwynne/StoppedCurveLaws.lean:60). Every law statement that uses it carries `hexit`, so the value sits on a null set and cannot change a law. Measurability is unaffected.
- `measurable_stoppedPolygonalCurve` (line 47), `aemeasurable_stoppedPolygonalCurve` (line 54): OK. Measurability needs no finiteness hypothesis, as the docstring says.
- `stoppedPolygonalCurve_map_isProbabilityMeasure` (line 59): OK.

## Nonvacuity examples
Compiled: `Nonvacuity.lean`, from the repo root with `lake env lean ...`. Final run: exit code 0, no errors, no warnings. `#print axioms` output:

```
'swap_harmonic_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Verbatim file:

```lean
import SpherePackings.General.Walk.DiscreteHarmonicMeasure

/-! Scratch nonvacuity check for audit batch 16 (not part of the repository).

A two-state chain on `Bool` that swaps its states, absorbed outside `A = {false}`, satisfies the
hypothesis bundle of `SpherePackings.MarkovChain.integral_discreteHarmonicMeasure_of_solvesDirichlet`
(almost sure finite exit, measurable and bounded solution, `SolvesDirichlet`), and the conclusion
then gives a nontrivial value. -/

open MeasureTheory ProbabilityTheory Set
open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork BouRabeeGwynne.TrajectoryCoupling
open SpherePackings.MarkovChain

/-- The swap kernel: `swapKernel b` is the point mass at `!b`. -/
noncomputable abbrev swapKernel : Kernel Bool Bool :=
  Kernel.deterministic (fun b : Bool => !b) (measurable_of_countable _)

lemma swap_A_measurable : MeasurableSet ({false} : Set Bool) := measurableSet_singleton false

/-- The absorbed chain from every start has second state `true` almost surely. -/
lemma swap_absorbed_eval_one (v : Bool) :
    ∀ᵐ ω ∂law (absorbedKernel swapKernel swap_A_measurable) v, ω 1 = true := by
  have hdirac : absorbedKernel swapKernel swap_A_measurable v = Measure.dirac true := by
    cases v with
    | false =>
      rw [absorbedKernel_of_mem swapKernel swap_A_measurable (mem_singleton false)]
      simp [Kernel.deterministic_apply]
    | true =>
      rw [absorbedKernel_of_not_mem swapKernel swap_A_measurable
        (by simp : true ∉ ({false} : Set Bool))]
  have hmap := law_map_eval_one (absorbedKernel swapKernel swap_A_measurable) v
  rw [hdirac] at hmap
  have hae : ∀ᵐ x ∂(law (absorbedKernel swapKernel swap_A_measurable) v).map
      (fun ω : ℕ → Bool => ω 1), x = true := by
    rw [hmap]
    exact (MeasureTheory.ae_dirac_iff (measurableSet_singleton true)).mpr rfl
  exact MeasureTheory.ae_of_ae_map (measurable_pi_apply 1).aemeasurable hae

lemma swap_exit_ne_top (v : Bool) :
    ∀ᵐ ω ∂law (absorbedKernel swapKernel swap_A_measurable) v,
      exitTime {false} ω ≠ ⊤ := by
  filter_upwards [swap_absorbed_eval_one v] with ω hω
  have hle : exitTime {false} ω ≤ ((1 : ℕ) : WithTop ℕ) :=
    (exitTime_le_iff {false} ω 1).mpr ⟨1, le_rfl, by simp [hω]⟩
  exact ne_top_of_le_ne_top WithTop.coe_ne_top hle

/-- Boundary data `g` (equal to `2` at `true`). -/
noncomputable def swapBoundary : Bool → ℝ := fun b => if b = true then 2 else 0

lemma swap_solvesDirichlet :
    SolvesDirichlet swapKernel {false} ({false} : Set Bool)ᶜ swapBoundary (fun _ => 2) := by
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · have ha' : a = false := ha
    subst ha'
    refine ⟨integrable_const 2, ?_⟩
    simp [Kernel.deterministic_apply]
  · have hb' : b = true := by simpa using hb
    subst hb'
    simp [swapBoundary]

/-- The bundle of the discrete harmonic measure theorem holds for the swap chain, and the
conclusion gives the value `2` at the start `false`. -/
theorem swap_harmonic_integral : ∫ w, swapBoundary w ∂(SpherePackings.MarkovChain.discreteHarmonicMeasure swapKernel
    {false} swap_A_measurable false) = 2 :=
  integral_discreteHarmonicMeasure_of_solvesDirichlet swapKernel {false} swap_A_measurable
    swap_exit_ne_top (measurable_of_countable _) measurable_const ⟨2, fun _ => by norm_num⟩
    swap_solvesDirichlet false

#print axioms swap_harmonic_integral
```

What it shows: for a non-degenerate two-state chain (`V = Bool`, `A = {false}`, swap kernel), the hypothesis bundle of `integral_discreteHarmonicMeasure_of_solvesDirichlet` is jointly satisfiable: almost sure finite exit (`swap_exit_ne_top`), measurable `g` and bounded `f = 2`, and `SolvesDirichlet` with boundary `Aᶜ` (`swap_solvesDirichlet`). The conclusion then gives `∫ g d(harmonic measure from false) = 2`. The harmonic measure from `false` is the Dirac mass at `true` (exit at time 1), so the value `2 = g(true)` is nontrivial and not forced to be zero.

Not done:
- No nonvacuity example for `levyProkhorov_actual_stopped_laws_le_of_shape` or `levyProkhorov_ball_stopped_laws_le`. Their bundles include a Brownian law `μ`, the walk-Brownian coupling, and the probability bounds `hfailure`, `htail`, `hosc` tied to budgets. Building one needs the coupling for a concrete chain, which I did not attempt within the 30-minute box. Indirect evidence only: Section4General/Theorem41.lean:119 applies `levyProkhorov_ball_stopped_laws_le` to the walks from `theorem41_hypotheses_satisfiable` (SpherePackings/Support/Guards/AssumptionDLattice.lean:130). I read that call site but did not compile it or check the hypotheses it discharges.
- `theorem41_hypotheses_satisfiable` supplies walks `W`, `near`, `δ`, `μ` with AssumptionD, a Lipschitz domain and `IsStandardBrownianLaw`, but not the probability bounds.
- Four earlier scratch compiles failed because of my own scratch-file errors (an instance on a `def` rather than an `abbrev`, a name clash with `FiniteConductanceNetwork.discreteHarmonicMeasure` under the opens, and the `ae_map_iff` predicate). None reflects a repository issue. Only the final version above is reported.
