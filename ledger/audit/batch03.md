# Audit batch 3
| Module | Verdict | Summary |
|---|---|---|
| BouRabeeGwynne.StoppedBrownianMeasurable | OK | Exit time, representative, curve and law are measurable for every path; the τ=∞ totalization only affects a null set (documented). |
| BouRabeeGwynne.ContinuousExitProperties | OK | Finite exit is attained, the endpoint lies on the frontier; hypotheses (open U, finite exit, start inside) are the needed ones. |
| BouRabeeGwynne.UnitCurveExit | OK | `min _ 1` removes the ⊤ junk; capped exit time, representative and measurability are correct. |
| BouRabeeGwynne.IndependentCoordinatePairs | OK | Standard regrouping lemma; hypotheses are jointly satisfiable by i.i.d. coordinates. |
| BouRabeeGwynne.BrownianWeakMarkov | OK | Deterministic-time future increments are independent of the whole past; matches docstring. |
| BouRabeeGwynne.BrownianLawUniqueness | OK | `IsStandardBrownianLaw` = Mathlib pre-Brownian coordinates + a.s. continuity + coordinate independence; uniqueness correct. |
| BouRabeeGwynne.BrownianScaling | OK | `r⁻¹ • ω(r²·)` is the correct parabolic scaling; `0⁻¹ = 0` junk at r = 0 is guarded by `0 < r` in every theorem. |
| BouRabeeGwynne.BrownianExitStoppingTime | OK | First exit is a stopping time for the (non-augmented) natural filtration; matches docstring. |
| BouRabeeGwynne.BrownianFiniteStopping | OK | Strong Markov factorization for finitely valued stopping times; docstring says so explicitly. |
| BouRabeeGwynne.BrownianGaussianReference | OK | Translated marginals are N(z, tI) and are ≪ N(0, I) for t > 0; matches. |
| BouRabeeGwynne.BrownianUniformLanding | OK | Uniform positive landing probability over ‖c‖ ≤ 2; open-positive marginal, d = 0 included. |
| BouRabeeGwynne.BrownianScaledLanding | OK | Parabolic rescaling of the landing bound with dist(c, x) ≤ 2r; correct. |
| BouRabeeGwynne.ContinuousPathRange | OK | Range events are closed, increasing and exhaust the paths; tightness statement correct. |
| BouRabeeGwynne.BrownianLandingRange | NOTE | Range bound is on the displacement ‖ω t‖ from the start x (walk x + ω), not from the origin; the docstring is accurate only in that reading. |
| BouRabeeGwynne.BrownianExcursionRange | OK | Time/range links via `toNNReal` with the needed finite-exit hypotheses; matches docstring. |
| BouRabeeGwynne.BrownianMoments | OK | Fourth moments 3v² and 3\|s−t\|² are correct, including v = 0. |
| BouRabeeGwynne.GaussianIncrementBounds | OK | Markov bound 3v²/r⁴ with r > 0 required and given. |
| BouRabeeGwynne.BrownianQuadraticMoments | OK | E[ω_t^i ω_t^j] = tδ_ij, E‖B_t‖⁴ ≤ 3d²t², and ‖x‖⁴ ≤ d Σ x_i⁴ are correct. |
| BouRabeeGwynne.BrownianPredictableMoments | NOTE | Predictable linear/quadratic identities carry no integrability hypothesis on C; the Bochner integral is junk 0 when C is not integrable, so "= 0" holds in Lean but is meaningful only for integrable C. |
| BouRabeeGwynne.Harmonic | NOTE | `IsHarmonicOn` is documented for open sets but accepts arbitrary U; for non-open U the Δ clause at boundary points uses global Fréchet derivatives (junk 0 where h is not C²). Every caller that matters is open or globally C². |
| BouRabeeGwynne.BrownianHessianGenerator | NOTE | Both statements hold without a C²-at-x hypothesis; where f is not twice differentiable at x both sides are Lean junk 0, so the content requires C² at x. |
| BouRabeeGwynne.BrownianTaylorBound | NOTE | Remainder hypothesis hR is global in y, although the docstring describes a compact neighbourhood; satisfiable for compactly supported C² f (checked). |
| BouRabeeGwynne.BrownianPredictableTaylor | OK | Integrability of F is derived, and the linear/quadratic terms carry integrability hypotheses; matches docstring. |
| BouRabeeGwynne.HessianTaylorRemainder | OK | Oscillation remainder bound with constant ε (weaker than the true ε/2, so sound); uniform and compact-support versions match docstrings; nonvacuity compiled. |
| BouRabeeGwynne.BrownianStoppedStep | OK | Uniform one-step bound with C independent of t, s, X, A; f is globally C², so Δ is classical; nonvacuity compiled with a nonzero f. |
| BouRabeeGwynne.DyadicExitApprox | OK | `nnrealApproxSeq τ n ω = ⌈τ ω · 2ⁿ⌉ / 2ⁿ` with no truncation junk; matches the docstring formula. The vendored upstream source is not in the repo, so provenance is not diffable here. |
| BouRabeeGwynne.BrownianStoppingApprox | OK | Ceiling dyadic times; the range is finite and covers all dyadic values ≤ N; matches docstring. |
| BouRabeeGwynne.BrownianStoppedSum | OK | Telescoping identity is right, including the upper-approximation endpoint and the crossing step; C is uniform over σ, N, z, n. |

## BouRabeeGwynne.StoppedBrownianMeasurable
- `measurable_continuousExitTime` (line 24): matches; countable dense S of ℝ≥0∞ gives the exact decomposition of {τ < a}.
- `measurable_stoppedBrownianRepresentative` (line 64): matches.
- `measurable_stoppedBrownianCurve` (line 81): matches; the totalization for τ = ∞ (curve constant at z) is documented and does not affect measurability.
- `stoppedBrownianLaw_isProbabilityMeasure` (line 86): matches.

## BouRabeeGwynne.ContinuousExitProperties
- `continuousExitTime_le_of_not_mem` (line 23), `mem_of_lt_continuousExitTime` (line 27), `continuousExitTime_eq_zero_of_not_mem` (line 32): match the infimum-over-exit-times definition in `StoppedCurveLaws.lean:67`.
- `continuousExitTime_not_mem` (line 37): matches; openness of U gives a closed exit set, so the infimum is attained when finite.
- `continuousExitTime_mem_frontier` (line 59): matches; uses start inside U and finite exit.
- `stoppedBrownianCurve_endPoint` (line 79), `stoppedBrownianCurve_endPoint_mem_frontier` (line 86): match.

## BouRabeeGwynne.UnitCurveExit
- `extendUnitCurve` (line 20): constant extension beyond 1 via `projIcc`; matches.
- `unitCurveExitTime` (line 34): `(min τ 1).toNNReal` is finite, so no ⊤ junk; matches "first unit-time exit, capped at one".
- `unitCurveExitTime_not_mem_of_exists` (line 72): matches (exit point lies outside U when some value does).
- `unitCurveExitRepresentative` (line 117), `unitCurveExitProjection` (line 125): match.

## BouRabeeGwynne.IndependentCoordinatePairs
- `indepFun_vectors_of_independent_coordinate_pairs` (line 17): matches; standard lemma, hypotheses satisfiable.

## BouRabeeGwynne.BrownianWeakMarkov
- `shiftedBrownianPath` (line 18): `s ↦ ω(t+s) − ω t`; matches.
- `standardBrownianLaw_indepFun_shift` (line 32): future increments ⊥ whole past at deterministic t; matches docstring.

## BouRabeeGwynne.BrownianLawUniqueness
- `standardBrownianLaw_unique` (line 67), `standardBrownianLaw_shift` (line 77), `standardBrownianLaw_map_shift` (line 108): match.

## BouRabeeGwynne.BrownianScaling
- `scaledBrownianPath` (line 16): spatial scale r⁻¹, time scale r²; matches.
- `standardBrownianLaw_scale` (line 35), `standardBrownianLaw_map_scale` (line 72): require 0 < r; match.

## BouRabeeGwynne.BrownianExitStoppingTime
- `brownianNaturalFiltration` (line 17): raw natural filtration of evaluations; no augmentation, consistent with the statements.
- `restrictBrownianPath` (line 22): matches.
- `continuousExitTime_le_iff_not_mapsTo` (line 34): correct equivalence.
- `isStoppingTime_continuousExitTime` (line 54): matches.

## BouRabeeGwynne.BrownianFiniteStopping
- `brownianNaturalFiltration_eq_comap` (line 19), `standardBrownianLaw_indepFun_shiftedPath` (line 25): match.
- `standardBrownianLaw_finiteStopping_inter` (line 87): strong Markov for finite-range σ; matches docstring.
- `standardBrownianLaw_finiteStopping_map_restrict` (line 132): `μ A • μ` form; correct for probability μ.

## BouRabeeGwynne.BrownianGaussianReference
- `standardBrownianLaw_map_translated_eval` (line 45): marginal is N(z, tI); matches (variance t, not standard deviation).
- `standardBrownianLaw_translated_eval_absolutelyContinuous` (line 71): matches. Absolute continuity is proved for each z with one fixed reference N(0, I); there is no quantitative uniform density bound, so "uniformly ... qualitative" should be read as "one reference measure for all translations".

## BouRabeeGwynne.BrownianUniformLanding
- `standardBrownianLaw_eval_one_isOpenPosMeasure` (line 19): matches.
- `standardBrownianLaw_uniform_landing_probability` (line 37): p depends only on κ; matches docstring; nonvacuity compiled.

## BouRabeeGwynne.BrownianScaledLanding
- `standardBrownianLaw_uniform_scaled_landing_probability` (line 16): matches; p is independent of r, x, c.

## BouRabeeGwynne.ContinuousPathRange
- `pathRangeEvent` (line 16): `‖ω t‖` is the Euclidean norm from the origin; matches.
- `measure_compl_pathRangeEvent_tendsto_zero` (line 40), `exists_pathRangeEvent_compl_lt` (line 53): match.

## BouRabeeGwynne.BrownianLandingRange
- `pathRangeEvent_of_scaledBrownianPath` (line 17): scaled-to-original bound is correct (‖ω t‖ = r·‖ω'(t/r²)‖).
- `standardBrownianLaw_uniform_scaled_landing_and_range_probability` (line 37): NOTE. The range event bounds the displacement from the start x, since the walk is x + ω. The docstring "keeping the whole preceding path within a fixed multiple of the scale" is accurate in that reading only; the statement itself is correct and p, L are chosen before r, x, c.

## BouRabeeGwynne.BrownianExcursionRange
- `lt_continuousExitTime_of_mem_Icc` (line 14), `mem_range_stoppedBrownianRepresentative` (line 27), `stoppedBrownianRepresentative_not_all_mem_of_visit` (line 49): match; the τ = 0 and τ = ∞ cases are handled.

## BouRabeeGwynne.BrownianMoments
- `gaussianReal_fourth_moment` (line 63): E X⁴ = 3v² for variance v, including v = 0; matches.
- `brownianProjectiveFamily_increment_fourth_moment` (line 83), `preBrownian_increment_fourth_moment` (line 98): 3\|s−t\|²; match.

## BouRabeeGwynne.GaussianIncrementBounds
- `gaussianReal_lintegral_abs_fourth` (line 26), `hasLaw_gaussian_measure_abs_ge_le` (line 47): Markov bound 3v²/r⁴; correct with r > 0.
- `brownianProjectiveFamily_measure_increment_ge_le` (line 65): matches.

## BouRabeeGwynne.BrownianQuadraticMoments
- `standardBrownianLaw_integral_coordinate_mul` (line 32): covariance tδ_ij; matches.
- `standardBrownianLaw_integral_quadratic` (line 51): E[Σ H_ij ω_i ω_j] = t·tr H; matches.
- `euclidean_norm_fourth_le_coordinate_fourth` (line 69), `standardBrownianLaw_integral_norm_fourth_le` (line 95): correct constants (3d²t²).

## BouRabeeGwynne.BrownianPredictableMoments
- `standardBrownianLaw_indepFun_shift_coefficient` (line 19): matches.
- `standardBrownianLaw_integral_predictable_linear` (line 33): NOTE. No integrability hypothesis on C. The statement is true in Lean (if C is not integrable, the product is not integrable either for s > 0, so both sides are junk 0), but "zero expectation" is meaningful only for integrable C. Downstream always supplies integrability (`BrownianPredictableTaylor`).
- `standardBrownianLaw_integral_predictable_quadratic` (line 53): NOTE, same reason as above.
- `standardBrownianLaw_integral_predictable_trace_zero` (line 81): has integrability hypotheses; correct cancellation.

## BouRabeeGwynne.Harmonic
- `IsHarmonicOn` (line 17): classical C² harmonicity, matching the docstring for open U. NOTE: the definition accepts non-open U; there `Δ h x` at boundary points uses global Fréchet derivatives, so it is junk 0 wherever h is not globally twice differentiable. The predicate then does not mean classical harmonicity on the closed set. The callers that matter (`BrownianStoppedStep`, `BrownianStoppedSum`, `BrownianHarmonicExit` with `IsOpen U`) are fine: the first two assume `ContDiff ℝ 2 f` globally, and the last assumes U open.
- `HarmonicNearClosure` (line 28): `∃ W open, closure U ⊆ W ∧ IsHarmonicOn h W` matches Theorem B(a) (`rw-spheres.tex:297–303`).
- `ContinuousOnClosure` (line 40): `ContinuousOn h (closure U)` matches Theorem B(b).

## BouRabeeGwynne.BrownianHessianGenerator
- `bilinear_eq_sum_euclidean_coordinates` (line 19): matches.
- `standardBrownianLaw_integral_hessian` (line 42): NOTE. Holds with no C²-at-x hypothesis. For f not twice differentiable at x, `fderiv (fderiv f) x` and `Δ f x` are both Lean junk 0, so the identity is unconditionally true but says nothing there. For C² f at x it is the correct E[D²f(x)(B_t,B_t)] = tΔf(x).
- `standardBrownianLaw_integral_hessian_eq_zero` (line 60): same junk at boundary points x ∈ U when U is not open; for open U harmonicity gives the correct zero.

## BouRabeeGwynne.BrownianTaylorBound
- `standardBrownianLaw_taylor_expectation_bound` (line 79): NOTE. The remainder hypothesis hR is required for all y ∈ Euc d, while the docstring describes "the compact neighbourhood". The statement is correct and not vacuous: `uniform_taylor_remainder_of_contDiff_compactSupport` gives hR for any compactly supported C² f (checked by compiling the example below). If f is not differentiable at x, hR forces |f(x+y) − f x| = O(|y|²), so the junk Δ f x = 0 does not invalidate the bound.
- Constants ε d t and C·3d²t² match E‖B_t‖² = dt and E‖B_t‖⁴ ≤ 3d²t².

## BouRabeeGwynne.BrownianPredictableTaylor
- `standardBrownianLaw_integrable_predictable_linear` (line 20), `standardBrownianLaw_integrable_predictable_quadratic` (line 31): integrability from the independence of coefficients; match.
- `standardBrownianLaw_predictable_taylor_bound` (line 52): matches; the conclusion includes `Integrable F`, derived rather than assumed.

## BouRabeeGwynne.HessianTaylorRemainder
- `taylor_remainder_le_of_hessian_oscillation` (line 24): bound ε‖y‖² (weaker than the true ε/2, so sound); needs only C² on the convex set S, with no third derivative, matching the docstring.
- `quadratic_remainder_le_quadratic_add_quartic` (line 72): correct split at radius r.
- `uniform_taylor_remainder_of_uniformContinuous_hessian` (line 95): matches.
- `uniform_taylor_remainder_of_contDiff_compactSupport` (line 138): matches; nonvacuity compiled with a nonzero f.

## BouRabeeGwynne.BrownianStoppedStep
- `standardBrownianLaw_stopped_harmonic_step_bound` (line 29): correct one-step bound, uniform over t, s, X, A. The indicator form |E[1_A(f(X+Δ) − f(X))]| ≤ εds + Cs² follows from the zero linear term (F_t-measurable coefficient against independent mean-zero Δ) and the zero trace on A. f is globally C² (`ContDiff ℝ 2 f`), so Δ f is classical everywhere. Nonvacuity compiled with a nonzero compactly supported f.

## BouRabeeGwynne.DyadicExitApprox
- `nnrealApproxSeq` (line 31): `⌈τ·2ⁿ⌉ / 2ⁿ` in ℝ≥0 with `WithTop.map`, no truncation or subtraction junk; matches the docstring formula.
- `nnrealApproxSeq_le_iff` (line 35), `nnrealApproxSeq_isStoppingTime` (line 46), `nnrealApproxSeq_tendsto` (line 106): correct.
- Not a file under `Upstream/`. The header says it is vendored from RemyDegenne/brownian-motion, but that source is not in the repository, so the provenance claim could not be diffed; the definition and lemma statements match the stated formula.

## BouRabeeGwynne.BrownianStoppingApprox
- `dyadicStoppingTime` (line 19): `⌈σ·2ⁿ⌉/2ⁿ`; matches.
- `dyadicStoppingRange` (line 50): covers all dyadic values ≤ N (uses `Finset.range (⌈N·2ⁿ⌉ + 1)`); matches.
- `dyadicStoppingTime_mem_range` (line 55), `le_dyadicStoppingTime`, `isStoppingTime_dyadicStoppingTime`, `tendsto_dyadicStoppingTime`: match.

## BouRabeeGwynne.BrownianStoppedSum
- `measurableSet_before_nnreal_stopping` (line 51): `{t < σ}` ∈ F_t; correct.
- `standardBrownianLaw_dyadic_stopped_harmonic_bound` (line 61): matches the docstring. The telescoping identity is right: j < ⌈σ2ⁿ⌉ ⇔ j/2ⁿ < σ, and each crossing step starts at a time t_j < σ where the path is still in U. C is uniform over σ, N, z, n. Hypotheses are satisfiable (σ = min(exit time, N)); not compiled.

## Nonvacuity examples
Scratch file: `Nonvacuity.lean`
Compile command (from the repository root, as specified):
`lake env lean Nonvacuity.lean`

Result: **compiled with no errors**. One deprecation warning (`EuclideanSpace.norm_single` is deprecated in favour of `PiLp.norm_single`). A copy with `#print axioms` appended (`NonvacuityAxioms.lean`) reports `BouRabeeGwynne.nv_cutoff` and `BouRabeeGwynne.nv_harmonic_x0` depend only on `[propext, Classical.choice, Quot.sound]`.

```lean
import BouRabeeGwynne.BrownianStoppedStep
import BouRabeeGwynne.BrownianUniformLanding
import BouRabeeGwynne.EuclideanWienerLaw
import BouRabeeGwynne.HarmonicCutoff
import BouRabeeGwynne.PolynomialAnalyticLaplacian

open MeasureTheory Set Metric
open scoped NNReal ENNReal

namespace BouRabeeGwynne

/-- The standard Brownian predicate used throughout the batch is satisfied by the Wiener law. -/
example (d : ℕ) : IsStandardBrownianLaw (euclideanWienerLaw d) :=
  isStandardBrownianLaw_euclideanWienerLaw d

/-- Unit-time landing hypotheses are satisfied at `d = 2` by the Wiener law. -/
example : ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧ ∀ c : Euc 2, ‖c‖ ≤ 2 →
    ENNReal.ofReal p ≤ euclideanWienerLaw 2 {ω | ω 1 ∈ ball c 1} :=
  standardBrownianLaw_uniform_landing_probability
    (isStandardBrownianLaw_euclideanWienerLaw 2) one_pos

/-- The coordinate `x₀` is a harmonic polynomial on all of `ℝ²`. -/
lemma nv_harmonic_x0 : IsHarmonicOn (polynomialEval (MvPolynomial.X (0 : Fin 2))) univ :=
  isHarmonicOn_polynomialEval_of_laplacian_eq_zero _
    (by simp [polynomialLaplacian, Fin.sum_univ_two]) _

/-- A genuinely nonzero compactly supported `C²` function, harmonic on an open set `V ∋ 0`,
obtained by cutting off `x₀` with the repository's harmonic cutoff. -/
lemma nv_cutoff : ∃ (g : Euc 2 → ℝ) (V : Set (Euc 2)), IsOpen V ∧ (0 : Euc 2) ∈ V ∧
    ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ IsHarmonicOn g V ∧
      g (EuclideanSpace.single 0 (1 / 2 : ℝ)) ≠ 0 := by
  obtain ⟨g, V, hV, hKV, -, hg, hgc, -, heq, hgh⟩ :=
    IsHarmonicOn.exists_compactSupport_eq_near_compact nv_harmonic_x0
      (isCompact_closedBall (0 : Euc 2) 1) isOpen_univ (subset_univ _)
  have hp : (EuclideanSpace.single 0 (1 / 2 : ℝ) : Euc 2) ∈ closedBall (0 : Euc 2) 1 := by
    rw [mem_closedBall, dist_zero_right, EuclideanSpace.norm_single]
    norm_num
  refine ⟨g, V, hV, hKV (mem_closedBall_self zero_le_one), hg, hgc, hgh, ?_⟩
  rw [heq (hKV hp)]
  simp [polynomialEval]

/-- The hypotheses of the one-step stopped harmonic bound are met by a nonzero function
under the Wiener law (the bound gives a constant `C ≥ 0`). -/
example : ∃ C : ℝ, 0 ≤ C := by
  obtain ⟨g, V, hV, hKV, hg, hgc, hgh, hne⟩ := nv_cutoff
  obtain ⟨C, hC, -⟩ := standardBrownianLaw_stopped_harmonic_step_bound
    (isStandardBrownianLaw_euclideanWienerLaw 2) hg hgc hgh one_pos
  exact ⟨C, hC⟩

/-- The global quartic-tail remainder hypothesis of `standardBrownianLaw_taylor_expectation_bound`
holds for a nonzero compactly supported `C²` function, with `ε = 1` at the starting point `0`. -/
example : ∃ (g : Euc 2 → ℝ) (C : ℝ), ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
    g (EuclideanSpace.single 0 (1 / 2 : ℝ)) ≠ 0 ∧ 0 ≤ C ∧ ∀ y : Euc 2,
      |g (0 + y) - g 0 - fderiv ℝ g 0 y - (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ g) 0 y y| ≤
        1 * ‖y‖ ^ 2 + C * ‖y‖ ^ 4 := by
  obtain ⟨g, V, hV, hKV, hg, hgc, hgh, hne⟩ := nv_cutoff
  obtain ⟨C, hC, hR⟩ := uniform_taylor_remainder_of_contDiff_compactSupport hg hgc one_pos
  exact ⟨g, C, hg, hgc, hne, hC, fun y ↦ hR 0 y⟩

end BouRabeeGwynne
```

What the compiled examples show:
- **Standard Brownian predicate (`IsStandardBrownianLaw`)**: satisfied by `euclideanWienerLaw d` for every `d`, via the existing `isStandardBrownianLaw_euclideanWienerLaw`. Every Brownian theorem in the batch with a `μ` hypothesis is therefore not vacuous.
- **Landing hypothesis**: `standardBrownianLaw_uniform_landing_probability` is instantiated at the Wiener law with `d = 2` and `κ = 1`, giving a concrete `p`.
- **Harmonic bundle (`nv_cutoff`)**: there is a *nonzero* `g : ℝ² → ℝ`, compactly supported and `C²`, harmonic on an open `V ∋ 0`, with `g ≠ 0` at `(1/2) e₀`. It is the repository's harmonic cutoff of the harmonic polynomial `x₀`. So the bundle `ContDiff ℝ 2 f ∧ HasCompactSupport f ∧ IsHarmonicOn f U` in `standardBrownianLaw_stopped_harmonic_step_bound` and `standardBrownianLaw_dyadic_stopped_harmonic_bound` is satisfiable beyond the trivial `f = 0`.
- **Step bound**: the one-step stopped harmonic bound applies to that nonzero `g` under the Wiener law (the example extracts `C ≥ 0`).
- **Taylor remainder bundle**: the global-in-`y` remainder hypothesis of `standardBrownianLaw_taylor_expectation_bound` holds for the same nonzero `g` with `ε = 1`.

Not attempted (time): a nonvacuity instance for the dyadic-bound stopping-time bundle. Its hypotheses are satisfiable in principle by `σ = min(exit time, N)`, but I did not compile that.

## Checks not requiring a verdict
- No `sorry`, `axiom`, or `set_option` changes in the batch, except the `maxHeartbeats 400000` on `HessianTaylorRemainder.lean:135` (an elaboration setting, not a semantic one).
- Paper and docstring cross-checks: `Harmonic.lean` Theorem B(a)/(b) docstrings match `paper/rw-spheres.tex:297–303`; `ContinuousExitProperties` and `BrownianStoppedSum` docstrings match the Section 4 setting (`rw-spheres.tex:1480–1490`).
