# Audit batch 10
| Module | Verdict | Summary |
|---|---|---|
| BouRabeeGwynne.Section3TheoremBPartA | OK | `theoremB_part_a` proves the Theorem B(a) target `TheoremBPartAStatement`; the statement is faithful to paper Theorem A (Dirichlet), item (a). |
| BouRabeeGwynne.Section4BallHarmonicMeasure | NOTE | Exit-measure lemmas are correct; `hcont : Continuous h` is an extra hypothesis the paper does not need (harmless for the collar-lemma user, which passes a polynomial `h`). |
| BouRabeeGwynne.ClockedExcursionRange | NOTE | `curveOscillationLe R` means "distance from the start is ≤ R", not pairwise oscillation; the stated constants `2r+2·mesh` are correct for that meaning. |
| BouRabeeGwynne.SelectedExcursionOscillation | NOTE | Same naming point (`curveOscillationLe`); Brownian `2r` and walk `2r+2·mesh` bounds are correct. |
| BouRabeeGwynne.JointExcursionPasting | NOTE | Same naming point; the `R + a + S` pasted-distance bound follows by the triangle inequality through start points. |
| BouRabeeGwynne.ActualStoppedLawComparison | NOTE | Statement is non-vacuous; junk values for non-exiting paths and `innerDomain U = univ` are harmless; the `mesh` parameter is a step bound (downstream instantiates it with `2·T.mesh`), not the tile mesh. |
| BouRabeeGwynne.BrownianExitReference | OK | Reference law, its probability property, and the absolute-continuity theorem match the docstrings. |
| BouRabeeGwynne.ContinuityCells | OK | Disjoint bounded measurable cells with null frontier and diameter `< ε` covering a compact set; no junk. |
| BouRabeeGwynne.BrownianContinuityCells | OK | One common cell family gives null exit-law mass on every cell frontier for every start in every `U j`; non-vacuous. |
| BouRabeeGwynne.HarmonicCutoff | OK | Compactly supported `C²` cutoff agreeing with `h` on an open neighbourhood of `K`; harmonicity transfers by locality. |
| BouRabeeGwynne.HarmonicNearClosureBrownianExit | OK | `HarmonicNearClosure` (`closure U ⊆ W`, `W` open) gives the Brownian harmonic exit representation; matches paper's Theorem A(a) mechanism. |
| BouRabeeGwynne.Section4BrownianBallHarmonicMeasure | NOTE | `brownianSpatialHarmonicMeasure` is total: for `z ∉ U` it is `δ_z` (harmless, all lemmas take `z ∈ U`); `hcont` is an extra global-continuity hypothesis. |
| BouRabeeGwynne.PolynomialLaplacian | OK | `polynomialLaplacian = ∑ ∂ᵢ∂ᵢ`, `polynomialSquaredNorm = ∑ Xᵢ²`; Euler-type identity for `Δ(|x|²p)` is the standard one. |
| BouRabeeGwynne.PolynomialAnalyticLaplacian | OK | `polynomialEval` is evaluation at coordinates; `Δ` is Mathlib's `InnerProductSpace.laplacian` (as in `IsHarmonicOn`), so the algebraic and analytic Laplacians agree. |
| BouRabeeGwynne.PolynomialBoundaryApproximation | OK | Stone–Weierstrass density of polynomials in `C(K)` for compact `K`; statement is `∀ x : K, |p x − f x| < ε`. |
| BouRabeeGwynne.PolynomialDegree | OK | Degree lowering and degree preservation of `q ↦ Δ(Aq)` for `deg A ≤ 2`; faithful. |
| BouRabeeGwynne.PolynomialBallIdentity | OK | A polynomial vanishing on a nonempty open ball is zero; `0 < r` is hypothesised and needed. |
| BouRabeeGwynne.Upstream.KolmogorovExtension | OK | Vendored Degenne–Pfaffelhuber projective limit; standard Kolmogorov extension, probability instance needs `Nonempty ι` (present). |
| BouRabeeGwynne.BrownianProjectiveLaw | OK | `brownianProjectiveLaw` is the projective limit of Mathlib's `BrownianReal.projectiveFamily` (centred Gaussian, covariance `min(s,t)`); `IsPreBrownianReal` is Mathlib's notion; continuity is not claimed. |
| BouRabeeGwynne.Upstream.BrownianMotion.Continuity.KolmogorovChentsov | NOTE | Statements and the `holderSet`/`holderModification` definitions match Kolmogorov–Chentsov; `holderModification` takes the junk value `hE.some` off `U` (harmless, only `t ∈ U` is asserted). Proofs skimmed, not read. |

## BouRabeeGwynne.Section3TheoremBPartA
- `theoremB_part_a` (line 14): proves `TheoremBPartAStatement` (`BouRabeeGwynne/TheoremBStatement.lean`), which is the Theorem B(a) statement; matches paper Theorem A (Dirichlet problem), item (a) (paper lines 301, `item:cont-neighborhood`). `PaperRegularity` = (I) `d = 2` ∨ (II) ∨ (III) matches paper items `item:planarity`, `item:vol`, `item:diam` (paper lines 269–272). The case split is on the disjunction; no extra hypothesis.

## BouRabeeGwynne.Section4BallHarmonicMeasure
- `spatialHarmonicMeasure` (line 19): the discrete harmonic (exit) measure of the finite conductance walk from `v`, mapped to `Euc d` by `pos`; probability by the instance at line 26. Matches the exit law of the paper's walk (conductances `vol_{d-1}/‖w−v‖`, paper eq. `eq:conductance`, line 233). Total off `finiteInterior`, where it is `δ_{pos v}`; the integral identity still holds there (boundary value), so no harm.
- `integral_spatialHarmonicMeasure` (line 34): `∫ h dμ_v = dirichletSolution (h∘pos) v`; correct.
- `abs_integral_spatialHarmonicMeasure_sub_le` (line 50): `|∫f dμ_v − target| ≤ η + |DS(h∘pos)(v) − target|` from boundary error `η` on `boundaryVertices` and total mass 1; correct (exit vertices are exactly `closedVertices \ finiteInterior`).
- `eventually_spatialHarmonicMeasure_harmonic_error` (line 74): matches paper Theorem A(a) in quantitative form (uniform `η` over interior `v`); conclusion is non-vacuous (existence of boundary access is derived). NOTE: `hcont : Continuous h` (global) is an extra hypothesis; the exit measures are finitely supported so integrability is automatic. The collar-lemma user `Section4BallExitConvergence.lean:55` passes a polynomial `h` (its harmonicity witness at `SpherePackings/Support/Section4/BallExitConvergence.lean:48` is `polynomialEval P`); I did not check the other user (`SpherePackings/Support/Section4/HarmonicMeasure.lean:89`), so the harmlessness claim is for the collar user only.
- `boundary_pos_mem_cthickening_frontier` (line 121): an external vertex `w` lies within `2·mesh` of `frontier U`. Checked: `w` adjacent to interior `v` with a common facet point `x`, so `dist(pos v,pos w) ≤ diam P_v + diam P_w ≤ 2·mesh`; the segment from `pos v ∈ U` to `pos w ∉ U` crosses `frontier U`. Correct.
- `closedVertices_pos_mem_enlarged_ball` (line 130), `closedVertices_segment_subset_enlarged_ball` (line 145): same `2·mesh` overshoot; correct.
- `abs_integral_sub_integral_le_of_ae_mem_compact` (line 160): correct for probability `μ` with `μ(S)=1`, `S` compact.
- `eventually_spatialHarmonicMeasure_collar_error` (line 181): `hnear` on `cthickening δ (frontier U)` plus `mesh ≤ δ/2` eventually gives error `≤ η + ρ`; correct. Same `hcont` remark.

## BouRabeeGwynne.ClockedExcursionRange
- `clockedWalkExcursionKernel_ae_mem_convex` (line 22): a.e. excursion stays in a closed convex set containing the vertex positions; correct.
- `ambient_clockedExcursion_ae_mem_enlarged_ball` (line 43): a.e. curve in `closedBall c (r + 2·mesh)`; matches the overshoot lemma; hypotheses (`hR`, `hB` positivity of conductances) are satisfiable by orthogonal tilings with nonempty facets.
- `ambient_clockedExcursion_ae_oscillation` (line 70), `ambient_clockedExcursion_ae_oscillation_of_positive` (line 93): conclusion `ClockedWalkExcursion.curve e ∈ curveOscillationLe (2r + 2·mesh)`. NOTE: `curveOscillationLe R = {c | ∀ t, dist (c t) (c 0) ≤ R}` (`BouRabeeGwynne/ExcursionOscillation.lean:18–19`) bounds the distance from the *start*, not `sup_{s,t} dist`. The constant is right for that meaning (start in `closedBall c r`, path in `closedBall c (r+2·mesh)` ⇒ radius `≤ 2r+2·mesh`). The pairwise notion is `unitCurveDiameterBound` (`UnitCurveOscillation.lean:66`); the two coexist, so the name "oscillation" can mislead. No statement is false.

## BouRabeeGwynne.SelectedExcursionOscillation
- `constant_mem_curveOscillationLe` (line 19), `clockedConstant_mem_curveOscillationLe` (line 24): correct.
- `trajectoryLaw_walkSkeleton_ae_oscillation` (line 34): a.e. all selected excursions are in `curveOscillationLe R` (start-radius meaning, see ClockedExcursionRange NOTE); correct.
- `trajectoryLaw_selectedBallSkeleton_ae_oscillation` (line 89): `2r + 2·mesh`; correct under `hBW`, `hmesh`, positivity hypotheses.
- `standardBrownianLaw_skeleton_ae_oscillation` (line 122): start `z ∈ ball(c_initial, r)`, exit keeps the path in `closedBall(c,r)` until exit, so start-radius `≤ 2r`; correct. Hypotheses (`hμ : IsStandardBrownianLaw μ`, `hd : 1 ≤ d`) are satisfiable (`isStandardBrownianLaw_euclideanWienerLaw`).

## BouRabeeGwynne.JointExcursionPasting
- `walkBrownianJointLaw_ae_pasted_dist_le` (line 23): on `goodExcursionPair` pieces, the pasted walk and Brownian curves are within `R + a + S` at all times. Checked: each piece is within `R` (walk) or `S` (Brownian) of its start; starts are within `a` (initial `hnear`, then the good-pair closeness at later knots). Statement is the intended one. Good pairs (`WalkBrownianGoodEvent.lean:20–26`): either both active in the same cell `E i` (closeness from `hdiam`) or both absorbed with endpoint distance `≤ a`; consistent with `activeEndpointCell`/`walkEndpointCell` (`WalkBrownianCoupling.lean:24–25, 51–53`). NOTE: same `curveOscillationLe` naming point.

## BouRabeeGwynne.ActualStoppedLawComparison
- `levyProkhorov_actual_stopped_laws_le` (line 22): `LP(walk stopped law, Brownian stopped law) ≤ rWalk + rMiddle + rBrownian`. Budgets `b+c ≤ rWalk`, `c ≤ rBrownian`, `b+c+o ≤ rMiddle`, `ε+η < rMiddle` are jointly satisfiable (`b=c=o=0`), and the bound is non-trivial (small `ε, η` give a small bound). Correct as an intermediate lemma; downstream `TilingStoppedLawComparison.lean:72–83` discharges `hsteps` via `trajectoryLaw_ae_step_dist_le_two_mesh` and passes `2·T.mesh`.
- NOTE (naming/junk): the parameter `mesh` in `hsteps` is a step bound, not the tile mesh: for `d = 1`, cells `[0,1]`, `[1,2]` with vertices `0.01`, `1.99` form an orthogonal tiling with `mesh = 1` and step `1.98`, so `step ≤ mesh` is false in general. Read `mesh` as the step bound.
- NOTE (junk for non-exiting paths): `continuousExitTime` is `⊤` when a path never leaves `U` (`StoppedCurveLaws.lean:67–80`); `stoppedBrownianRepresentative` then gives duration 0, and `stoppedPolygonalCurve` uses `untopD 0` (`StoppedCurveLaws.lean:60–63`). The lemma assumes only `IsOpen U`, not boundedness. The bound stays true as a statement about these objects, and it is only meaningful when exits are a.s. finite (downstream uses bounded `U`).
- NOTE: `innerDomain U ε = {x | ε < infDist x Uᶜ}` (`BrownianInnerExit.lean:15–16`) is `∅` for `U = univ` (`infDist` to `∅` is `0`), not `ℝ^d`. This only makes the `hosc` hypothesis stronger; harmless.

## BouRabeeGwynne.BrownianExitReference
- `brownianExitReferenceLaw` (line 20): pushforward of `(law of ω 1) × μ` through the stopped endpoint; probability by `brownianExitReferenceLaw_isProbability` (line 29). Matches the docstring (Gaussian-start reference).
- `standardBrownianLaw_restarted_exit_absolutelyContinuous` (line 56): restart at positive time `t` is dominated by the reference; correct.
- `standardBrownianLaw_early_exit_tendsto_zero` (line 72): `P(τ ≤ 1/(n+1)) → 0` for `z ∈ U`; correct.
- `standardBrownianLaw_exit_absolutelyContinuous_reference` (line 113): exit endpoint law from `z ∈ U` is `≪` the reference (bounded `U`). Non-vacuous (instantiated in the Nonvacuity section).

## BouRabeeGwynne.ContinuityCells
- `exists_finite_small_nullFrontier_cells` (line 48): finite disjoint bounded measurable cells covering compact `K`, `γ`-null frontiers, `dist < ε` inside a cell. Correct; `γ` is only assumed `SFinite`, and the conclusion is what the docstring says. No junk.

## BouRabeeGwynne.BrownianContinuityCells
- `exists_common_brownian_exit_continuity_cells` (line 18): one labelling works for all `z ∈ U j`, all `j`, since each exit law is `≪ brownianExitReferenceLaw (U j) μ ≤ Σ_j(...)`. Correct and not vacuous (`ι` finite, `U j` open bounded).

## BouRabeeGwynne.HarmonicCutoff
- `exists_contDiff_compactSupport_eq_near_compact` (line 18): `χ · h` with a `C²` cutoff; `EqOn g h V` on an open `V ⊇ K`, `V ⊆ W`; correct.
- `IsHarmonicOn.exists_compactSupport_eq_near_compact` (line 56): harmonicity on `V` by locality of `Δ`; correct.

## BouRabeeGwynne.HarmonicNearClosureBrownianExit
- `standardBrownianLaw_stopped_endPoint_ae_mem_frontier` (line 16): the endpoint law is carried by `frontier U`; correct.
- `standardBrownianLaw_integral_stopped_endPoint_harmonicNearClosure` (line 33): `∫ h d(endpoint law) = h z` for `h` harmonic near `closure U` (`HarmonicNearClosure`, `Harmonic.lean:28–29`); correct, and no junk.

## BouRabeeGwynne.Section4BrownianBallHarmonicMeasure
- `brownianSpatialHarmonicMeasure` (line 15): endpoint law as a `ProbabilityMeasure`; faithful. NOTE: total in `z`; for `z ∉ U` the stopped law is `δ_z` (exit at time 0). All lemmas take `hz : z ∈ U`, so harmless.
- `brownianSpatialHarmonicMeasure_ae_mem_frontier` (line 26): correct.
- `abs_integral_brownianSpatialHarmonicMeasure_sub_le` (line 36): `|∫f − h z| ≤ η` from `|f−h| ≤ η` on `frontier U`; uniform in `z ∈ U`. NOTE: `hcont` as above (harmless).

## BouRabeeGwynne.PolynomialLaplacian
- `polynomialLaplacian` (line 21): `∑ᵢ ∂ᵢ∂ᵢ p` on `MvPolynomial (Fin d) ℝ`; matches the Euclidean Laplacian of coordinate polynomials.
- `polynomialSquaredNorm` (line 24): `∑ Xᵢ²`, i.e. `|x|²`; correct.
- `pderiv_twice_polynomialSquaredNorm_mul` (line 45): `∂ᵢ²(S·p) = 2p + 4Xᵢ∂ᵢp + S∂ᵢ²p` (checked by hand); correct.
- `polynomialLaplacian_squaredNorm_mul` (line 60): `Δ(|x|²p) = 2d·p + 4 x·∇p + |x|²Δp`; standard; correct.

## BouRabeeGwynne.PolynomialAnalyticLaplacian
- `polynomialEval` (line 22): evaluation at coordinates `x ↦ eval (x i) p`; correct.
- `laplacian_polynomialEval` (line 97): `Δ (polynomialEval p) = polynomialEval (polynomialLaplacian p)` with Mathlib's `Δ` (`Harmonic.lean` opens `InnerProductSpace Laplacian`); correct.
- `isHarmonicOn_polynomialEval_of_laplacian_eq_zero` (line 110): correct; used by the Section4 ball examples.

## BouRabeeGwynne.PolynomialBoundaryApproximation
- `exists_polynomial_near_continuous_on_compact` (line 49): for compact `K` and continuous `f : K → ℝ`, `∃ p, ∀ x : K, |p(x) − f x| < ε`; correct (Stone–Weierstrass, coordinate polynomials separate points).

## BouRabeeGwynne.PolynomialDegree
- `totalDegree_pderiv_le` (line 19): `deg p ≤ m+1 ⇒ deg ∂ᵢp ≤ m`; correct.
- `totalDegree_pderiv_pderiv_mul_le` (line 38), `totalDegree_laplacian_mul_le` (line 45): `deg(Ap) ≤ deg(A)+deg p` lowers by two derivatives; correct.
- `quadraticLaplacianOnDegree` (line 54): linear self-map of `restrictTotalDegree σ ℝ m`; `A` of degree `≤ 2` is needed and present. Faithful to the docstring.

## BouRabeeGwynne.PolynomialBallIdentity
- `polynomial_eq_zero_of_eval_zero_on_ball` (line 26): `0 < r` is needed and present; the proof uses a box inside the ball; correct.

## BouRabeeGwynne.BrownianProjectiveLaw
- `brownianProjectiveLaw` (line 25): projective limit of `BrownianReal.projectiveFamily` (Mathlib, `GaussianProjectiveFamily.lean:81`: centred Gaussian, covariance `min(s,t)` on finite sets). Correct.
- `brownianProjectiveLaw_isProbabilityMeasure` (line 29): probability; correct.
- `isPreBrownianReal_brownianProjectiveLaw` (line 40): the coordinate process has the Brownian finite-dimensional laws (Mathlib's `IsPreBrownianReal`). Correct; continuity is not claimed (as documented). `IsStandardBrownianLaw` in `StoppedCurveLaws.lean:38–41` = probability + `IsBrownianReal` coordinates + `iIndepFun`, the standard `d`-dimensional Brownian motion.

## BouRabeeGwynne.Upstream.KolmogorovExtension
- `projectiveLimit` (line 138), `isProjectiveLimit_projectiveLimit` (line 149), `isFiniteMeasure_projectiveLimit` (line 161), `isProbabilityMeasure_projectiveLimit` (line 165): standard Kolmogorov extension via `projectiveFamilyContent` and inner-regular compact closures; vendored from Degenne–Pfaffelhuber, adaptation is import paths only (per the header). Matches standard math.

## BouRabeeGwynne.Upstream.BrownianMotion.Continuity.KolmogorovChentsov
- Read: statement lines and `holderSet` (line 311), `holderModification` (line 443), `exists_modification_holder` (line 885), `exists_modification_holder_iSup` (line 1093). Proof bodies not read (outside the review scope).
- `holderSet` (line 311): `(⨆ s t, edist(X s,X t)^p / edist(s,t)^{βp}) < ∞ ∧ (edist s t = 0 ⇒ edist(X s,X t) = 0)`, over `s, t ∈ T' ∩ U`; the `⨆` body stops before `<` (Mathlib notation precedence 60), so the parse is as intended. Standard Hölder-type set; the `0/0 = 0` cases in `ℝ≥0∞` are harmless.
- `holderModification` (line 443): limit along a dense countable set on `U`; off `U` it takes the junk value `hE.some`. NOTE: harmless, since `exists_modification_holder` asserts `Y t =ᵐ X t` and Hölder continuity only for `t ∈ U`.
- `exists_modification_holder` (line 885), `exists_modification_holder_iSup` (line 1093): Hölder modification with exponent `β < (q−d)/p` on open `U`, for every `ω`, with `ω`-dependent constant; matches standard Kolmogorov–Chentsov.

## Nonvacuity examples
Scratch file: `Nonvacuity.lean`. Compiled from the repository root with `lake env lean`; exit status 0, and the output log (`nonvacuity.out`) is empty: no errors, no warnings, no `sorry`.

```lean
import BouRabeeGwynne.TheoremBStatement
import BouRabeeGwynne.EuclideanWienerLaw
import BouRabeeGwynne.BrownianExitReference
import SpherePackings.Support.Guards.LatticeTilings
import SpherePackings.Support.Guards.LipschitzBall

open BouRabeeGwynne MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

/-- Hypothesis bundle of `TheoremBPartAStatement` (minus the universally quantified
`hC` and `U` that are instantiated here): the lattice tiling sequence, the ball
`U = B(0,1)`, and the zero function, which is harmonic on `ℝ^d`. -/
example {d : ℕ} (hd : 1 ≤ d) :
    ∃ (G : TilingSequence d) (N : NearestVertexData G) (U : Set (Euc d)) (hC : Euc d → ℝ),
      1 ≤ d ∧ IsDomain U ∧ Bornology.IsBounded U ∧ HasAmbientCollar U G.domain ∧
      N.ApproximationCondition ∧ PaperRegularity G ∧ HarmonicNearClosure hC U := by
  obtain ⟨G, hcol, ⟨N⟩, happ, hreg⟩ := SpherePackings.exists_lattice_tilingSequence hd
  refine ⟨G, N, ball (0 : Euc d) 1, fun _ => 0, hd,
    ⟨isOpen_ball, ⟨0, mem_ball_self one_pos⟩, (convex_ball 0 1).isPreconnected⟩,
    isBounded_ball, hcol, happ N, Or.inr (Or.inl hreg), Set.univ, isOpen_univ,
    subset_univ _, ?_⟩
  exact ⟨contDiff_const.contDiffOn, fun x _ => by simp⟩

/-- Hypothesis bundle of `TheoremBPartBStatement` (same instance, with a Lipschitz
domain and `IsHarmonicOn`/`ContinuousOnClosure` in place of `HarmonicNearClosure`). -/
example {d : ℕ} (hd : 1 ≤ d) :
    ∃ (G : TilingSequence d) (N : NearestVertexData G) (U : Set (Euc d)) (hC : Euc d → ℝ),
      1 ≤ d ∧ IsLipschitzDomain U ∧ Bornology.IsBounded U ∧ HasAmbientCollar U G.domain ∧
      N.ApproximationCondition ∧ PaperRegularity G ∧ IsHarmonicOn hC U ∧
      ContinuousOnClosure hC U := by
  obtain ⟨G, hcol, ⟨N⟩, happ, hreg⟩ := SpherePackings.exists_lattice_tilingSequence hd
  refine ⟨G, N, ball (0 : Euc d) 1, fun _ => 0, hd, SpherePackings.isLipschitzDomain_ball hd,
    isBounded_ball, hcol, happ N, Or.inr (Or.inl hreg), ?_, ?_⟩
  · exact ⟨contDiff_const.contDiffOn, fun x _ => by simp⟩
  · exact continuousOn_const

/-- The branch-(b) sampling class is nonempty for any nonempty `U`. -/
example {d : ℕ} (G : TilingSequence d) (U : Set (Euc d)) (hU : U.Nonempty) :
    Nonempty (NearestClosureBoundaryChoices G U) :=
  ⟨NearestClosureBoundaryChoices.ofNonempty G U hU⟩

/-- The actual Gaussian-start-free standard Brownian law on `ℝ²` (`euclideanWienerLaw 2`)
satisfies the hypotheses of the exit-reference lemma for `B(0,1)` and start `0`; the
conclusion is then an instance of the absolute continuity used in the Brownian comparison. -/
example :
    (stoppedBrownianLaw (ball (0 : Euc 2) 1) 0 (euclideanWienerLaw 2)).map CurveSpace.endPoint ≪
      brownianExitReferenceLaw (ball (0 : Euc 2) 1) (euclideanWienerLaw 2) :=
  standardBrownianLaw_exit_absolutelyContinuous_reference (by norm_num)
    (isStandardBrownianLaw_euclideanWienerLaw 2) isOpen_ball isBounded_ball
    (mem_ball_self one_pos)
```

What they show:
1. The `TheoremBPartAStatement` hypothesis bundle is jointly satisfiable: `SpherePackings.exists_lattice_tilingSequence` supplies `G` with `HasAmbientCollar`, a `NearestVertexData`, `ApproximationCondition` (for every `N`), and `RegularityII`. With `U = B(0,1)`, `IsDomain`/boundedness hold, and `hC = 0` is harmonic on `univ`, so `HarmonicNearClosure` holds. `PaperRegularity` is satisfied through `RegularityII`.
2. The same holds for the `TheoremBPartBStatement` bundle with `IsLipschitzDomain (B(0,1))` (from `SpherePackings.isLipschitzDomain_ball`), `IsHarmonicOn` and `ContinuousOnClosure`.
3. The branch-(b) sampling class `NearestClosureBoundaryChoices` is inhabited for every nonempty `U` (`ofNonempty`), so the `Nonempty` clause of `TheoremBPartBStatement` is not vacuous.
4. The Brownian exit lemma is instantiable: `euclideanWienerLaw 2` is a standard Brownian law and `B(0,1)` with start `0` meets its hypotheses, so the absolute-continuity conclusion is a real statement.

Not compiled (time budget): an explicit `TilingData`/`OrthogonalTiling` counterexample for the `step ≤ mesh` remark (given on paper above, `d = 1`), and a concrete `NearestVertexData` verification beyond what `exists_lattice_tilingSequence` provides.
