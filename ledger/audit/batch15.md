# Audit batch 15
| Module | Verdict | Summary |
|---|---|---|
| SpherePackings.General.MarkovChain.Basic | OK | Chain law, Markov property and first-step decomposition mean what they say; no junk values. |
| SpherePackings.General.MarkovChain.Absorbed | NOTE | `absorbedKernel` and the strong Markov property are as intended; `observedHistory`/`futureAt` junk values sit only on `{τ = ⊤}`, excluded by `hfin`. |
| SpherePackings.General.MarkovChain.Dirichlet | NOTE | `exitValue`, `survival`, `SolvesDirichlet` mean what they say; uniqueness hypotheses quantify over all of `V`, so they are stronger than they look; `exitVertex` junk is guarded. |
| SpherePackings.General.NearestNeighbourWalk | NOTE | `inner`/`boundary` match `V_n[S]`/`∂V_n[S]`; the kernel is arbitrary (paper's walk is the conductance walk); `harmonicMeasure` is a sub-probability measure and is `δ_a` for `a ∉ inner S`. |
| SpherePackings.General.NearestNeighbourWalkHarmonic | NOTE | Identity with the absorbed-chain harmonic measure is correct under the a.s.-exit hypothesis; the outside-batch `MarkovChain.discreteHarmonicMeasure` puts non-exit mass on the start vertex, which `hexit` excludes. |
| SpherePackings.General.LevyProkhorovTest | NOTE | Test-family statement matches its docstring and is satisfiable; `tent`/`farCutoff` have `x/0 = 0` junk for `ρ ≤ 0` and `farCutoff ≡ 0` on `∅`, all excluded by hypotheses. |
| SpherePackings.Support.LevyProkhorovIntegral | OK | Oscillation bound `δ + 2ε‖f‖` under `levyProkhorovEDist < ε` for bounded continuous `f`; constants and strictness correct. |
| SpherePackings.Support.MeasureOverlap | OK | Bounded-overlap union bound; the `ncard` set is a subset of a `Finset`, so there is no infinite-set `ncard = 0` junk. |

Verdict counts: OK 3, NOTE 5, ISSUE 0.

## SpherePackings.General.MarkovChain.Basic
- `historyKernel` (line 25): next state depends only on the last state of the history. Matches the time-homogeneous Markov chain.
- `law` (line 33): `Kernel.trajMeasure` from `dirac a` with `historyKernel`; probability measure (instance line 36). Matches the chain started at `a`.
- `pathKernel` (line 41), `pathKernel_apply` (line 46): `pathKernel κ a = law κ a`. Matches.
- `law_initialHistory` (line 54), `law_map_eval_one` (line 131): `ω 0 ~ dirac a`, `ω 1 ~ κ a`. Matches.
- `continuation_walkShift_law` (line 92), `law_prefix_future` (line 120): Markov property at a deterministic time. Matches.
- `law_map_walkShift_one` (line 153), `lintegral_walkShift_one` (line 165), `integral_walkShift_one` (line 171): first-step decomposition. Matches; the integral version carries an explicit bound `C`.

## SpherePackings.General.MarkovChain.Absorbed
- `absorbedKernel` (line 34): `Kernel.piecewise hA κ (deterministic id)`, that is `κ` on `A` and stay put off `A`. Matches the docstring ("moves like `κ` in `A` and stays put outside `A`").
- `absorbedKernel_of_mem` (line 43), `absorbedKernel_of_not_mem` (line 49): pointwise values. Match.
- `observedRestartKernel` (line 57): `pathKernel` at the state `h.2 h.1`, the state at the observed stopping time. Matches.
- `law_observed_future` (line 117): strong Markov property at an a.s. finite stopping time (`hfin`, line 119). Meaningful; the hypothesis is the natural one for `exitTime`.
- `law_absorbed_ae_absorbed` (line 191): `IsAbsorbedPath A ω` (`∀ n, ω n ∉ A → ω (n+1) = ω n`, `BouRabeeGwynne/StoppedWalk.lean:103`) holds a.s. Matches.
- NOTE: `observedHistory` and `futureAt` (`BouRabeeGwynne/WalkStoppedHistory.lean:51,54`) use `untopD 0` on `{τ = ⊤}`. Excluded by `hfin` (line 119), so harmless.

## SpherePackings.General.MarkovChain.Dirichlet
- `exitPayoff` (line 63): `0` on `{exitTime = ⊤}`, `g (exitVertex A ω)` otherwise. Matches `E[g(X_τ); τ < ∞]`. The junk `exitVertex` value (`ω 0`) on `⊤` never reaches the integral.
- `exitValue` (line 139): `∫ exitPayoff ∂law κ a`. Matches "expectation of `g` at the exit state on the event of exit". NOTE: for non-integrable `g` the Bochner convention makes it `0`; every lemma assumes `|g| ≤ C` (lines 149, 171, 197), so this cannot matter.
- `IsHarmonicAt` (line 184): integrability plus mean value. Integrability is required, so the Bochner `0` convention cannot make a non-integrable `f` harmonic. Matches.
- `SolvesDirichlet` (line 188): harmonic on `A`, equal to `g` on `B`. Matches. Values of `f` outside `A ∪ B` are free, and harmonicity at `a ∈ A` involves them if `κ a` charges the outside.
- `HasUniqueDirichletSolution` (line 192): `∃ f` solving, and every solution `f'` agrees with `f` on `A ∪ B`. NOTE: `f'` ranges over all `V → ℝ`. Example: `V = {a,b,c}`, `κ a = ½δ_b + ½δ_c`, `κ b = δ_b`, `κ c = δ_c`, `A = {a}`, `B = {b}`. Then `f(c)` is free and `f(a) = (f(b)+f(c))/2`, so uniqueness fails for every `g` and the hypothesis of `survival_eq_zero_of_unique` is false. The lemma is still correct; it applies only when `B` contains the one-step outer boundary of `A`, which nearest-neighbour walks guarantee (`ae_adj`, `boundary`).
- `survival` (line 218): `(law κ a).real {exitTime = ⊤}`; finite, no `toReal ⊤` issue. Matches.
- `exitValue_solvesDirichlet` (line 197), `eqOn_exitValue_of_unique` (line 206): match their docstrings.
- `survival_eq_zero_of_unique` (line 265): matches docstring; hypothesis bundle satisfiable (see Nonvacuity, `Audit15.survival_true`).
- `survival_eq_zero_of_forall_solution_bounded` (line 289): matches docstring; same caveat as `HasUniqueDirichletSolution` (solutions range over all `V → ℝ`).
- Junk note: `exitVertex` (`BouRabeeGwynne/DiscreteHarmonicMeasure.lean:25`) is `ω ((exitTime A ω).untopD 0)`; on non-exit it is `ω 0`. Only consumed under `exitTime ≠ ⊤` guards.

## SpherePackings.General.NearestNeighbourWalk
- `NearestNeighbourWalk` (line 19): kernel is an arbitrary Markov kernel on `V` with steps along an arbitrary symmetric adjacency (`ae_adj`, line 29). NOTE: the paper's walk is the conductance walk `p(v,w) = cond(v,w)/cond(v)` (`paper/rw-spheres.tex:234`). The Lean generalization is harmless: for the paper's walk, `Σ_w p(v,w)(h(w)−h(v)) = Δh(v)/cond(v)` with `Δh` as at paper line 290, so kernel-harmonic is `Δ`-harmonic. The Lean Assumption D (4.2) is therefore the paper's assumption for conductance walks.
- `inner` (line 38): `{v | ↑v ∈ interior S}`. Matches `V_n[S]` (paper line 296).
- `boundary` (line 41): vertices outside `inner S` adjacent to `inner S`. Matches `∂V_n[S]` (paper line 296, and `∂A` at line 563).
- `harmonicMeasure` (line 54): `(law a).restrict {exitTime ≠ ⊤}` mapped to the exit position. NOTE: this is a sub-probability measure of mass `P(exit) ≤ 1` (`harmonicMeasure_univ_le_one`, line 66). The paper's `hm_n` is a probability measure on `∂V_n[B]` (paper lines 1507–1508). They agree under a.s. exit (see `NearestNeighbourWalkHarmonic`). NOTE: with `inner S` empty or `a ∉ inner S`, exit happens at time `0`, so `harmonicMeasure S a = dirac a`. This is the first-exit convention. Prop 4.2 is proved with this convention, so it does not make the statement false, but it is worth knowing.
- `integral_harmonicMeasure` (line 85): `∫ f dH = exitValue … f` for every measurable `f`, with no integrability hypothesis. Both sides follow the Bochner `0` convention, so the identity is correct as stated.
- `IsNearestVertex` (line 98): `near z` minimizes distance over `V`. Matches "`z^n` is a nearest vertex" (paper line 260).
- `isClosed_of_isNearestVertex` (line 103): correct; the nearest-vertex property implies `V` is closed.

## SpherePackings.General.NearestNeighbourWalkHarmonic
- `discreteHarmonicMeasure_map_val` (line 23): `discreteHarmonicMeasure … .map Subtype.val = harmonicMeasure S a` under `hexit` (line 24, a.s. exit from `inner S`). Correct: under the exit hypothesis both sides are the exit law of the chain. Matches.
- `discreteHarmonicMeasure_map_val_of_eq` (line 33): same, for `B = inner S`. Matches.
- NOTE (outside batch, `SpherePackings/General/Walk/DiscreteHarmonicMeasure.lean:67`): `MarkovChain.discreteHarmonicMeasure` is `(law (absorbedKernel κ hpos) v).map (exitVertex A)`. It is always a probability measure, and on non-exit it puts mass `P(no exit)` on the start vertex `v` (since `exitVertex = ω 0`). `hexit` excludes this in both lemmas here.

## SpherePackings.General.LevyProkhorovTest
- `tent` (line 25): `max 0 (1 − dist x y / ρ)`. NOTE: junk at `ρ = 0` (`x/0 = 0`). Harmless: every lemma uses `0 < ρ`.
- `tentSum` (line 48): `min 1 (4 * Σ tent)`. Matches "truncated sum of four times the tents".
- `farCutoff` (line 80): `min 1 (infDist x S / (ρ/2))`. NOTE: for `S = ∅`, `infDist = 0` so it is identically `0`. Excluded by `hSne` (line 136).
- `exists_test_family_levyProkhorov` (lines 135–141): finitely many continuous `[0,1]`-valued test functions such that, for finite `μ`, `ν` with `μ Sᶜ = 0` (line 139; only `μ` is concentrated), and `|∫g_i dν − ∫g_i dμ| ≤ θ` for all `i`, `levyProkhorovEDist μ ν ≤ ofReal(2ρ + 2θ)`. Matches the module docstring. Satisfiable for any compact nonempty `S` and `ρ > 0`; the conclusion is non-trivial, since `ν`'s mass off the thickening is controlled by `g_none`.

## SpherePackings.Support.LevyProkhorovIntegral
- `integral_le_integral_add_of_nonneg` (private, line 36): `∫g dμ ≤ ∫g dν + δ + ε‖g‖` for nonnegative bounded continuous `g` with oscillation `≤ δ` on `ε`-pairs. Matches; the layer-cake argument is correct.
- `abs_integral_sub_integral_le_of_levyProkhorovEDist_lt` (line 79): `|∫f dμ − ∫f dν| ≤ δ + 2 ε ‖f‖` when `levyProkhorovEDist μ ν < ε` and `f` oscillates by at most `δ` at scale `ε`. The shift `g = f + ‖f‖` gives `‖g‖ ≤ 2‖f‖`, so the constants are right. Strict `<` (line 82) is the correct hypothesis. No junk values.

## SpherePackings.Support.MeasureOverlap
- `sum_measure_le_of_ncard_le` (line 39): `Σ μ(B i) ≤ M · μ(⋃ B i)` when each point lies in at most `M` of the `B i`, `i ∈ F`. Matches the docstring. The `ncard` set `{i | i ∈ F ∧ y ∈ B i}` is a subset of the finset `F`, so `ncard` is the true cardinality, not the infinite-set `0`. Holds in `ℝ≥0∞` with no finiteness assumption on `μ`.
- Citation: `rw-spheres.tex:1717–1755` lies in the proof of `prop:min-max-edge-length` (paper line 371), the paper's first proposition, which the docstring calls Proposition 1.1.

## Nonvacuity examples
Compiled from the repository root with `lake env lean Nonvacuity.lean`: exit 0, no warnings, no errors. `#print axioms` for both named results gives `[propext, Classical.choice, Quot.sound]`.

```lean
import SpherePackings.General.MarkovChain.Dirichlet
import SpherePackings.General.NearestNeighbourWalk

/-! Nonvacuity witnesses for batch 15 (audit nonvacuity examples).

* `toggleKernel`: the two-state chain on `Bool` that flips its state at every step.
  With `A = {true}`, `B = {false}` and data `0`, the Dirichlet problem has a unique solution
  (`hasUnique`), so the hypothesis of `survival_eq_zero_of_unique` holds, and its conclusion
  `survival toggleKernel {true} true = 0` is then a genuine consequence (`survival_true`).
* `trivialWalk`: a `NearestNeighbourWalk 1` with vertex set `ℝ` (all of it), every pair adjacent,
  and the walk that stays put; `IsNearestVertex` holds for the identity selection. -/

open MeasureTheory ProbabilityTheory SpherePackings.MarkovChain

namespace SpherePackings.Audit15

/-- The chain on `Bool` that flips its state at every step. -/
noncomputable def toggleKernel : Kernel Bool Bool :=
  Kernel.deterministic (fun b : Bool => !b) (measurable_of_countable _)

instance : IsMarkovKernel toggleKernel := by
  unfold toggleKernel
  infer_instance

lemma toggleKernel_true : toggleKernel true = Measure.dirac false := by
  simp [toggleKernel, Kernel.deterministic_apply]

/-- With `A = {true}`, `B = {false}` and data `0`, the Dirichlet problem has a unique solution. -/
lemma hasUnique : HasUniqueDirichletSolution toggleKernel {true} {false} (fun _ => (0 : ℝ)) := by
  refine ⟨fun _ => 0, ⟨fun a ha => ?_, fun b hb => rfl⟩, ?_⟩
  · rw [Set.mem_singleton_iff] at ha
    subst ha
    refine ⟨integrable_const _, ?_⟩
    simp
  · rintro f' ⟨hA, hB⟩ x hx
    have hfalse : f' false = 0 := hB false (Set.mem_singleton _)
    have htrue : f' true = f' false := by
      have h := (hA true (Set.mem_singleton _)).2
      rw [toggleKernel_true, integral_dirac] at h
      exact h.symm
    simp only [Set.mem_union, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · simp [htrue, hfalse]
    · simp [hfalse]

/-- The conclusion of `survival_eq_zero_of_unique` is attained (not vacuous) for this chain. -/
theorem survival_true : survival toggleKernel {true} true = 0 :=
  survival_eq_zero_of_unique toggleKernel (measurableSet_singleton true)
    (Set.disjoint_singleton.mpr (by decide)) hasUnique (by simp)

/-- A nearest-neighbour walk on the whole line: all of `ℝ` is the vertex set, every pair of
vertices is adjacent, and the walk stays put. -/
noncomputable def trivialWalk : SpherePackings.NearestNeighbourWalk 1 where
  V := Set.univ
  adj _ _ := True
  adj_symm _ _ _ := trivial
  kernel := Kernel.deterministic id measurable_id
  isMarkovKernel := inferInstance
  ae_adj _ := ae_of_all _ fun _ => trivial

example : trivialWalk.IsNearestVertex (fun z => ⟨z, Set.mem_univ z⟩) := by
  intro z v
  simp

end SpherePackings.Audit15

#print axioms SpherePackings.Audit15.survival_true
#print axioms SpherePackings.Audit15.trivialWalk
```

What the examples show:
- `survival_true` (compiled): the hypothesis bundle of `survival_eq_zero_of_unique` (`HasUniqueDirichletSolution`, here `hasUnique`) is satisfiable for a concrete Markov kernel with `A`, `B` disjoint and `A ∪ B = Bool`. The conclusion `survival = 0` is then a genuine consequence, not a vacuous one.
- `trivialWalk` (compiled): the `NearestNeighbourWalk` structure is inhabited (vertices `ℝ`, a deterministic kernel, `ae_adj` trivially), and the identity selection is a nearest-vertex selection (`IsNearestVertex`). This is a weak instance; it shows the fields are constructible, not that the paper's setting is covered.
- Not compiled here, but cited and confirmed to exist by name: `SpherePackings.exists_lattice_tilingSequence` (`SpherePackings/Support/Guards/LatticeTilings.lean:202`); `SpherePackings.exists_walks_assumptionD` (`SpherePackings/Support/Guards/AssumptionDLattice.lean:49`); `SpherePackings.theorem41_hypotheses_satisfiable` (`SpherePackings/Support/Guards/AssumptionDLattice.lean:130`), which covers the Theorem 4.1 / Prop 4.2 hypothesis bundle (Assumption D, Lipschitz domain, Brownian law); `isLipschitzDomain_ball` (`SpherePackings/Support/Guards/LipschitzBall.lean:112`); `isStandardBrownianLaw_euclideanWienerLaw` (`BouRabeeGwynne/EuclideanWienerLaw.lean:83`).
- Not checked: nonvacuity of `law_observed_future`'s `hfin` and of the test-family hypotheses in `LevyProkhorovTest`. Both are standard (any chain that exits a.s., and any compact nonempty `S`), and no example was written for them.
