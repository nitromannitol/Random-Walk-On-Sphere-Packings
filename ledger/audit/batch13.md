# Audit batch 13
| Module | Verdict | Summary |
|---|---|---|
| BouRabeeGwynne.Upstream.BrownianMotion.Continuity.KolmogorovChentsovInequality | NOTE | `constL` junk values (`ofReal` truncation, `c.toReal` at `c = ⊤`/`c = 0`, ENNReal `∑'`) all harmless; statements match the Kolmogorov–Chentsov bound; depends on `HasBoundedCoveringNumber` whose `ε = 0` clause is harmless only for `0 < d` (all batch statements assume it). |
| BouRabeeGwynne.Upstream.BrownianMotion.Continuity.LimitModification | OK | `indicatorProcess` and `IsLimitOfIndicator` mean what their docstrings say; all `limUnder` uses sit under existence hypotheses or are measurability-only; nonvacuity compiled. Header copyright year (2026) differs from the other files (2023/2025); cannot be checked offline. |
| BouRabeeGwynne.Upstream.BrownianMotion.Gaussian.StochasticProcesses | OK | Four standard modification/indistinguishability lemmas with the right hypotheses (separability, continuity a.s., open `U`); no junk values. |
| BouRabeeGwynne.Upstream.KolmogorovExtension.CompactSystem | OK | `IsCompactSystem` (Mathlib `dissipate` form), `allProj`, `indexProj`, `projCylinder`, `piCylinderSet` match their docstrings; `isCompactSystem_closedCompactCylinders` is the stated theorem; `Classical.choose` only picks representations that are used consistently. |
| BouRabeeGwynne.Upstream.KolmogorovExtension.RegularContent | OK | Standard regular-content lemmas (decreasing sets with empty intersection tend to 0; σ-additivity under finiteness and inner regularity); no finiteness needed for the first; hypotheses satisfiable on paper, not instantiated in Lean. |

**Repository-level note (not a math verdict).** The headers of all five modules (and of other `Upstream/` files) say "see `Upstream/BrownianMotion/PROVENANCE.md`" or "see LICENSE and PROVENANCE.md in this directory". No `PROVENANCE.md` exists anywhere in the repository, and no `LICENSE` exists under `Upstream/`. The root `LICENSE` exists. `BouRabeeGwynne/BrownianProjectiveLaw.lean:16` also points to a missing `Upstream/KolmogorovExtension/PROVENANCE.md`. Either add those files or drop the pointers.  *(Action, after the audit: `LICENSE` and `PROVENANCE.md` were added in `Upstream/BrownianMotion/` and `Upstream/KolmogorovExtension/`, so the pointers now resolve.)*

**Scope.** None of the five modules defines a paper object. They are the library behind `BouRabeeGwynne.isStandardBrownianLaw_euclideanWienerLaw`: `BrownianContinuousLaw` imports `KolmogorovChentsov`, which imports the first three modules; `BrownianProjectiveLaw` imports `KolmogorovExtension`. So they matter for the existence of the Wiener law, not for the paper statements directly. Mathematical content was checked against Mathlib's `IsKolmogorovProcess`, `IsAEKolmogorovProcess`, `IsCompactSystem`, `closedCompactCylinders`, `IsSetRing` and `Dense.extend`.

## BouRabeeGwynne.Upstream.BrownianMotion.Continuity.KolmogorovChentsovInequality
- `Asymptotics.IsEquivalent.rpow_of_nonneg` (line 32): matches the standard fact that `t ~ u` with `u ≥ 0` gives `t^r ~ u^r`. The real `rpow` of a negative base is junk, but `t ~ u` forces `t > 0` eventually, so the conclusion is about the filter only.
- `Set.FiniteExhaustion.subset` (line 46): matches (`K n ⊆ s`).
- `measure_add_ge_le_add_measure_ge` (line 51): matches the Chebyshev-type split. ENNReal subtraction `x - u` is correct because of `hu : u ≤ x`.
- `measure_add_ge_le_add_measure_ge_half` (line 67): matches, including the `x = ⊤` case (`⊤ / 2 = ⊤`).
- `lintegral_div_edist_le_sum_integral_edist_le` (line 90): dyadic-scale bound. ENNReal `/` has no bad junk here: `x / 0 = ⊤` for `x ≠ 0`, and the diagonal terms `0 / 0 = 0` are the intended value (`edist (X s) (X s) = 0`).
- `constL` (line 151): the Kolmogorov–Chentsov constant. Junk-value check, all harmless:
  - `ENNReal.ofReal (Real.logb 2 c.toReal + (k+2)*d)` clips negative arguments to `0`. This only enlarges the constant, which is the direction needed for an upper bound, and it is documented in the comment at line 150.
  - `c = ⊤`: `c.toReal = 0` and `logb 2 0 = 0` are junk, but the factor `c = ⊤` makes `constL = ⊤` anyway, because `(ediam U+1)^(q-d) ≥ 1` and the `k = 0` term is at least `Cp > 0`. So the bound is trivially true there.
  - `∑'` is in `ℝ≥0∞`, so a divergent series (`β p ≥ q - d`) gives `⊤`, not `0` as a real `tsum` would. The bound is then trivial, never false.
  - `c = 0`: `constL = 0`. Then `HasBoundedCoveringNumber` forces `U = ∅` (any cover of a nonempty set has at least one centre, so `coveringNumber ε U ≥ 1` but the bound is `0`), and the left-hand side is `0`.
- `constL_lt_top` (line 156): finiteness under `c ≠ ⊤`, `0 < d < q`, `β < (q-d)/p`. Matches the expected geometric-series condition.
- `finite_kolmogorov_chentsov` (line 240): matches the finite Kolmogorov–Chentsov chaining bound. Here `hX` is the a.e. version (`IsAEKolmogorovProcess`, which is the right hypothesis because it is a modification of a Kolmogorov process). The `Finite T'` and `T' ⊆ U` hypotheses are as intended.
- `countable_kolmogorov_chentsov` (line 363): matches. The supremum over an empty `T'` is `0`, consistent with the bound.
- `IsKolmogorovProcess.ae_iSup_rpow_edist_div_lt_top` (line 385): a.s. finiteness of the Hölder quotient on a countable `T' ⊆ U`. Hypotheses `c ≠ ⊤`, `0 < d < q`, `0 < β < (q-d)/p`, `T'.Countable`, `T' ⊆ U` are all needed. The quotient at `s ≠ t` with `edist s t = 0` has a.s. zero numerator (Kolmogorov condition with `0^q = 0`), so the diagonal convention does not matter. Nonvacuity: example `nv_kc_hypotheses_hold` below compiles.
- Dependency, not in this batch: `HasBoundedCoveringNumber` (`Upstream/BrownianMotion/Continuity/HasBoundedInternalCoveringNumber.lean:34`). The docstring says `ε ∈ (0, diam A]`, but the code says `ε : ℝ≥0` with `ε ≤ ediam A`, which includes `ε = 0`. At `ε = 0` the clause is `coveringNumber 0 A ≤ c * ⊤^d`. For `c ≠ 0` and `d > 0` the right side is `⊤`, so the clause is trivially true. For `d < 0` the right side is `0`, which is impossible for nonempty `A`, so the hypothesis then holds only for `A = ∅`. Every batch statement assumes `0 < d`, so nothing here is affected. Recorded by reading, not compiled.

## BouRabeeGwynne.Upstream.BrownianMotion.Continuity.LimitModification
- `measurable_limUnder_of_exists_tendsto` (line 33): matches. Measurability of a pointwise limit on the set where the limit exists, with `limUnder` as the (irrelevant) default elsewhere.
- `measurable_limUnder` (line 44): matches, via `MeasurableEmbedding.measurable_extend` on the convergence set. The junk value of `limUnder` outside that set is harmless for a measurability statement.
- `limUnder_prod` (line 61): matches, under the existence hypotheses and `T2Space`.
- `Measurable.of_edist_eq_zero` (line 72): matches. A pointwise `edist = 0` makes `Y` measurable if `X` is, because `Inseparable` gives equal neighbourhood filters.
- `edist_limUnder_const` (line 87): matches (`NeBot` filter, constant tends to `c`).
- `edist_limUnder_prod_eq_zero` (line 95): matches under the two existence hypotheses.
- `indicatorProcess` (line 130): matches the docstring. It equals `X t ω` on `A` and the default constant `hE.some` off `A`. The default is an arbitrary point of `E`, and every use treats it as such.
- `indicatorProcess_apply` (line 135), `measurable_pair_indicatorProcess` (line 145), `measurable_edist_indicatorProcess` (line 170): match.
- `IsLimitOfIndicator` (line 189): the intended class. `Y` is, on `U`, the continuous extension of the indicator-restricted process from a countable dense set, and `Y` is pointwise constant (`hE.some`) off `U`. The first two clauses give `A` measurable of full measure; the third gives existence of the dense limit of `X` on `A` for `t ∈ U`. Off-`U` values are not constrained beyond being the default, which is what the docstring's "built from another, used to ensure measurability" needs. Nonvacuity: `nv_limit_of_indicator` below compiles.
- `IsLimitOfIndicator.measurable` (line 198), `measurable_pair_limUnder_comap` (line 215), `measurable_pair_limUnder_indicatorProcess` (line 248), `IsLimitOfIndicator.measurable_pair` (line 278), `IsLimitOfIndicator.measurable_edist` (line 354): all measurability statements with the hypotheses they need (`SecondCountableTopology`, `Measurable (X t)`, pair measurability). No junk values feed into the conclusions.
- `IsLimitOfIndicator.indicatorProcess` (line 368): matches (the indicator of a full-measure measurable set preserves the class).

## BouRabeeGwynne.Upstream.BrownianMotion.Gaussian.StochasticProcesses
- `modification_of_indistinguishable` (line 21): matches (a.s. equality for all `t` gives modification).
- `indistinguishable_of_modification` (line 27): matches the standard theorem. Two modifications with a.s. continuous paths on a separable `T` (with `T2Space E`) are indistinguishable. `P` need not be a probability measure.
- `subset_closure_dense_inter` (line 40): matches (`Dense T'`, `IsOpen U` gives `U ⊆ closure (T' ∩ U)`).
- `indistinguishable_of_modification_on` (line 49): matches. Continuity a.s. on an open `U`, plus modifications on `U`, give indistinguishability on `U`. Openness is needed for the closure argument, and it is present.

## BouRabeeGwynne.Upstream.KolmogorovExtension.CompactSystem
- `IsCompactSystem.support` (line 32): a `Classical.choose`-type choice of an `n` with `⋂ i ≤ n, C i = ∅`. It is proof-only (`noncomputable`), and its only consumer, `iInter_eq_empty` (line 35), states the property of the chosen `n`, so the default is never observed. Matches Mathlib's `dissipate`-form `IsCompactSystem`.
- `allProj` (line 55): the union of the chosen finsets of the cylinders. Matches the docstring.
- `indexProj` (line 68): `Nat.find` gives the least `n` with `i ∈ Js (hs n)`. Matches the docstring.
- `projCylinder` (line 94): cylinder over the countably many relevant coordinates. Matches.
- `piCylinderSet` (line 142): matches the docstring. A point is in the set iff each coordinate `i` lies in the projection of `As (hs (indexProj i))` onto `i`.
- Note: the representation of a cylinder (`closedCompactCylinders.finset` / `.set`, lines 53–60 of Mathlib) is chosen, so `allProj` and `projCylinder` depend on that choice. Every property used (`preimage_projCylinder`, closedness, compactness) is derived from the same `choose_spec`, so this is consistent and harmless.
- `exists_finset_iInter_projCylinder_eq_empty` (line 261): the finite-intersection property for a countable family with empty intersection, under `∀ i, Nonempty (α i)`. Matches.
- `isCompactSystem_closedCompactCylinders` (line 275): the stated theorem (closed compact cylinders form a compact system), with no separation hypothesis, which is correct (Tychonoff). Matches the docstring.

## BouRabeeGwynne.Upstream.KolmogorovExtension.RegularContent
- `tendsto_zero_of_regular_addContent` (line 30): matches the standard result. For a set ring `R`, a content `m`, a compact system `C ⊆ R` and inner regularity (`∀ A ∈ R, ∀ ε > 0, ∃ K ∈ C, K ⊆ A ∧ m (A \ K) ≤ ε`), a decreasing sequence in `R` with empty intersection has `m (s n) → 0`. The proof does not use finiteness of `m`, and the conclusion is correctly stated in `ℝ≥0∞`. Not instantiated in Lean; on paper, Lebesgue content on bounded finite unions of intervals with compact intervals as `C` satisfies the hypotheses.
- `addContent_iUnion_eq_sum_of_regular` (line 81): matches (σ-additivity of a finite regular content on a set ring, via `addContent_iUnion_eq_sum_of_tendsto_zero`). The `hm_ne_top` hypothesis is needed and present.

## Nonvacuity examples
File: `Nonvacuity.lean`. Compiled from the repository root with `lake env lean`. Exit status 0, no errors, no warnings, about 4 s. No `sorry`.

```lean
import BouRabeeGwynne.Upstream.BrownianMotion.Continuity.KolmogorovChentsovInequality
import BouRabeeGwynne.Upstream.BrownianMotion.Continuity.LimitModification
import BouRabeeGwynne.EuclideanWienerLaw

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal

/-! Nonvacuity examples for batch 13 (audit nonvacuity examples). -/

/-- `[0,1]` has bounded covering number with constant `2` and exponent `1`. -/
theorem nv_covering_Icc : HasBoundedCoveringNumber (Set.Icc (0 : ℝ) 1) 2 1 := by
  refine ⟨by rw [Real.ediam_Icc]; exact ENNReal.ofReal_lt_top, fun ε hε => ?_⟩
  rcases eq_or_ne ε 0 with rfl | hε0
  · rw [ENNReal.coe_zero, ENNReal.inv_zero, ENNReal.top_rpow_of_pos one_pos,
      ENNReal.mul_top two_ne_zero]
    exact le_top
  · have h1 : ε ≤ 1 := by
      have h := hε
      rw [Real.ediam_Icc, sub_zero, ENNReal.ofReal_one] at h
      exact_mod_cast h
    calc (coveringNumber ε (Set.Icc (0 : ℝ) 1) : ℝ≥0∞)
        ≤ 1 / ε := coveringNumber_Icc_zero_one_le_one_div h1
      _ = 1 * (ε : ℝ≥0∞)⁻¹ := by rw [one_div, one_mul]
      _ ≤ 2 * ((ε : ℝ≥0∞)⁻¹ ^ (1 : ℝ)) := by
        rw [ENNReal.rpow_one]
        exact mul_le_mul' (by norm_num) le_rfl

/-- The identity process on `ℝ` over the one-point probability space satisfies the
Kolmogorov condition with `p = q = 2` and `M = 1`. -/
theorem nv_kolmogorov_identity :
    IsKolmogorovProcess (fun (t : ℝ) (_ : Unit) => t) (Measure.dirac ()) 2 2 1 := by
  refine ⟨fun s t => measurable_const, fun s t => ?_, by norm_num, by norm_num⟩
  simp

/-- A countable subset of `[0,1]`. -/
abbrev nvSet : Set ℝ := Set.Icc (0 : ℝ) 1 ∩ Set.range ((↑) : ℚ → ℝ)

/-- The Kolmogorov-Chentsov Hölder finiteness applies to the identity process on `[0,1]`
along the countable set `nvSet`. -/
theorem nv_kc_hypotheses_hold : ∀ᵐ ω ∂(Measure.dirac ()),
    ⨆ (s : ↥nvSet) (t : ↥nvSet),
      edist ((fun (u : ℝ) (_ : Unit) => u) s ω) ((fun (u : ℝ) (_ : Unit) => u) t ω) ^ (2 : ℝ)
        / edist (s : ℝ) (t : ℝ) ^ (((1 / 4 : ℝ≥0) : ℝ) * (2 : ℝ)) < ∞ := by
  have hT' : nvSet.Countable := (Set.countable_range _).mono Set.inter_subset_right
  exact IsKolmogorovProcess.ae_iSup_rpow_edist_div_lt_top nv_covering_Icc nv_kolmogorov_identity
    (by simp) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hT' Set.inter_subset_left

/-- The identity process is a limit of its own indicator process on all of `ℝ` (`A = univ`). -/
theorem nv_limit_of_indicator :
    IsLimitOfIndicator (fun (t : ℝ) (_ : Unit) => t) (fun (t : ℝ) (_ : Unit) => t)
      (Measure.dirac ()) Set.univ := by
  refine ⟨Set.univ, MeasurableSet.univ, Filter.Eventually.of_forall (fun _ => Set.mem_univ _),
    fun t _ ω _ => ⟨t, ?_⟩, fun t _ ω => ?_, fun t ht => absurd (Set.mem_univ t) ht⟩
  · exact tendsto_comap
  · have ht : Tendsto (fun t' : denseCountable ℝ => indicatorProcess
        (fun (u : ℝ) (_ : Unit) => u) Set.univ t' ω) (comap Subtype.val (𝓝 t)) (𝓝 t) := by
      simp only [indicatorProcess_apply, Set.mem_univ, ite_true]
      exact tendsto_comap
    rw [dense_denseCountable.extend_eq_of_tendsto ht, edist_self]

/-- A standard Brownian law on `C([0,∞), ℝ¹)` exists (`BouRabeeGwynne.EuclideanWienerLaw`). -/
example : ∃ μ : Measure (BouRabeeGwynne.BrownianPath 1), BouRabeeGwynne.IsStandardBrownianLaw μ :=
  ⟨_, BouRabeeGwynne.isStandardBrownianLaw_euclideanWienerLaw 1⟩
```

What these show (all with the batch's hypotheses instantiated concretely):
- `nv_covering_Icc`: `HasBoundedCoveringNumber (Icc 0 1) 2 1` holds. It uses Mathlib's `coveringNumber` and the existing `coveringNumber_Icc_zero_one_le_one_div`. So the covering bundle is satisfiable with a set of nonzero diameter, not only a singleton.
- `nv_kolmogorov_identity`: `IsKolmogorovProcess` holds for the identity process on `ℝ` over `Measure.dirac ()`, with `p = q = 2`, `M = 1`. So the Kolmogorov bundle is satisfiable.
- `nv_kc_hypotheses_hold`: the full a.s. Kolmogorov–Chentsov finiteness theorem applies with `c = 2`, `d = 1`, `p = q = 2`, `M = 1`, `β = 1/4` (so `β < (q-d)/p = 1/2`) and the countable `T' = [0,1] ∩ ℚ`. The conclusion is a genuine Hölder-finiteness statement for an instance, not a vacuous one.
- `nv_limit_of_indicator`: `IsLimitOfIndicator` holds for the identity process with `A = univ`, so that definition is satisfiable and not contradictory.
- The Brownian example cites the existing `isStandardBrownianLaw_euclideanWienerLaw` and compiles. The import chain from this batch's modules to that theorem is checked by the `import` lines above; I did not read its proof.

Not attempted: a Lean instance of `tendsto_zero_of_regular_addContent` / `addContent_iUnion_eq_sum_of_regular` (the hypotheses are standard and satisfiable on paper, but building the ring, compact system and content was not worth the time budget).

RESULT: DONE
Verdicts: OK 4, NOTE 1, ISSUE 0 (5 modules).
