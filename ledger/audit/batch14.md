# Audit batch 14
| Module | Verdict | Summary |
|---|---|---|
| SpherePackings.Support.Section4.AmbientExitPartitions | OK | One statement; quantifiers and the ambient/Brownian comparison match the docstring; hypotheses are only the documented ambient collar and localized Assumption D. |
| SpherePackings.Support.Section4.AssumptionD | NOTE | `TilingAssumptionD` is the documented localization of Assumption D and is satisfiable (Example 1); two out-of-batch docstrings are stale. |
| SpherePackings.Support.Section4.BackwardExitPartitions | OK | Partitions and moduli are chosen before the eventual index; ℕ-subtractions are exact because indices are bounded; matches docstring. |
| SpherePackings.Support.Section4.BallExitConvergence | OK | Test-function convergence is uniform over all interior vertices; the integrals are not junk. |
| SpherePackings.Support.Section4.BallExitCouplingInputs | OK | Modulus δ is quantified before `∀ᶠ n` in both lemmas, as the docstrings say; the cell lemma's modulus is not partition-independent, as documented. |
| SpherePackings.Support.Section4.BallExitLevyProkhorov | NOTE | Compact-K LP lemma matches its docstring (this is the weaker lemma behind Prop 4.2(b)); the `toReal` in `levyProkhorovDist` cannot see `⊤` for probability measures. |
| SpherePackings.Support.Section4.CouplingPartitions | OK | Partitions, selectors and δ₀ precede `∀ᶠ n`; starts are uniform; margin and non-termination conditions match the docstring; the `⊤` instance on `Option` is correct for a finite index set. |
| SpherePackings.Support.Section4.HarmonicMeasure | NOTE | Both statements match their docstrings; `hDomain` is an unused hypothesis in the first lemma (harmless). |
| SpherePackings.Support.Section4.Prop42 | ISSUE | `prop42_assumptionD` is labelled Proposition 4.2, but part (b) is uniform only over compact `K ⊂ ball`; the paper claims `sup` over the open unit ball. |
| SpherePackings.Support.Section4.Theorem41 | OK | Conclusion is Theorem A's conclusion with `TilingAssumptionD`; the restriction to orthogonal tilings is stated in the header and registered as weakened; `theoremA_of_theorem41` discharges the hypothesis via Theorem B(a). |
| SpherePackings.Support.Section4.UniformStoppedWalkConvergence | NOTE | Statement is faithful (uniform over `z ∈ U` and over all walk laws satisfying the predicate); the main lemma has no docstring; ℕ-subtraction in `brownianSelectorForWalk` aliases index 0 (proof-only, harmless). |

Counts: OK 6, NOTE 4, ISSUE 1. No module in this batch is under `Upstream/`.

## SpherePackings.Support.Section4.AmbientExitPartitions
- `eventually_ambient_finite_accessible` (private, line 23): proof helper for finiteness and boundary access; no statement of its own to judge.
- `exists_backward_ambient_exit_partitions` (line 42): the discrete side is `discreteHarmonicMeasure` on `closedVertices W` absorbed at `{v | pos v ∈ ball (c j) r}`, pushed to positions, and the Brownian side is `stoppedBrownianLaw … .map endPoint`. This is the comparison the docstring (lines 39–41) describes. The `∀ᶠ n` (line 64) comes after all partitions, moduli and `m` are existentially quantified. Example 2 exercises this chain on the lattice instance (see the nonvacuity section for the limits of that check).

## SpherePackings.Support.Section4.AssumptionD
- `TilingAssumptionD` (line 21): for every ball `ball c r` with `HasAmbientCollar` (closure inside `interior G.domain`) and every `h` harmonic on an open neighbourhood of the closure, `DirichletApproximationTarget` holds with boundary data `h ∘ pos`. This is the printed Assumption D (`rw-spheres.tex:1438–1462`) restricted to these balls, with (4.1) kept separately as `ApproximationCondition`. The printed condition on these balls implies the localized one, so the localized hypothesis is the weaker one. This is the documented localization (README correction 1 and CORRESPONDENCE.md:221).
- `tilingAssumptionD_of_paperRegularity` (line 28): it is not an extra hypothesis in Theorem A's setting. It is derived from `PaperRegularity G` and `ApproximationCondition` through `theoremB_part_a` (`BouRabeeGwynne/Section3TheoremBPartA.lean:14`). The repository has no `sorry` or `axiom` declarations. Example 1 compiles this instance.
- Out-of-batch docstrings (no effect on any statement): `BouRabeeGwynne/TheoremBStatement.lean:93` calls Theorem B(a) "an unproved target" and line 17 says "no proof of either convergence theorem is claimed", although `theoremB_part_a` proves it. `BouRabeeGwynne/TheoremAStatement.lean:11` says Theorem A is "a proposition to be proved". `BouRabeeGwynne/TheoremAStatement.lean:15` and `BouRabeeGwynne/TheoremBStatement.lean:21` cite `STATEMENT_SPEC.md`, which does not exist in the repository.

## SpherePackings.Support.Section4.BackwardExitPartitions
- `ExitPartitionStage` (private structure, lines 23–49): `modulus_pos` (line 29) is strictly positive; `comparison` (lines 38–49) gives tolerance `b / (card + 1)`, which is the per-stage error the coupling sums over the `K + 1` stages.
- `exists_backward_ball_exit_partitions` (line 116): the chain `P i = seq (L − i)` uses ℕ-subtraction, which is exact since `i.val ≤ L`. The stated fact that stage `i.castSucc` cells fit within `δ i.succ` (lines 132–133) is what `hback` proves. The partitions are chosen before `∀ᶠ n` (line 137), as the docstring (lines 112–115) says.

## SpherePackings.Support.Section4.BallExitConvergence
- `eventually_ball_exit_test_error` (line 26): for continuous `f`, the bound is uniform over all interior vertices (docstring lines 23–25). The Bochner integrals are not junk: the discrete measure lives on a finite set, and the Brownian endpoint law is carried by the compact `frontier (ball c r)` (`brownianSpatialHarmonicMeasure_ae_mem_frontier`), so `f` is integrable. No hypothesis is contradictory (Example 2).

## SpherePackings.Support.Section4.BallExitCouplingInputs
- `eventually_ball_exit_nearby_levyProkhorov_error` (line 26): `∀ ε, ∃ δ, ∀ᶠ n` has the right order, with the modulus fixed before the eventual index, as the docstring (lines 23–25) says.
- `eventually_ball_exit_nearby_cell_error` (line 77): `hnull` (frontier null for `z ∈ K`) is the continuity-cell hypothesis. The conclusion `|μ(S).toReal − ν(S).toReal| ≤ ε` is uniform over the finitely many cells `i`. The `toReal` is faithful because both measures are probability measures. The docstring (lines 74–76) says the modulus is not partition-independent, which matches the statement, since `δ` depends on `S`.

## SpherePackings.Support.Section4.BallExitLevyProkhorov
- `eventually_ball_exit_levyProkhorov_error` (line 26): uniform over vertices whose positions lie in a fixed compact `K ⊂ ball` (docstring lines 23–25 says so). The quantifier order `∀ ε, ∀ᶠ n` is right. This lemma is the content of Prop 4.2(b), so see the ISSUE below.
- Junk value (cannot matter): `levyProkhorovDist` (Mathlib `LevyProkhorovMetric.lean:166`) is `(levyProkhorovEDist μ ν).toReal`. By `levyProkhorovEDist_le_max_measure_univ` (line 106), it is at most `max (μ univ) (ν univ) = 1` for probability measures, so the `toReal` never sees `⊤`. Both arguments are `ProbabilityMeasure`s (`spatialExitProbability`, `brownianSpatialHarmonicMeasure`).
- `spatialExitProbability` (`BouRabeeGwynne/Section4BallExitLevyProkhorov.lean:26–30`) chooses its finiteness witness with `hg.choose`. That witness is a `Prop`, and `spatialExitProbability_eq` (lines 34–43) is `rfl`, so the choice cannot change the measure.

## SpherePackings.Support.Section4.CouplingPartitions
- `exists_eventual_walkBrownian_coupling_partitions` (line 29): `m`, `E`, `select`, `hs`, `δ₀` and the margin and non-termination conditions (lines 44–47) come before `∀ᶠ n` (line 48). The starts are uniform (lines 59–61). The bound `(K + 1) * ofReal b` (line 66) is non-trivial. The conditions match the docstring (lines 26–28): `ball x (r/2) ⊆ ball j r` (line 45) and `select i x ≠ none` on `C` (line 46).
- `local instance … : MeasurableSpace (Option X) := ⊤` (line 24) is used only with `X = ↥centers`, a finite type. `⊤` is then the discrete σ-algebra, and `Measurable (select i)` is a genuine fibre condition, so this is not a trap.
- `goodExcursionPair` (`BouRabeeGwynne/WalkBrownianGoodEvent.lean:20`) encodes "same active cell" or "both terminated and endpoint distance ≤ a", which matches its docstring.

## SpherePackings.Support.Section4.HarmonicMeasure
- `eventually_spatialHarmonicMeasure_harmonic_error` (line 27): the conclusion `≤ η` for test functions harmonic near the closure matches its docstring (lines 24–26). `hDomain : IsDomain U` (line 30) is never used by the proof. This is harmless, since the hypothesis is satisfiable.
- `eventually_spatialHarmonicMeasure_collar_error` (line 71): the conclusion `≤ η + ρ` follows from `hnear` on `cthickening δ (frontier U)` (line 80), and the two-mesh overshoot uses `mesh ≤ δ/2` (line 91), as the docstring (lines 68–70) says. `η` is not assumed nonnegative, but `hnear` together with the nonempty frontier of a bounded nonempty open set forces `η ≥ 0`, so this is harmless.

## SpherePackings.Support.Section4.Prop42
- `prop42_assumptionD` (line 20), ISSUE. Part (a) (lines 25–36) is uniform over all continuous test functions and all interior vertices, which matches the paper's `sup over x ∈ B` for test functions. Part (b) (lines 37–46) is the Lévy–Prokhorov claim, and it is uniform only over compact `K ⊆ ball`.
- The paper's Proposition 4.2 (`rw-spheres.tex:1511–1515`) asserts `lim_n sup_{x ∈ B} d_P(hm_n(x), hm(x)) = 0` over the open unit ball. Part (b) gives, for each `K`, an eventual index that may depend on `K`. Nothing in (b) controls points approaching `∂B`, so (b) does not give the paper's `sup`. I did not construct a counterexample to the paper's form.
- The header (lines 1–15) discloses the compact-subset restriction, but the file is titled "Proposition 4.2". The README's PARTIAL list (`README.md:179–196`) does not mention it.
- The registered statement is `SpherePackings.Frozen.prop42_general` (`SpherePackings/Frozen/Prop42General.lean:22–29`), which is uniform over `∀ x ∈ ball c r`; CORRESPONDENCE.md:209 says the same. So no registered claim is overstated. This module's part (b) is an unregistered, weaker intermediate.
- Example 3 instantiates this statement's hypotheses in the lattice instance.

## SpherePackings.Support.Section4.Theorem41
- `theorem41_tiling` (line 19): the conclusion is the same as `TheoremAStatement` (`BouRabeeGwynne/TheoremAStatement.lean:40–51`) and as the registered `SpherePackings.Frozen.theorem41_tiling` (`SpherePackings/Frozen/Theorem41Tiling.lean:25–36`). The hypotheses are `IsLipschitzDomain`, boundedness, ambient collar, (1.3) and `TilingAssumptionD`. The restriction to orthogonal tilings is stated in the header (lines 9–12) and registered as "weakened" (CORRESPONDENCE.md:208).
- The `∃ μ` and `∃ walkLaw` clauses carry no slack. `IsStoppedTilingWalkLaw` (`StoppedCurveLaws.lean:100–113`) determines its measure (`μ = law.map curve`, with the finite set `R`, `start` and `hpos` unique), so the Lévy–Prokhorov bound constrains the actual walk law.
- `theoremA_of_theorem41` (line 49) gives `TheoremAStatement`, with `tilingAssumptionD_of_paperRegularity` as the only extra input.

## SpherePackings.Support.Section4.UniformStoppedWalkConvergence
- `eventually_stoppedWalkLaw_levyProkhorov_le` (line 25): `∀ᶠ n, ∀ z ∈ U, ∀ ν, IsStoppedTilingWalkLaw … ν → levyProkhorovEDist ν (stoppedBrownianLaw U z μ) ≤ ofReal η`. The universal over `ν` is the right form, since the predicate determines `ν`, so the statement is not vacuous. The bound is uniform over `z ∈ U`, as in Theorem A. The lemma has no docstring.
- `brownianSelectorForWalk` (`WalkBrownianCoupling.lean:41–42`) is `select (n − 1)`, so ℕ-subtraction aliases index 0 onto `select 0`, the same selector as index 1. The file docstring says state 0 is the fixed initial excursion, and the proof uses `hs (i − 1)` and `hmargin (i − 1)` consistently. The statement does not mention the selector, so this is harmless.

## Nonvacuity examples
Compiled from the repository root with the exact command:
`lake env lean Nonvacuity.lean`

Result: exit 0 in about 5 s, with no build. The only output was one linter warning: the unused binder `N` in Example 3's statement (line 35), which is cosmetic.

```lean
import SpherePackings.Support.Section4.AssumptionD
import SpherePackings.Support.Section4.Theorem41
import SpherePackings.Support.Section4.Prop42
import SpherePackings.Support.Guards.LatticeTilings
import SpherePackings.Support.Guards.LipschitzBall
import BouRabeeGwynne.EuclideanWienerLaw

open MeasureTheory Filter Metric
open BouRabeeGwynne SpherePackings

-- Example 1: the Assumption D bundle is jointly satisfiable with (1.3) and PaperRegularity.
example {d : ℕ} (hd : 1 ≤ d) : ∃ (G : TilingSequence d) (N : NearestVertexData G),
    N.ApproximationCondition ∧ PaperRegularity G ∧ TilingAssumptionD G := by
  obtain ⟨G, -, ⟨N⟩, hN, hII⟩ := exists_lattice_tilingSequence hd
  exact ⟨G, N, hN N, Or.inr (Or.inl hII),
    tilingAssumptionD_of_paperRegularity hd G N (hN N) (Or.inr (Or.inl hII))⟩

-- Example 2: the full hypothesis bundle of Theorem 4.1 on the unit ball is satisfiable, and
-- Theorem 4.1 applied to it produces a standard Brownian law and eventual stopped walk laws.
example {d : ℕ} (hd : 1 ≤ d) : ∃ (G : TilingSequence d) (N : NearestVertexData G),
    ∃ μ : Measure (BrownianPath d), IsStandardBrownianLaw μ ∧
    ∃ walkLaw : ℕ → Euc d → Measure (CurveSpace d),
      ∀ᶠ n in atTop, ∀ z ∈ Metric.ball (0 : Euc d) 1,
        IsStoppedTilingWalkLaw (G.tiling n) (Metric.ball (0 : Euc d) 1) (N.vertex n z)
          (walkLaw n z) := by
  obtain ⟨G, hcol, ⟨N⟩, hN, hII⟩ := exists_lattice_tilingSequence hd
  obtain ⟨μ, hμ, -, walkLaw, hwalk, -⟩ :=
    theorem41_tiling hd G N (Metric.ball (0 : Euc d) 1) (isLipschitzDomain_ball hd)
      Metric.isBounded_ball hcol (hN N)
      (tilingAssumptionD_of_paperRegularity hd G N (hN N) (Or.inr (Or.inl hII)))
  exact ⟨G, N, μ, hμ, walkLaw, hwalk⟩

-- Example 3: the hypotheses of Proposition 4.2 on the unit ball are satisfiable; the statement
-- instantiates with the standard Brownian law `euclideanWienerLaw d`.
example {d : ℕ} (hd : 1 ≤ d) : ∃ (G : TilingSequence d) (N : NearestVertexData G),
    ∃ (μ : Measure (BrownianPath d)) (hμ : IsStandardBrownianLaw μ),
    (∀ K : Set (Euc d), IsCompact K → K ⊆ Metric.ball (0 : Euc d) 1 → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop,
        ∃ hg : (G.tiling n).HasFiniteAccessibleRegion (Metric.ball (0 : Euc d) 1),
          ∀ v : (G.tiling n).V, ∀ hv : v ∈ (G.tiling n).interiorVertices (Metric.ball (0 : Euc d) 1),
            (G.tiling n).pos v ∈ K →
            levyProkhorovDist
              ((G.tiling n).spatialExitProbability (Metric.ball (0 : Euc d) 1) hg v
                ((G.tiling n).interiorVertices_subset_closedVertices _ hv) : Measure (Euc d))
              (brownianSpatialHarmonicMeasure (Metric.ball (0 : Euc d) 1) Metric.isOpen_ball μ hμ
                ((G.tiling n).pos v) : Measure (Euc d)) < ε) := by
  obtain ⟨G, hcol, ⟨N⟩, hN, hII⟩ := exists_lattice_tilingSequence hd
  have hAD := tilingAssumptionD_of_paperRegularity hd G N (hN N) (Or.inr (Or.inl hII))
  have hμ := isStandardBrownianLaw_euclideanWienerLaw d
  exact ⟨G, N, _, hμ, fun K hK hKU ε hε =>
    (prop42_assumptionD hd G N 0 one_pos hcol (hN N) hAD hμ).2 K hK hKU ε hε⟩
```

What they show:
- **Example 1**: (1.3), `PaperRegularity` and `TilingAssumptionD` hold together on the lattice instance from `exists_lattice_tilingSequence` (domain `ball 0 2`, ambient collar `ball 0 1`, every nearest-vertex choice satisfies (1.3), hypothesis (II) holds). So the localized Assumption D is not vacuous.
- **Example 2**: Theorem 4.1's whole hypothesis bundle holds on that instance, and `theorem41_tiling` produces a standard Brownian law and eventual stopped walk laws. The scratch file imports (directly or transitively) all eleven batch modules, and `theorem41_tiling` depends on the chain, so the lattice instance exercises all of them. The examples do not test each internal lemma's hypotheses separately.
- **Example 3**: Proposition 4.2's hypotheses hold on the lattice instance with `μ = euclideanWienerLaw d`, and part (b) instantiates for compact `K ⊂ ball 0 1`. This is the compact-`K` form that the ISSUE refers to.
- **Not covered**: the nonvacuity of the internal `hnull` cell hypotheses, and of the non-lattice cases of `PaperRegularity` (planar, or (III)). Those are not needed for the batch statements, since the lattice instance already discharges every batch hypothesis.
