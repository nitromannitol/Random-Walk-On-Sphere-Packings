# Audit batch 21
| Module | Verdict | Summary |
|---|---|---|
| SpherePackings.Support.Poisson.Basic | NOTE | `IsPoissonPointProcess` admits Lebesgue intensity (by reasoning); `ncard` junk on unbounded sets (docstring overclaims, harmless); unsatisfiable for atomic intensities (compiled) |
| SpherePackings.Support.Poisson.Tails | OK | Poisson tail estimates match display (5.2); only bounded sets used |
| SpherePackings.Support.Voronoi.PoissonCells | NOTE | `voronoi_cells_between_balls` matches corrected Prop 1.1; vacuous for an intensity with an atom outside `W` |
| SpherePackings.Support.Counterexample.Construction | OK | `SpherePacking`, `Tangent`, `tangentHalfspace`, `Covered`, centres, radii, `levelValue` mean what they say; the `d ≥ 4` parity restriction is documented and checked |
| SpherePackings.Support.Counterexample.Covering | OK | `packing_covered`: every sphere of the dimension-3 packing is covered; non-vacuous (a lone sphere is not covered, compiled) |
| SpherePackings.Support.Section2.DualCoverage | NOTE | corrected Lemma 2.5 as documented; `interiorVertices` is `pos ∈ U`, not `pos ∈ interior U`; reading of `E[Ū]` |
| SpherePackings.Support.Voronoi.GeometricConstraint | NOTE | corrected Lemma 5.1(a), (b) match README and GAP-CHECKS; (b) weaker than printed for `d ≥ 4` (printed false for `d ≥ 14`, open for `4 ≤ d ≤ 13`) |
| SpherePackings.Frozen.Lemma25DualCoverage | NOTE | same as `dual_coverage_natural`; the statement parses as the intended conjunction |
| SpherePackings.Frozen.Lemma51Inner | NOTE | corrected 5.1(a): hypothesis on every grid cube meeting `U`, closed-ball conclusion; both documented |
| SpherePackings.Frozen.Lemma51Outer | NOTE | corrected 5.1(b): `δ = 1/10`, radius `max(2, 2√(d/3))`; equals printed for `d ≤ 3`; non-vacuous (compiled) |
| SpherePackings.Frozen.Theorem61Counterexample | OK | existential statement as printed; non-vacuous: Wiener measure is a standard Brownian law (compiled), and the Brownian target is a genuine probability measure |
| SpherePackings.Frozen.Prop11Cells | NOTE | corrected Prop 1.1 as documented; vacuous for an intensity with an atom outside `W` |

Counts: OK 4 · NOTE 8 · ISSUE 0.

Classification note: the documented corrections (Lemma 2.5 lower inclusion, Lemma 5.1(a), 5.1(b), Prop 1.1) are weaker than, or different from, the printed claim only where the printed claim is false (counterexample recorded in README and GAP-CHECKS) or open (Lemma 5.1(b) for `4 ≤ d ≤ 13`). I recorded them as NOTE. A literal reading of "weaker than the paper claims" would make them ISSUE.

Scope: definitions and statements only; proofs not reviewed.

## SpherePackings.Support.Poisson.Basic
- `IsPoissonPointProcess` (line 25): a simple point process, modelled as a random set. Lebesgue admissibility (by reasoning, not compiled): the standard Poisson process on `ℝ^d` (independent Poisson counts on unit cubes, uniform points) gives an ℕ-valued count per cube, so `finite` holds for every `ω`; counts in a set of finite measure are Poisson with that mean; disjoint restrictions are independent. So infinite total mass is admitted. No Lean construction exists (CORRESPONDENCE says so; not attempted here).
- `finite` (line 29) vs `hasLaw` (line 31) and `indep` (line 34): `finite` is required only for bounded `B`, while `hasLaw` and `indep` cover every measurable `B` with `ν B ≠ ∞`. For unbounded `B` of finite measure nothing rules out infinite `Λ ∩ B`, and `Set.ncard` returns `0` there, so `hasLaw` really says "the count with `∞` recorded as `0` is Poisson". The docstring (lines 13–14) says this event has probability zero for such `B`; the structure does not enforce it. Junk-value NOTE, harmless: every use (Tails, PoissonCells, Prop 1.1) applies counts only to bounded sets, where `finite` makes them exact. Fix if wanted: `∀ᵐ ω ∂P, (Λ ω ∩ B).Finite` for `ν B ≠ ∞`, or count in `ℕ∞`.
- Atoms (compiled, Nonvacuity example 3): for `ν` with an atom of finite positive mass `a` at `x`, `IsPoissonPointProcess P Λ ν → False`, for every `P` and `Λ`. In the set model the count in `{x}` is at most one, while `Po(a)` charges `2`. So atomic intensities are excluded. This is harmless for the paper's `μ`, since `HolderMassBounds` forbids atoms on `W`; for atoms outside `W` see PoissonCells.

## SpherePackings.Support.Poisson.Tails
- `poissonMeasure_real_two_le` (line 45): `P(N ≥ 2) ≤ r²` for all `r ≥ 0`, matching display (5.2). (The header's "constant 1 for every λ ≥ 0" is true: `1 − e^{−r}(1+r) ≤ r²`.)
- `IsPoissonPointProcess.measureReal_empty` (line 68): `P(Λ ∩ B = ∅) = e^{−ν B}` for bounded measurable `B` with `ν B < ∞`. Uses the surely-finite clause, so no junk.
- `IsPoissonPointProcess.measureReal_not_subsingleton_le` (line 88): `P(≥ 2 points) ≤ (ν B)²`. Same finiteness argument.

## SpherePackings.Support.Voronoi.PoissonCells
- `HolderMassBounds` (line 36): (1.4) as `r^{β⁺} ≤ μ(B_r(z)) ≤ r^{β⁻}` for `z ∈ W`, with one uniform `r₀`. The paper (`rw-spheres.tex:365-366`) states it for `z ∈ U`; the correction to an open `W ⊇ closure U` is recorded in README item 6. Non-vacuous for Lebesgue on `ℝ^d` (reasoning: `W = ℝ^d`, `β⁺ = 2d`, `β⁻ = d/2`, `r₀ = min(1, ω_d^{1/d}, ω_d^{−2/d})`).
- `voronoi_cells_between_balls` (line 434) and `voronoi_cells_between_balls_aux` (line 149): the conclusion matches Proposition 1.1 (`rw-spheres.tex:371-381`). Quantifiers: `∀ᵐ ω, ∀ᶠ m, ∀ s ∈ Λ_m, (cell ∩ U) ≠ ∅ → B_{m^{−8/β⁻}}(s) ⊆ cell ⊆ B_{m^{−1/(3β⁺)}}(s)`. Exponents: `βm = β⁻` inside, `βp = β⁺` outside. Correct.
- Vacuity (NOTE): `hΛ` gives the intensity `(m : ℝ≥0∞) • μ`, but `HolderMassBounds` constrains `μ` only on `W`. If `μ` has an atom at `p ∉ closure W` (e.g. `μ = volume + δ_p` with `p` far away), then `(m • μ)` has an atom of mass `m ≥ 1`, and `hΛ` is unsatisfiable for `m ≥ 1` (compiled, Basic). Both theorems then hold vacuously for that `μ`. The paper's `μ` is "defined in a neighborhood of Ū", so atoms outside `W` are arguably out of scope, and a Voronoi tessellation of a multiset is undefined anyway. Recommended: `(m : ℝ≥0∞) • μ.restrict W`, or assume `∀ z, μ {z} = 0`.
- `measure_exists_empty_le` (line 86) and `measure_exists_double_le` (line 103): union bounds are correct (`∑ e^{−c}`; `∑ λ² ≤ M ∑ λ`). No junk: `ofReal` of nonnegative quantities.

## SpherePackings.Support.Counterexample.Construction
- `SpherePacking` (line 31): radii positive; open balls pairwise disjoint (paper: "disjoint interiors"). `ι : Type` is only a universe restriction.
- `Tangent` (line 46): `i ≠ j` and `dist = r_i + r_j`. For disjoint open balls this is "touching", the paper's adjacency rule (`rw-spheres.tex:1820`).
- `tangentHalfspace` (line 51): `{x | ⟪x − c_i, c_j − c_i⟫ ≤ r_i · dist(c_i, c_j)}`. For tangent `j` this is the side containing `c_i` of the hyperplane through the contact point `p = c_i + (r_i/D) u` (`u = c_j − c_i`, `D = |u|`) orthogonal to `u`: `⟪x − p, u⟫ ≤ 0 ⟺ ⟪x − c_i, u⟫ ≤ r_i D`. Correct.
- `Covered` (line 59): matches `rw-spheres.tex:331-333` (`P_v` is a bounded polytope containing `v`). Two readings, both recorded: (1) the paper's "intersection of the hyperplanes" must mean the intersection of the half-spaces on `v`'s side (an intersection of hyperplanes is an affine subspace of dimension at most `d − 1`, or empty, never a `d`-dimensional polytope), and the Lean reads it that way; (2) with infinitely many tangent spheres the set is a bounded closed convex set, not a polytope (the docstring says so). Theorem 6.1 has bounded degree, so (2) has no effect. The set contains a ball around the centre (checked).
- `BigIdx` (line 69), `SmallIdx` (line 72), `Idx` (line 75), `smallOffset` (line 78), `center` (line 82), `radius` (line 87): these reproduce the paper's packing for `k = 0` (`rw-spheres.tex` proof of Theorem 6.1). For `k ≥ 1` the parity restriction on `y_j`, `j ≥ 3`, is a documented modification. Checked: a small sphere with an odd `y_j` (`j ≥ 3`) touches no big sphere. A tangency needs squared distance `9/4`; the `0`-th term `(√7/2 + n)²` is irrational unless `n = 0`, so `n = 0`, the coordinates `1, 2` each contribute `1/4`, and every other coordinate difference is `0`, which forces `y_j` even. Also, a small sphere touches a big one only when `y₀ = 0`, and then has exactly one big neighbour, as the paper says.
- `levelValue` (line 92): harmonic for simple random walk (checked): big `x₀ ≤ −1` has 6 neighbours with average `4x₀`; big `x₀ = 0` has 9 neighbours (`−4`, four `0`, four `1`), average `0`; small `y₀ = 0` has 6 neighbours (`2, 1, 1, 1, 1, 0`), average `1`; small `y₀ ≥ 1` has 6 neighbours, average `y₀ + 1`. Docstring slip (harmless): the module header says a big sphere at level 0 has "one neighbour at level −1 and four at level 1", omitting its four neighbours `x ± e₁`, `x ± e₂` at level 0, which contribute `0`.
- `origin` (line 97): the centre of the big sphere `x = 0`. Correct.

## SpherePackings.Support.Counterexample.Covering
- `packing_covered` (line 252): `∀ i : Idx 0, (packing 0).Covered i`, i.e. every sphere of the dimension-3 packing is covered. Matches the definitions in Construction and the docstring. Proof lemmas not reviewed. Non-vacuity: `Covered` is not trivially true (Nonvacuity example 1), and the packing example compiles (example 2).

## SpherePackings.Support.Section2.DualCoverage
- `dual_coverage_natural` (line 138), the content of frozen Lemma 2.5: the printed first inclusion `U ⊆ ⋃_{e∈E[Ū]} Q_e` is replaced by coverage of the cells of `V[U]` under `hcellD`. The printed inclusion is false: a small ball inside one square of the unit grid meets no vertex, so `E[Ū] = ∅` (README item 4). The correction is weaker than the printed claim in two documented ways: `hcellD` (cells of `V[U]` lie in `interior D`), and the conclusion covers cells rather than `U`. The second inclusion matches the printed one when `E[Ū]` is read as the edges with an endpoint in `V[U]`. The paper's notation is ambiguous (`rw-spheres.tex:556-557`); the other reading makes the printed union larger.
- `interiorVertices` (`BouRabeeGwynne/LocalRegion.lean:13`, used here): `{v | pos v ∈ U}`. The paper's `V[U]` is the set of vertices "contained in the interior of `U`" (`rw-spheres.tex:553`). These agree for open `U`, which is how the paper uses them. For non-open `U` the Lean set is larger, and `hcellD` is asked for more cells. The lemma is still true for the Lean set (its proof uses only the per-cell lemma), so this is recorded, not an error.
- `dual_coverage` (line 28, not frozen): the decomposition (cells ⊆ vertices ∪ pyramids over `touchingCells`) is correct. `cell_subset_iUnion_dualPolytope` (line 131) is the per-cell covering statement from which the frozen lemma is derived.
- Definitions checked: `dualPolytope v w = cellPyramid v w ∪ cellPyramid w v`, with `cellPyramid v w = conv(pos v ∪ P_v ∩ P_w)` (`BouRabeeGwynne/DualCells.lean:48-52`), matches `Q_e = conv(w, P_w ∩ P_v) ∪ conv(v, P_w ∩ P_v)` (`rw-spheres.tex`, eq. `eq:qeset`). `neighbors` is `adj` (`LocalRegion.lean:17`), and `adj` is "distinct and share a codimension-one facet" (`PaperObjects.lean:109-110`). `closedVertices` = `V[U] ∪ ∂V[U]` (`LocalRegion.lean:33`), the paper's `V̄[U]`.

## SpherePackings.Frozen.Lemma25DualCoverage
- Statement (lines 20–25): parses as `(A ⊆ X) ∧ (B ⊆ C)`, because `⊆` (precedence 50) binds tighter than `∧` (35), and the `⋃` body stops before `∧`. So the two inclusions are conjoined as intended. Same content as `dual_coverage_natural`; see that entry.

## SpherePackings.Frozen.Lemma51Inner
- Statement (line 18): if every grid cube `x + [−2r, 2r]^d` with `x ∈ rℤ^d` that meets `U` contains at most one point of `S`, then `closedBall s r ⊆ cell S s` for all `s ∈ S ∩ U`. The printed hypothesis (`x ∈ U`) fails at `∂U`, as README item 7 says. I checked the counterexample by hand: `S = {0.1, −1.5}`, `U = (0, 10)`, `r = 1`; at `x = −1` the cube `[−3, 1]` meets `U` and contains both points, so the corrected hypothesis correctly fails there. The conclusion is stronger (closed ball); the hypothesis ranges over more grid cubes. Non-vacuous: `S = 10r·ℤ^d` satisfies the hypothesis (two points of `10r·ℤ^d` differ by more than `4r` in some coordinate). Reasoned, not compiled.

## SpherePackings.Frozen.Lemma51Outer
- Statement (line 20): `δ = 1/10`, grid points `y ∈ kℤ^d` with `y ∈ cthickening (max 2 (2√(d/3))·k) U`, and cube `y + [−k/10, k/10]^d` meets `S`; conclusion `cell S s ⊆ ball s (4k√d)` for `s ∈ S ∩ U`. `cthickening` is the paper's `B_r(U)` (`rw-spheres.tex:1434`, `inf ≤ r`), so it is the closed neighbourhood. For `d ≤ 3` this is the printed statement with `δ = 1/10`, a special case of the printed `∃δ`.
- For `d ≥ 4` it is weaker than printed. GAP-CHECKS G3(ii) shows the printed statement is false for `d ≥ 14`. I re-derived that by hand: for `y ∈ ℤ^d` with `y₁ = 1`, the squared distance to `s` is at least `0.9801 + (d−1)/4`, which exceeds `2.01²` when `d ≥ 14`. So every grid point of `B₂(U)` has `y₁ ≤ 0` and lies in `S`, the cube hypothesis holds for every `δ`, and the ray `s + t e₁` lies in `𝒞_s`. For `4 ≤ d ≤ 13` the printed statement is open.
- Non-vacuity (compiled, example 4): with `S = grid k` the cube hypothesis holds with witness `y` itself, so the conclusion applies.
- The internal `geometric_constraint_outer` (line 128) uses `δ = 1/4` and radius `2k√d`. It is not frozen and is used only by PoissonCells. Its hypothesis region is larger than the printed `B_{2k}(U)`, so it is also weaker than printed. Recorded only.

## SpherePackings.Frozen.Theorem61Counterexample
- Statement (lines 26–38): there is a sphere packing `P` of `ℝ^d` (`d ≥ 3`) with radii in `{1, 1/2}`; bounded degree (`{j | Tangent i j}.Finite` is stated, so the `ncard` junk cannot be used); if `d = 3`, every sphere is covered (an addition, stronger than printed); a sphere at the origin; walk laws eventually equal to `IsStoppedSRWLaw (1/n)` on `ball 0 1`; and for every standard Brownian law `μ` and every eventually-SRW `walkLaw`, `¬ Tendsto (levyProkhorovEDist (walkLaw n) (stoppedBrownianLaw (ball 0 1) 0 μ)) atTop (𝓝 0)`. This matches Theorem 6.1 (`rw-spheres.tex:1791-1794`) as the frozen docstring describes.
- Non-vacuity: (a) The `∀ μ` clause is inhabited: `isStandardBrownianLaw_euclideanWienerLaw` (compiled, example 5). (b) The Brownian target is a genuine probability measure, not the zero measure from `Measure.map` of a non-measurable map: `measurable_stoppedBrownianCurve` holds for open `U` (`BouRabeeGwynne/StoppedBrownianMeasurable.lean:81-82`). Against the zero measure, the Lévy–Prokhorov distance from any probability measure is at least `1`, and `¬Tendsto` would hold trivially; this does not happen here. (c) The walk side is `AEMeasurable` by the definition of `IsStoppedSRWLaw` (`SpherePackings/Support/Counterexample/WalkLaw.lean:55`), which also requires a.s. finite exit and `μ = law.map curve`. (d) The walk laws exist: conjunct 1 is part of the proven theorem.
- Caveats (not verdict-changing): the `d ≥ 4` packing differs from the printed one (documented, README item 9); the statement is existential, so it is still the printed claim. CORRESPONDENCE labels Theorem 6.1 "as printed", which is accurate for the statement but not for the `d ≥ 4` witness.

## SpherePackings.Frozen.Prop11Cells
- Statement (line 21): identical to `voronoi_cells_between_balls` (see PoissonCells), with the `W`-correction. Hypothesis `IsBounded U` only, with no connectivity or openness. This is more general than the printed bounded domain. Vacuity for intensities with atoms outside `W` as above. Non-vacuous for Lebesgue on `ℝ^d` (reasoning, as above).

## Observations outside this batch (not verdicted)
- `BouRabeeGwynne/PaperObjects.lean:157-158`: `mesh := ⨆ v, (T.cell v).diamENN`, and `RegularityII` (lines 207–213) uses `mesh.toReal`. `ENNReal.toReal ⊤ = 0`, and `mesh` is `⊤` when the cell diameters are unbounded over all vertices. The structure does not exclude this: `locallyFinite` constrains only compact subsets of the domain, and cells outside `D` are unconstrained. Then the first clause of (II) holds vacuously, and (II) reduces to `minTileVolume.toReal > 0` eventually. `PaperRegularity` (line 223) is a disjunction that includes II, so this may weaken Theorems A and B. Not checked; it belongs to the batch that owns Theorem A.
- `BouRabeeGwynne/LocalRegion.lean:13`: `interiorVertices` uses `pos ∈ U` (see DualCoverage).

## Nonvacuity examples
Compiled from the repository root with `lake env lean Nonvacuity.lean`. Exit 0, no output: no errors, warnings or `sorry`.

```lean
import SpherePackings.Support.Counterexample.Covering
import SpherePackings.Support.Poisson.Basic
import SpherePackings.Frozen.Lemma51Outer
import BouRabeeGwynne.EuclideanWienerLaw

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal NNReal

namespace AuditBatch21

open SpherePackings SpherePackings.Voronoi BouRabeeGwynne

/-- One sphere of radius `1` at the origin: nothing touches it. -/
def lonelyPacking (d : ℕ) : SpherePacking d where
  ι := Unit
  center := fun _ => 0
  radius := fun _ => 1
  radius_pos := fun _ => one_pos
  disjoint := fun i j h => absurd (Subsingleton.elim i j) h

/-- A sphere with no tangent neighbour is not covered, in every dimension `d ≥ 1`. -/
example (d : ℕ) (hd : 1 ≤ d) : ¬ (lonelyPacking d).Covered () := by
  have : NeZero d := ⟨by omega⟩
  intro h
  unfold SpherePacking.Covered at h
  have hempty : ∀ j, ¬ (lonelyPacking d).Tangent () j := fun j hj => hj.1 (Subsingleton.elim (α := Unit) _ _)
  have huniv : (⋂ j ∈ {j | (lonelyPacking d).Tangent () j},
      (lonelyPacking d).tangentHalfspace () j) = univ := by
    ext x
    simp [hempty]
  rw [huniv] at h
  exact NormedSpace.unbounded_univ ℝ (Euc d) h

/-- The packing of Theorem 6.1 in dimension three covers every sphere (`Covering.lean`). -/
example : ∀ i, (SpherePackings.Counterexample.packing 0).Covered i :=
  SpherePackings.Counterexample.packing_covered

/-- An intensity with an atom of mass `1` admits no Poisson point process in the set model: the
count in `{x}` is at most one, while the Poisson law with mean `1` charges `2`. -/
example {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω) (Λ : Ω → Set (Euc d)) (x : Euc d)
    (h : IsPoissonPointProcess P Λ (Measure.dirac x)) : False := by
  have hν : (Measure.dirac x) {x} = 1 := Measure.dirac_apply_of_mem rfl
  have hL := h.hasLaw {x} (measurableSet_singleton x) (by rw [hν]; simp)
  have hr : (Measure.dirac x {x}).toNNReal = 1 := by rw [hν]; simp
  rw [hr] at hL
  have hle : ∀ ω, (Λ ω ∩ {x}).ncard ≤ 1 := fun ω =>
    (Set.ncard_le_ncard Set.inter_subset_right (Set.finite_singleton x)).trans
      (Set.ncard_singleton x).le
  have h2 : P.map (fun ω => (Λ ω ∩ {x}).ncard) {2} = 0 := by
    rw [Measure.map_apply_of_aemeasurable hL.aemeasurable (measurableSet_singleton 2)]
    have hpre : (fun ω => (Λ ω ∩ {x}).ncard) ⁻¹' {2} = ∅ := by
      ext ω
      have := hle ω
      simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      omega
    rw [hpre, measure_empty]
  rw [hL.map_eq] at h2
  have hpos : (poissonMeasure 1) {2} ≠ 0 := by
    rw [poissonMeasure_singleton]
    exact (ENNReal.ofReal_pos.mpr (by simp; positivity)).ne'
  exact hpos h2

/-- Lemma 5.1(b), the frozen statement, applied to `S = grid k`: the cube hypothesis holds with the
point `y` itself, so the statement is not vacuous. -/
example {d : ℕ} (hd : 1 ≤ d) (U : Set (Euc d)) {k : ℝ} (hk : 0 < k) :
    ∀ s ∈ grid k ∩ U, cell (grid k) s ⊆ ball s (4 * k * Real.sqrt d) :=
  SpherePackings.Frozen.lemma51b_outer hd U (grid k) hk fun y hy =>
    ⟨y, hy.1, show ∀ j, |y j - y j| ≤ k / 10 from fun j => by simp; linarith⟩

/-- The `∀ μ` clause of Theorem 6.1 is not vacuous: a standard Brownian law exists (Wiener measure). -/
example (d : ℕ) : ∃ μ : Measure (BrownianPath d), IsStandardBrownianLaw μ :=
  ⟨_, isStandardBrownianLaw_euclideanWienerLaw d⟩

end AuditBatch21
```

What they show:
1. Example 1 (lines 21–32): a lone sphere with no tangent neighbour is not covered, for every `d ≥ 1`. `Covered` is not trivially true.
2. Example 2 (lines 34–36): the Theorem 6.1 packing covers every sphere in dimension three.
3. Example 3 (lines 38–61): for every `P` and `Λ`, `IsPoissonPointProcess P Λ (Measure.dirac x) → False`. An intensity with an atom of mass 1 admits no Poisson point process in the set model. The same argument applies to any atom of finite positive mass `a` (reasoned, not compiled; the compiled case is `a = 1`). This is the atomic-intensity finding.
4. Example 4 (lines 63–68): the frozen Lemma 5.1(b) applies to `S = grid k`. The hypothesis bundle is satisfiable and the conclusion is not vacuous.
5. Example 5 (lines 70–72): Wiener measure is a standard Brownian law, so the `∀ μ` clause of Theorem 6.1 is not vacuous.

Reasoned, not compiled:
- Lebesgue intensity on `ℝ^d` satisfies `IsPoissonPointProcess` (the standard Poisson process; see Basic).
- `HolderMassBounds volume univ (2d) (d/2)` holds with `r₀ = min(1, ω_d^{1/d}, ω_d^{−2/d})`, where `ω_d` is the volume of the unit ball. So the Prop 1.1 hypotheses are satisfiable with `μ = volume` and any bounded `U`, on a space carrying the Poisson processes.
- `hcellD` holds for any tiling whose domain is `ℝ^d`, since the interior of `univ` is `univ`.
- The Lemma 5.1(a) hypothesis holds for `S = 10r·ℤ^d`.
- Not attempted: a Lean construction of any `IsPoissonPointProcess` (out of scope for the 30-minute budget; CORRESPONDENCE records that none exists in the repository).
