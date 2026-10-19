# Audit batch 22
| Module | Verdict | Summary |
|---|---|---|
| SpherePackings.Support.Complete.Basic | NOTE | `CompleteCell` and `dual_coverage_complete` match corrected Corr. 4 and Lemma 2.5; `V[U] = {pos ∈ U}` equals the paper's interior convention only for open `U` |
| SpherePackings.Support.Complete.Fibers | OK | statements only; a.e. nondegenerate fibres over the projected base, as used by Columns/GaussGreen |
| SpherePackings.Support.Complete.GaussGreen | OK | upper/lower neighbour finsets are strict-sign filters; Gauss–Green for complete cells (statements) |
| SpherePackings.Support.Complete.Columns | NOTE | column bad set uses projected cells `y ∈ π(P_v)` instead of the paper's `L_y^{(j)}` (contact projections); equal up to a null set, Lean set larger; `π_j(U)` restriction absent |
| SpherePackings.Support.Complete.Section3 | OK | statements only; hypotheses are quantitative and jointly satisfiable (small `ε`, large `K`); no junk values reached |
| SpherePackings.Support.Section2.AffineKernel | OK | `discreteLaplacian_affine_eq_zero_of_complete` matches corrected Lemma 2.2 ("at every vertex with a complete cell") |
| SpherePackings.Support.Section3.TaylorEnergy | OK | `taylor_of_segment` (sharp `M/2`) and flux residual bounds (`3Mε`) check out by hand; interior-cell versions are intermediate, documented as such |
| SpherePackings.Support.Section3.EnergyComplete | NOTE | Props 2.6/3.2 match corrected Taylor/Hessian hypotheses but are sharper (harmonicity and Hessian only on `V[U]` cells); header's "half the printed (stronger)" is relative to printed sums, not to corrected Corr. 4; `Fintype` extra |
| SpherePackings.Support.Section3.InternalTaylor | OK | internal-edge Taylor bounds (`2Mδ²`, `9M²δ²`) and comparison principle `abs_le_of_abs_laplacian_le` (checked by hand) |
| SpherePackings.Support.Section3.DecayInternal | OK | `generaldim_decay_rate_internal` matches corrected `theorem:generaldim-decay` (M = M_U°∨1, internal Taylor, decay hypothesis up to `F ↦ F d^α`) |
| SpherePackings.Support.Voronoi.GeometricConstraint | NOTE | (a) and (b) match corrected Lemma 5.1; closed thickenings and closed balls (absorbed by `∃ R`; closed balls strengthen (a)); arbitrary `U`, `S` |
| SpherePackings.Support.Voronoi.CountsToCells | OK | composition of Lemma 5.1 with cube counts; hypothesis `min δ (1/4) k ≤ δ k` used correctly |
| SpherePackings.Support.Voronoi.PoissonLocal | NOTE | Prop 1.1 local statements match corrected; `hlf` (sure local finiteness) and `IsDomain` are extra hypotheses; no Poisson process exists in the repo |
| SpherePackings.Frozen.Lemma22AffineKernel | OK | matches corrected Lemma 2.2; the compiled instance on `GT` (Nonvacuity) typechecks |
| SpherePackings.Frozen.Lemma25DualCoverage | NOTE | matches corrected Lemma 2.5; `.olean` (10:59) predates source (11:56), current source elaborates (checked) |
| SpherePackings.Frozen.Lemma31Poincare | NOTE | matches corrected Lemma 3.1 except `π_j(U)` dropped and projected-cell column set (both give a stronger claim); undirected sums per corrected Corr. 4 |
| SpherePackings.Frozen.Prop26Energy | NOTE | matches corrected Prop 2.6 hypotheses but harmonicity and Hessian bound only on `V[U]` cells (corrected: `Ĝ_U`), so stronger; header does not say so; `Fintype` extra |
| SpherePackings.Frozen.Prop32Columns | NOTE | as Prop 2.6 plus the column-set and `π_j(U)` points; threshold equals corrected Prop 3.2 (undirected sums) |
| SpherePackings.Frozen.Theorem37Rate | NOTE | matches corrected `theorem:generaldim-decay`; smallness `12Mε ≤ 1, ε ≤ 1/2` is implied by the paper's `ε < (CM)⁻¹` with C = 12; `Fintype` extra; G4 not re-verified |
| SpherePackings.Frozen.Lemma51Outer | OK | matches corrected Lemma 5.1(b); printed-radius counterexample checked by hand (holds iff d ≥ 13); compiled nonvacuity instance (`δℤ²`) |
| SpherePackings.Frozen.Prop11Cells | OK | matches corrected Prop 1.1 first part; exponents `βp = β⁺`, `βm = β⁻`; `HolderMassBounds` on open `W ⊇ closure U`; no PPP exhibited (see nonvacuity) |
| SpherePackings.Frozen.Prop11TheoremAB | NOTE | Theorem B(a)/(b) and Theorem A gated as in corrected Thm A/B; extra `hlf`; `IsDomain` kept (Prop 1.1 header's "U need not be connected" holds only for the first part); ambient `D` not required to be bounded or inside `W` |

Verdict counts: OK 11, NOTE 11, ISSUE 0.

## SpherePackings.Support.Complete.Basic
- `CompleteCell` (line 26): `(T.neighbors v).Finite ∧ frontier (T.cell v).carrier ⊆ ⋃ w ∈ T.neighbors v, (T.cell w).carrier` matches the corrected paper's "complete" (`paper/rw-spheres-corrected.tex:565–566`: `∂P_v = ⋃_{w∼v}(P_v ∩ P_w)`, finitely many neighbours). The two forms agree because `frontier_eq` (line 34) identifies the frontier with the union of facets, and the frontier lies in the closed cell. `T.neighbors v = {w | T.adj v w}` (`BouRabeeGwynne/LocalRegion.lean:17`), with `adj` = distinct cells meeting in a codimension-one set (`PaperObjects.lean:109–110`), which is the paper's edge set.
- `of_subset_interior` (line 83), `exists_neighbor` (line 95), `cell_subset_iUnion_dualPolytope` (line 121): correct; `exists_neighbor` uses `1 ≤ d` (connectedness of `ℝ^d`).
- `dual_coverage_complete` (line 132): both inclusions match corrected Lemma 2.5 (`rw-spheres-corrected.tex:824–829`). `E[Ū]` is `contactGraph` (edges with at least one endpoint in `V[U]`; `Section3ColumnEdgeIndex.lean:16`) and `Ĝ_U = ⋃_{V̄[U]} P_v` (paper line 596–599). The `∧` parses as intended (`⊆` and `⋃`-bodies bind tighter than `∧`).
  - NOTE: the paper defines `V[U]` as the vertices in the *interior* of `U` (`paper:579–581`). Lean uses `pos v ∈ U` (`LocalRegion.lean:13`) and states the lemma for arbitrary `U`. The two agree for open `U`, which is the paper's domain case; for non-open `U` the Lean `V[U]` is larger.

## SpherePackings.Support.Complete.Fibers
- `ae_lowerFiber_lt_upperFiber` (line 199) and `projectedBase_diff_intrinsicInterior_null` (line 165): a.e. nondegenerate fibres over the projected base; the relative boundary is null. Statement-level only. Matches its use in Columns and GaussGreen. `ConvexPolytope` is compact (`PaperObjects.lean:43–50`), so no junk.

## SpherePackings.Support.Complete.GaussGreen
- `upperNeighborFinset` (line 28), `lowerNeighborFinset` (line 34): strict-sign filters of `neighborFinset` by `⟨pos w − pos v, e⟩`. Zero-inner contacts are excluded a.e. (`ae_neighborFinset_transverse`, line 53). Meaning as documented.
- `sum_surfaceFlux_eq_integral_laplacian_of_complete` (line 351), `sum_surfaceFlux_eq_zero_of_complete` (line 360): Gauss–Green and the harmonic flux identity for complete cells. Statements match their docstrings.

## SpherePackings.Support.Complete.Columns
- `ae_exists_upper_neighbor` (line 36): a.e. exit of each line through a neighbour contact whose segment is longer. Correct.
- `column_bad_measure_le_of_complete` (line 154), `column_poincare_measure_bound_of_complete` (line 188), `column_poincare_of_energy_bound_of_complete` (line 230):
  - NOTE: the bad set is `columnBadSet R A e he f τ` (`Section3ColumnEstimate.lean:24`) = `{y | ∃ v ∈ A, y ∈ π(P_v), τ < |f v|}`. The paper's set (`paper:1025–1032`) is over `L_y^{(j)}[U] = {v ∈ V[U] : v is an endpoint of e ∈ E[L_y]}`, `E[L_y] = {e : y ∈ π(H_e)}`. For complete cells the two agree up to a null set (by `ae_exists_upper_neighbor`). The Lean set is the larger one, so the Lean bound is at least as strong. Direction `e ≠ 0` is general, where the paper has coordinate `j`.
- `incidentEnergy`/`incidentMass` (`Section3ColumnEstimate.lean:15,20`): sum over `orientedInteriorEdges` (`Section3ColumnEdgeIndex.lean:43`), one orientation per contact edge. Undirected, as corrected Corr. 4 (`paper:567–568`) requires.

## SpherePackings.Support.Complete.Section3
- Statements only. `cellVolume_le_adjacent_row_of_complete` (line 69): `vol(P_v) ≤ Σ_w facetVolume·‖Δpos‖` (= d·Σ vol(Q_e)); valid, not sharp by a factor `d`. `incidentMass_trimmed_le_contraction_factor_of_complete` (line 135), `harmonicIteration_mass_le_geometric_of_complete` (line 178), `correctedError_trimmed_mass_le_half_of_complete` (line 237): the quantitative hypotheses (`hwidth`, `hsmall`, `hfactor`) are jointly satisfiable for small `ε`, large `K`. No junk reached (cells compact, facets finite measure).

## SpherePackings.Support.Section2.AffineKernel
- `discreteLaplacian_affine_eq_zero` (line 55): interior-cell version, a special case of the next.
- `discreteLaplacian_affine_eq_zero_of_complete` (line 71): matches corrected Lemma 2.2 (`paper:705–708`). The printed counterexample (two unit squares, `ℓ(x) = x₁`, `Δ_a ℓ = 1` at the left square) checked by hand: conductance `1/1`, increment `1`.

## SpherePackings.Support.Section3.TaylorEnergy
- `taylor_of_segment` (line 27): Taylor's theorem with remainder `(M/2)‖b − a‖²` under a Hessian bound on the segment. Correct (integral remainder).
- `fluxResidual_bound_taylor` (line 89), `surfaceFlux_residual_bound_taylor` (line 136): constant `3Mε` checked by hand (`(M/2)(2ε)‖w−v‖ + Mε‖w−v‖`).
- `energy_error_le_hessian_taylor` (line 192), `harmonic_energy_bound_taylor` (line 254), `harmonic_column_bound_taylor` (line 285): interior-cell intermediates (not registered). Docstrings say so.
- `abs_laplacian_le_taylor` (line 352): correct.

## SpherePackings.Support.Section3.EnergyComplete
- `energy_error_le_complete` (line 30), `harmonic_energy_bound_complete` (line 92), `harmonic_column_bound_complete` (line 129): Taylor hypotheses are the corrected `M/2` finite inequality at one active endpoint (`paper:885–889`), so `T_U(h) ≤ M` is the Lean hypothesis; constants `9` and `3` are the corrected ones with undirected sums.
  - NOTE 1: the Lean hypotheses are sharper than the corrected Props 2.6/3.2 as written. The paper requires `h_C` harmonic on `Ĝ_U` and `|∇²h_C| ≤ M` on `Û` (`paper:918`, `:881`). Lean requires harmonicity and the Hessian bound only on `V[U]` cells, which is all the proof uses. This matches "stronger" in the README, but the header does not say so.
  - NOTE 2: the header of `harmonic_column_bound_complete` says "half the printed one, so the threshold is half the printed one (stronger)". That is relative to the printed directed sums. The corrected paper already counts undirected edges once (`paper:567–568`), so the registered threshold equals the corrected one. Suggest rewording.
  - NOTE 3: `[Fintype (T.closedVertices U)]` is an extra hypothesis. In the paper's setting (bounded `U`, closure inside the domain, locally finite, complete active cells) it holds automatically.

## SpherePackings.Support.Section3.InternalTaylor
- `surfaceTaylorRemainder_abs_le_cells` (line 44): `|h(w) − h(v) − ∇h(v)(w−v)| ≤ (M/2)(diam P_v + diam P_w)² ≤ 2Mδ²` via the broken segment through a contact point. Checked by hand: `|z−v| ≤ diam P_v` and `|w−z| ≤ diam P_w`.
- `energy_boundaryCorrected_le_internal` (line 183): energy `≤ 9M²δ²·incidentMass`, Taylor on internal edges only. Consistent with README item 5.
- `abs_le_of_abs_laplacian_le` (line 437): comparison principle. Checked by hand: `ψ = φ + cq` is subharmonic on `Q`, and `c·q(v) ≥ 0` is exactly what gives `|φ(v)| ≤ η`.

## SpherePackings.Support.Section3.DecayInternal
- `generaldim_decay_rate_internal` (line 240): matches corrected `theorem:generaldim-decay` (`paper:1464–1486`): `M = M_U°∨1` (`hM : 1 ≤ M`), Hessian bound on `V̄[U]` cells, Taylor on internal edges only, `ε < (CM)⁻¹` as `12Mε ≤ 1`, `ε ≤ 1/2`. Decay hypothesis in leobon12's form: `vol_d(Q_e) = ‖e‖vol_{d−1}(H_e)/d` (heights of the two pyramids sum to `‖e‖` for orthogonal tilings), so the paper's `F` corresponds to Lean's `F` times `d^α`, as the docstring says.
- `hypIIIRateConstant` (`Support/Section3/DecayRateArith.lean:21`): the only divisions are by `log 2` and `log(1/r)`, with `r = (1/2)^α ∈ (0,1)`, so no junk value is reached.
- `dirichlet_error_le_hypIIICost_internal` (line 205): hypotheses consistent with the above.

## SpherePackings.Support.Voronoi.GeometricConstraint
- `geometric_constraint_inner_collar` (line 191), `geometric_constraint_inner_cube` (line 129), `geometric_constraint_inner` (line 87): match corrected Lemma 5.1(a) (`paper:1742–1748`). The conclusion `closedBall s r ⊆ cell S s` is stronger than the paper's `B_r(s)`.
- `geometric_constraint_outer` (line 255): quantifier order correct (`δ, R` depend only on `d`), `R ≥ 2`, arbitrary `U, S`, matching corrected Lemma 5.1(b).
  - NOTE: `cthickening (R * k) U` is closed; the paper's `B_{Rk}(U)` may be open. This is harmless because `R` is existential: with `R' < R` the closed thickening of `R'` lies in the open one of `R`.
- The printed-radius counterexample (frozen header) rechecked by hand: with `k = 1`, grid points `z ∈ ℤ^d ∩ B_2(U)` have `z₁ ≤ 0`, because `z₁ = 1` forces `|s − z|² ≥ 1.01² + (d−1)/4 > 2.001²` exactly when `d ≥ 13`.
- Cell and cube definitions (`Voronoi/Basic.lean:17,22,26`): `cell` is the closed Voronoi cell `{y | ∀ s' ∈ S, dist s y ≤ dist s' y}`, `grid r = rℤ^d`, `cube` the closed sup-ball. Correct.

## SpherePackings.Support.Voronoi.CountsToCells
- `cell_between_balls_of_counts` (line 22): hypothesis `hE` with `min δ (1/4) k` yields the Lemma 5.1(b) hypothesis `hδ5` since `min δ (1/4) k ≤ δ k`. The conclusion `closedBall s r ⊆ cell S s ∧ cell S s ⊆ ball s (4k√d)` matches the docstring.

## SpherePackings.Support.Voronoi.PoissonLocal
- `IsPoissonPointProcess.restrict_inter` (line 31): `Λ ∩ W` is a Poisson process with intensity `ν.restrict W`. The four clauses check out.
- `voronoi_cells_between_balls_local` (line 359): matches corrected Prop 1.1 first part (`paper:388–399`): `hΛ` on `W`, `closure U ⊆ W`, `HolderMassBounds μ W` (`PoissonCells.lean:36`).
- `voronoi_tilings_hypotheses_local` (line 373), `voronoi_tilings_theoremAB_local` (line 575):
  - NOTE: `hlf` (`∀ m ω B`, bounded `B`: `(Λ m ω ∩ B).Finite`) is an extra hypothesis, sure rather than almost sure. CORRESPONDENCE explains that this is equivalent since the conclusion is almost sure (modify on a null set).
  - `IsDomain U` (open, nonempty, connected) is the repo's reading of the paper's "bounded domain" (`LipschitzDomain.lean:33–35`).

## SpherePackings.Frozen.Lemma22AffineKernel
- `lemma22_affine_kernel` (line 18): matches corrected Lemma 2.2 (`paper:705–708`): hypothesis `CompleteCell T v`, conclusion `discreteLaplacian (affine) v hv.1 = 0`. Nonvacuity instance compiled (below).

## SpherePackings.Frozen.Lemma25DualCoverage
- `lemma25_dual_coverage` (line 19): matches corrected Lemma 2.5 (`paper:824–829`) with the completeness hypothesis, and the `V[U]` convention note of `dual_coverage_complete` applies.
  - NOTE: the compiled `.olean` (10:59) predates the source edit (11:56), so the built statement is stale. The current source elaborates (`lake env lean` on the file: exit 0, no messages). Not a statement issue.

## SpherePackings.Frozen.Lemma31Poincare
- `lemma31_poincare` (line 23): matches corrected Lemma 3.1 (`paper:1036–1044`) in the threshold `k·√(E·M) = k(D·Σ d vol)^{1/2}` (both undirected).
  - NOTE: `π_j(U)` is dropped (the bound covers all of the projected cells, so stronger); the column set is the projected-cell set (see `Complete.Columns`); direction `e ≠ 0` is general; the zero condition `hzero` on `R ∖ A` coincides with the paper's `∂V[U]` when `R = closure V[U]`.

## SpherePackings.Frozen.Prop26Energy
- `prop26_energy` (line 25): matches corrected Prop 2.6 (`paper:916–938`) for the energy inequality with constant `9`.
  - NOTE: `h_C` harmonic and `|∇²h_C| ≤ M` are required only on `V[U]` cells (corrected: `Ĝ_U`, `paper:918`, `:881`), so the registered statement is sharper. The header states the `V[U]` requirement but not that it is a strengthening. `[Fintype (closedVertices U)]` is extra (see EnergyComplete note 3).

## SpherePackings.Frozen.Prop32Columns
- `prop32_columns` (line 25): as `prop26_energy`, plus the column-set and `π_j(U)` points from `Complete.Columns`. The threshold `3kMε·incidentMass` equals corrected Prop 3.2's threshold because the corrected paper counts undirected edges once (see EnergyComplete note 2).

## SpherePackings.Frozen.Theorem37Rate
- `theorem37_rate` (line 31): matches corrected `theorem:generaldim-decay` (`paper:1464–1486`). The conclusion is `hypIIIRateConstant(...) · 3M · ε · log(1/ε)`, which is the paper's `C M ε log(1/ε)` with `C = C(R₀, d, F, α)`.
  - NOTE: `12Mε ≤ 1` and `ε ≤ 1/2` are implied by the paper's `ε < (CM)⁻¹` with `C = 12` (since `M ≥ 1`), so the Lean hypotheses are no stronger than the paper's. `[Fintype (closedVertices U)]` is extra (EnergyComplete note 3). The header's comparison with the printed `M = sup_Û |∇²h_C| ∨ 1` is accurate. The corrected `theorem:generaldim` (with `L`, `D`, `K`, `paper:1366–1395`) is a different theorem, not in this batch.
  - G4 (`GAP-CHECKS.md`) not re-verified.

## SpherePackings.Frozen.Lemma51Outer
- `lemma51b_outer` (line 21): matches corrected Lemma 5.1(b) (`paper:1742–1756`): `δ = δ(d) ∈ (0,1)`, `R = R(d) ≥ 2`, universally quantified `U, S, k > 0`. `grid`, `cube`, `cell` as in `Voronoi/Basic.lean`.
  - Printed-radius counterexample verified (holds for `d ≥ 13`, see GeometricConstraint). The closed-thickening point is absorbed by `∃ R`.
  - Nonvacuity instance compiled (below).

## SpherePackings.Frozen.Prop11Cells
- `prop11_cells` (line 24): matches corrected Prop 1.1 first part (`paper:388–399`): `ball s (m^{−8/βm}) ⊆ cell ⊆ ball s (m^{−1/(3βp)})`, `βp = β⁺`, `βm = β⁻`. The mass bounds are on open `W ⊇ closure U`, the Poisson hypothesis on `Λ_m ∩ W` only, `U` only bounded (weaker assumption than the paper's bounded domain).
  - Junk: `Set.ncard` of an infinite set is `0` (`IsPoissonPointProcess`, `Support/Poisson/Basic.lean:26`), but only on a null event, so `HasLaw` is unaffected. `(m : ℝ)^(…)` at `m = 0` is irrelevant under `∀ᶠ m`.
  - Not exhibited: no Poisson process is constructed in the repo, so `hΛ` is not shown satisfiable. It is not contradictory: `HolderMassBounds` forces the intensity to be atomless on `W`, which is necessary (Batch21's Dirac check excludes atoms).

## SpherePackings.Frozen.Prop11TheoremAB
- `prop11_theoremAB` (line 20): Theorems B(a) (`HarmonicNearClosure`), B(b) (gated by `IsLipschitzDomain`, `IsHarmonicOn`, `ContinuousOnClosure`), and A (gated by `IsLipschitzDomain`, uniform in `z ∈ U`) match corrected Theorems A/B (`paper:263–290`, `:306–320`). `HasAmbientCollar U G.domain` is `closure U ⊆ interior D` (`PaperObjects.lean:21`).
  - NOTE 1: `hlf` is extra (see PoissonLocal).
  - NOTE 2: `IsDomain U` keeps connectedness in the "in particular" clause. The Prop 1.1 header's "U need not be connected" holds only for the first part (`Prop11Cells`); suggest saying so here.
  - NOTE 3: the ambient `D` (`G.domain`) is existential with only `closure U ⊆ interior D`. The paper takes a fixed bounded neighbourhood with `closure D ⊂ W` (`paper:398–399`). The Lean statement does not record that locality. The conclusions depend only on cells near `U` (`closedVertices U`; walk stopped on exit), and CORRESPONDENCE says the proof uses `D = thickening ρ U`, so this is a wording gap, not a vacuity.
  - Nonvacuity of the Poisson bundle not compiled (see Prop11Cells).

## Nonvacuity examples
Now `SpherePackings/Audit/Nonvacuity/Batch22.lean`. Compiled from the repository root with `lake env lean Nonvacuity.lean`. Exit 0, no messages; `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound` for the three main declarations (no `sorry`).

```lean
import SpherePackings.Support.Guards.LatticeVoronoi
import SpherePackings.Support.Voronoi.TilingProps
import SpherePackings.Support.Complete.Basic
import SpherePackings.Frozen.Lemma22AffineKernel
import SpherePackings.Frozen.Lemma51Outer

/-! Nonvacuity examples for audit batch 22.

* `GT_complete`: every active cell of the Voronoi tiling of `(1/10) ℤ²` over the unit ball is
  complete (`CompleteCell`, via `CompleteCell.of_subset_interior`).
* the frozen Lemmas 2.2 and 2.5 apply to `GT` with that hypothesis.
* `lemma51b_fine_lattice_nonvacuous`: the hypothesis of Lemma 5.1(b) holds for the fine lattice
  `δ ℤ²` (with the witnesses `δ`, `R` of the frozen lemma), so the conclusion applies to it. -/

open MeasureTheory Metric Set BouRabeeGwynne BouRabeeGwynne.OrthogonalTiling
open SpherePackings SpherePackings.Voronoi

namespace AuditBatch22

/-- The Voronoi tiling of `(1/10) ℤ²` on the open ball of radius `2`. -/
noncomputable def GT : OrthogonalTiling 2 :=
  voronoiTiling (grid (1 / 10 : ℝ)) (ball (0 : Euc 2) 2)
    (goodVoronoi_grid (by norm_num) (by norm_num) isBounded_ball)

lemma GT_domain : GT.domain = ball (0 : Euc 2) 2 := voronoiTiling_domain _ _ _

lemma GT_mesh_le : GT.mesh ≤ ENNReal.ofReal (1 / 2) := by
  refine (voronoiTiling_mesh_le _).trans (ENNReal.ofReal_le_ofReal ?_)
  have hs : Real.sqrt ((2 : ℕ) : ℝ) ≤ 3 / 2 := by
    have := Real.sqrt_le_sqrt (show ((2 : ℕ) : ℝ) ≤ (3 / 2) ^ 2 by norm_num)
    rwa [Real.sqrt_sq (by norm_num)] at this
  linarith

lemma GT_diam_le (v : GT.V) : Metric.diam (GT.cell v).carrier ≤ 1 / 2 := by
  have hne : GT.mesh ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top GT_mesh_le
  have h1 : ENNReal.ofReal (Metric.diam (GT.cell v).carrier) ≤ GT.mesh :=
    le_iSup (fun w : GT.V => ENNReal.ofReal (Metric.diam (GT.cell w).carrier)) v
  exact ((ENNReal.ofReal_le_iff_le_toReal hne).mp h1).trans
    (ENNReal.toReal_le_of_le_ofReal (by norm_num) GT_mesh_le)

lemma GT_cell_sub (v : GT.V) (hv : GT.pos v ∈ ball (0 : Euc 2) 1) :
    (GT.cell v).carrier ⊆ ball (0 : Euc 2) 2 := by
  intro x hx
  have h1 : dist x (GT.pos v) ≤ 1 / 2 :=
    (Metric.dist_le_diam_of_mem (GT.cell v).compact.isBounded hx
      (interior_subset (GT.pos_mem_interior v))).trans (GT_diam_le v)
  have h2 := dist_triangle x (GT.pos v) 0
  rw [dist_zero_right, dist_zero_right] at h2
  rw [mem_ball_zero_iff] at hv ⊢
  linarith

lemma GT_cell_interior (v : GT.V) (hv : GT.pos v ∈ ball (0 : Euc 2) 1) :
    (GT.cell v).carrier ⊆ interior GT.domain := by
  rw [GT_domain, isOpen_ball.interior_eq]
  exact GT_cell_sub v hv

/-- Nonvacuity of the completeness hypothesis of Lemmas 2.2, 2.5, 3.1, Propositions 2.6, 3.2 and
Theorem 3.7: every active cell of `GT` over the unit ball is complete. -/
theorem GT_complete : ∀ v ∈ GT.interiorVertices (ball (0 : Euc 2) 1), CompleteCell GT v :=
  fun v hv => CompleteCell.of_subset_interior (by norm_num) (GT_cell_interior v hv)

/-- Lemma 2.2 (frozen) applied to `GT`: affine functions are harmonic at each complete vertex. -/
example (v : GT.V) (hv : v ∈ GT.interiorVertices (ball (0 : Euc 2) 1)) (p : Euc 2) (c : ℝ) :
    GT.discreteLaplacian (fun w => inner ℝ p (GT.pos w) + c) v (GT_complete v hv).1 = 0 :=
  SpherePackings.Frozen.lemma22_affine_kernel (by norm_num) GT v (GT_complete v hv) p c

/-- Lemma 2.5 (the statement of `Frozen/Lemma25DualCoverage.lean` is proved by this theorem) applied
to `GT`, with the completeness hypothesis discharged. -/
example := SpherePackings.dual_coverage_complete (by norm_num) GT (ball (0 : Euc 2) 1) GT_complete

/-- The hypothesis of Lemma 5.1(b) for the fine lattice `δ ℤ²` and `k = 1`, `U` the unit ball:
every grid point `y ∈ ℤ ∩ R-thickening` has a point of `δ ℤ²` in its cube of half-side `δ`. -/
lemma lattice_hyp {δ R : ℝ} (hδ : 0 < δ) :
    ∀ y ∈ grid (1 : ℝ) ∩ cthickening (R * 1) (ball (0 : Euc 2) 1),
      (grid (δ * 1) ∩ cube y (δ * 1) : Set (Euc 2)).Nonempty := by
  intro y _
  obtain ⟨g, hg, hgy⟩ := exists_grid_near (mul_pos hδ one_pos) y
  refine ⟨g, ⟨hg, fun j => ?_⟩⟩
  have := hgy j
  linarith

/-- Nonvacuity of Lemma 5.1(b): the witnesses `δ`, `R` of the frozen lemma admit the fine lattice
`S = δ ℤ²` as a hypothesis-satisfying set, and the conclusion applies to it. -/
theorem lemma51b_fine_lattice_nonvacuous :
    ∃ δ R : ℝ, 0 < δ ∧ δ < 1 ∧ 2 ≤ R ∧
      ∃ S : Set (Euc 2),
        (∀ y ∈ grid (1 : ℝ) ∩ cthickening (R * 1) (ball (0 : Euc 2) 1),
          (S ∩ cube y (δ * 1)).Nonempty) ∧
        ∀ s ∈ S ∩ ball (0 : Euc 2) 1, cell S s ⊆ ball s (4 * 1 * Real.sqrt ((2 : ℕ) : ℝ)) := by
  obtain ⟨δ, R, hδ0, hδ1, hR, hmain⟩ := SpherePackings.Frozen.lemma51b_outer (d := 2) (by norm_num)
  exact ⟨δ, R, hδ0, hδ1, hR, grid (δ * 1), lattice_hyp hδ0,
    hmain (ball (0 : Euc 2) 1) (grid (δ * 1)) 1 one_pos (lattice_hyp hδ0)⟩

end AuditBatch22

#print axioms AuditBatch22.GT_complete
#print axioms AuditBatch22.lemma51b_fine_lattice_nonvacuous
#print axioms AuditBatch22.lattice_hyp
```

Output (the compile printed only the `#print axioms` lines):
```
'AuditBatch22.GT_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'AuditBatch22.lemma51b_fine_lattice_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound]
'AuditBatch22.lattice_hyp' depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT=0
```

What the examples show:
- **Completeness is satisfiable in a real tiling.** `GT` is the Voronoi tiling of `(1/10)ℤ²` over the ball of radius 2 (the construction Batch20 used). Every active cell over the unit ball is `CompleteCell` (`GT_complete`), so the completeness hypothesis of Lemmas 2.2/2.5/3.1, Props 2.6/3.2 and Theorem 3.7 holds in a concrete two-dimensional instance. The proof goes through `CompleteCell.of_subset_interior`, so this instance does not exhibit a complete cell that touches `∂D`. That case (README item 1) is not covered by these examples.
- **Lemmas 2.2 and 2.5 apply to `GT`.** The Lemma 2.2 instance gives discrete harmonicity of affine functions at each complete vertex of `GT`. The Lemma 2.5 instance is `dual_coverage_complete`, which the frozen Lemma 2.5 is defined to be. I used the Basic declaration because the stale `.olean` of `Frozen/Lemma25DualCoverage` carries an older hypothesis; the current source elaborates (checked), so this is only a workaround.
- **Lemma 5.1(b) is non-vacuous.** The witnesses `δ`, `R` from the frozen lemma admit the fine lattice `S = δℤ²` at `k = 1`: every grid point in the `R`-thickening of the unit ball has a point of `S` in its cube of half-side `δ`, so the conclusion applies (`lemma51b_fine_lattice_nonvacuous`).

Not compiled:
- A nonvacuity example for `Prop11Cells`/`Prop11TheoremAB` (Poisson hypotheses). The repo constructs no Poisson point process, so the bundle `hΛ` is not shown satisfiable. It is not contradictory: `HolderMassBounds` makes the intensity atomless on `W`, which is necessary.
- Props 2.6/3.2 with an explicit affine `h_C` and a discrete Dirichlet solution. Time budget spent; the `Fintype` and Dirichlet-solution hypotheses were not discharged.

## Not verified in this audit
- Counterexamples G1–G4 in `GAP-CHECKS.md` (slit domain, whole-ray claim, Theorem 3.7 grid example) are only cited by the headers; I did not re-derive them. The printed-radius counterexample for Lemma 5.1(b) and the energy and Lemma 2.2 counterexamples in the headers were checked by hand.
- Proofs were not reviewed (by design). Long Section 3 and Fibers/GaussGreen/Columns statements were read at signature and docstring level.
