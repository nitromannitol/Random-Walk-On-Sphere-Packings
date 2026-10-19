# Audit batch 19
| Module | Verdict | Summary |
|---|---|---|
| SpherePackings.Support.Section2.AffineKernel | OK | Lemma 2.2 as corrected (cells in the interior of `D`); the discrete Laplacian is the paper's `Δ_a`. |
| SpherePackings.Support.Section2.DualCoverage | NOTE | Upper inclusion of Lemma 2.5 matches; the printed lower inclusion is false and replaced by a disclosed coverage of cells of `V[U]`. |
| SpherePackings.Support.Section2.DualVariational | OK | `IsIncidentEdge` is `E[Ā]`; Lemma 2.3 matches (`f = 0` off `A` is WLOG). |
| SpherePackings.Support.Section3.ComponentArith | OK | Pure real arithmetic for the component case analysis; no junk values, hypotheses satisfiable. |
| SpherePackings.Support.Section3.ComponentChain | OK | `adjGraphIn` is facet adjacency inside `S`; the chain bound is an upper bound by the list sum of diameters. |
| SpherePackings.Support.Section3.ComponentLaplacian | OK | `Δ|·−z|²` and the Taylor bound for `C²` functions on edge segments; neighbours of `V[U]` lie in `V̄[U]`, so the restricted network is faithful. |
| SpherePackings.Support.Section3.DecayRateArith | OK | `hypIIIRateConstant` is junk-free for `0 < r < 1`; `1 ≤ M` is the paper's `M := sup|∇²h_C| ∨ 1` (tex 1328). |
| SpherePackings.Support.Section3.DecaySegment | NOTE | `hypIIICost` is a `tsum` (0 if not summable); summability follows from the hypotheses, so the statements are meaningful. |
| SpherePackings.Support.Section3.EnergyMinimal | NOTE | Corrected Proposition 2.6 and Proposition 3.2 match the paper; sums use one consistent undirected convention, and the Prop 3.2 threshold is at least as strong as printed. |
| SpherePackings.Support.Section3.GeneralDecayRate | OK | Theorem 3.7 with rate matches the paper; `M ≥ 1` is the paper's `∨ 1`; decay hypothesis is the paper's up to the `d^α` rescaling of `F` (documented). |
| SpherePackings.Support.Section3.GeneralRateFull | OK | Theorem 3.6 matches the paper (`M ≥ 1`, `K ≥ 1`, `D` as sup over connected sets of small cells); smallness is an explicit `C`. |
| SpherePackings.Support.Section3.PlanarCuts | ISSUE | Docstring says "Y meets the line in measure ≤ ℓ", but the hypothesis is `μHE[1] Y ≤ ℓ` on the whole set `Y`; strictly stronger, no effect on the use site. |
| SpherePackings.Support.Section3.PlanarRateFull | ISSUE | Theorem 3.3 carries the extra vertex-Lipschitz hypothesis `hLip`, which the printed `L = sup|∇h_C|` does not imply; this is open and disclosed (frozen statement, README PARTIAL). |

## SpherePackings.Support.Section2.AffineKernel
- `discreteLaplacian_affine_eq_zero` (line 51): matches Lemma 2.2 as corrected (`rw-spheres.tex:657-678`; README correction 4). `T.discreteLaplacian` is `Σ_w cond(v,w)(f w − f v)` (`BouRabeeGwynne/DiscretePDE.lean:76-78`), the paper's `Δ_a` (tex 290-291). The hypothesis `hvD` (cell inside `interior T.domain`) is the disclosed correction; the lattice tiling of the nonvacuity file satisfies the analogous containment for `V[U]`.
- `fderiv_affine` (18), `isHarmonicOn_affine` (23), `surfaceFlux_affine` (37): private helpers, no definitions.

## SpherePackings.Support.Section2.DualCoverage
- `dual_coverage` (line 21): the upper inclusion `⋃_{v∈V[U]}⋃_{w∈N(v)} Q_{vw} ⊆ ⋃_{v∈V̄[U]} cell v` matches tex 770-773 with `E[Ū]` read as edges with an endpoint in `V[U]` (tex 556-557) and `Ĝ_U` (tex 569-572). `dualPolytope = cellPyramid v w ∪ cellPyramid w v` (`BouRabeeGwynne/DualCells.lean:52-53`) equals the paper's `Q_e := conv(w, P_w∩P_v) ∪ conv(v, P_w∩P_v)` (tex 728).
- NOTE: the printed lower inclusion `U ⊆ ⋃_{e∈E[Ū]} Q_e` (tex 773) is false (a small ball inside one grid square contains no vertex, so the union is empty). The Lean lower inclusion is a different statement: the cells of `V[U]` are covered by apexes and pyramids over all touching cells, including lower-dimensional contacts. Disclosed in the docstring and README correction 4; it is not a weakening of anything true.

## SpherePackings.Support.Section2.DualVariational
- `IsIncidentEdge` (line 18): `0 < N.a w v ∧ (w ∈ A ∨ v ∈ A)` is the paper's `E[Ā]` (tex 557) restricted to positive conductance. Means what it says.
- `sum_incident_eq` (24), `weightedGradient_eq_zero_of_not_incident` (33): private helpers.
- `dual_variational_principle_incident` (line 47): matches Lemma 2.3 (tex 684-690). The Lean asks `f = 0` on all of `V \ A`, the paper on `∂A`; the two are equivalent because the sums over `E[Ā]` never see values off `Ā`. Divisions by `N.a w v` are guarded by the indicator, so there is no junk. OK.

## SpherePackings.Support.Section3.ComponentArith
- `component_case_bound` (line 14): arithmetic lemma. The conclusion `x ≤ Dc·L + 4(R+1)/log 2 · M K ε log(1/ε)` is the two-case bound the module header ties to tex 1236-1240 (that correspondence was not re-checked here). Hypotheses are satisfiable (for example `x = 0`, `ε = 1/4`, `K = 1`). `log(1/ε)` is only used with `0 < ε ≤ 1/2`. OK.

## SpherePackings.Support.Section3.ComponentChain
- `adjGraphIn` (line 21): the induced facet-adjacency graph on `S`, with `symm` and `loopless` proved from `T.adj`. Means what it says.
- `chain_dist_le` (line 28): along a walk, `dist(φx, φy) ≤ L · Σ_{u ∈ support} diam(cell u)`. The support may repeat vertices, which only makes the bound weaker, so this is still correct. OK.

## SpherePackings.Support.Section3.ComponentLaplacian
- `norm_sq_sub_sq_eq` (22), `sum_inner_eq_zero` (29), `sum_clm_eq_zero` (45), `taylor_segment_bound` (57): private helpers. `taylor_segment_bound` takes `‖D²h‖ ≤ M` (operator norm on the segment) and gives `M|b−a|²`, a weaker constant than `M/2` in tex 884, which is harmless.
- `laplacian_sq_dist` (line 91): `Δ|·−z|²(u) = Σ_w a(u,w)|w−u|²` via Lemma 2.2 on the closed network. Matches the paper's argument for the `|·−z|²` term. OK.
- `abs_laplacian_le` (line 116): `|Δh(u)| ≤ M Σ_w a(u,w)|w−u|²`, under the Hessian bound on the edge segments incident to `u`, which is the corrected hypothesis. OK.

## SpherePackings.Support.Section3.DecayRateArith
- `hypIIIRateConstant` (line 19): closed form. Denominators `log(1/r)`, `1−r`, `1−√r`, `1−r²` are positive for `0 < r < 1`, and `log(max J 1) ≥ 0`, so there is no junk. OK.
- `hsmall`-type arithmetic helpers (24, 45): private.
- `hypIIICost_le_rate` (line 82): hypotheses include `1 ≤ M`, which is the paper's `M := sup|∇²h_C| ∨ 1` (tex 1328 for Theorem 3.7; tex 1161 for Theorem 3.6). The statement is consistent: `δ ≡ 0`, `J = 0`, `A = 0`, `M = 1`, `ε = 1/4`, `r = 1/2` satisfies every hypothesis. OK.

## SpherePackings.Support.Section3.DecaySegment
- `surfaceTaylorRemainder_abs_le_segment` (28), `correctedSurfaceField_bound_at_interior_segment` (68), `correctedSurfaceField_bound_segment` (109), `energy_boundaryCorrected_le_hessian_diam_mass_segment` (132), `boundaryCorrected_trimmed_mass_le_half_segment` (234), `correctedRegions_mass_le_geometric_segment` (269): internal steps of leobon12's corrected iteration, with the Hessian bound on cells and edge segments. Hypotheses are consistent with those of `EnergyMinimal` (line 196-211).
- `dirichlet_error_le_hypIIICost_of_mass_decay_segment` (328) and `dirichlet_error_le_hypIIICost_segment` (401): the RHS is `hypIIICost K (3M) ε δ`, which is `2Mε² + ∑' i, (…)` (`BouRabeeGwynne/HypIIICostSeries.lean:25-26`). NOTE: `tsum` is 0 when the series is not summable. In these statements summability follows from the geometric mass decay (`regionDiameter_le_geometric_of_mass`, then `hypIIICost_summable`), so the junk value cannot be reached. The statements need only `0 < K`, `0 < M`, `0 < ε`, not `1 ≤ M`, which is correct for a cost bound.

## SpherePackings.Support.Section3.EnergyMinimal
- `fluxResidual_bound_segment` (28), `dist_le_of_mem_cell` (74), `surfaceFlux_residual_bound_segment` (81), `energy_error_le_hessian_segment` (145): internal steps of the corrected Proposition 2.6 (Hessian bound on the cell of `w` and the edge segment).
- `harmonic_energy_bound_segment` (line 196): corrected Proposition 2.6 (tex 822-844; README correction 11). The hypotheses are the corrected ones: cells of `V[U]` in `interior D` (line 198), `h_C` harmonic near `V̄[U]` (lines 199-200), `C²` and `Hessian ≤ M` on the segments of edges with an endpoint in `V[U]` (lines 202-211). The constant `9M²ε²` matches tex 842. NOTE on conventions: `incidentEnergy` and `incidentMass` are both sums over undirected edges (`BouRabeeGwynne/Section3EnergyNormalization.lean:48-50`, `Section3ColumnEstimate.lean:15-22`), whereas the paper's `Σ_{E[Ū]}` counts both orientations (tex 556-558 says `E` contains both). Both sides of each inequality use the same convention, so the constant `9M²ε²` is unaffected. Nonvacuity compiled (see below).
- `harmonic_column_bound_segment` (line 232): Proposition 3.2 under the corrected hypotheses (tex 982-999). The threshold `3kMε·incidentMass` is half the printed threshold if the printed sum is over directed edges, so the Lean statement is at least as strong; no weakening. Consistent with Lemma 3.1's undirected proof (`column_poincare_measure_bound`, `Section3ColumnEstimate.lean:84-92`).

## SpherePackings.Support.Section3.GeneralDecayRate
- `generaldim_decay_rate` (line 39): Theorem 3.7 with its rate (tex 1314-1340). Faithful:
  - `hM : 1 ≤ M` (line 49) is the paper's `M := sup|∇²h_C| ∨ 1` (tex 1328).
  - `hreg` (line 57) uses `incidentScale α v = sup_w (‖e‖ vol_{d−1}(H_e))^α`. By Lemma 2.4 (tex 742), `‖e‖ vol_{d−1}(H_e) = d vol_d(Q_e)`, so the Lean `F` equals the paper's `F·d^{-α}`. The module header documents this.
  - `hα : 0 < α` and `hF : F ≠ ⊤` (line 56) are the paper's `F, α > 0`.
  - `hε2 : ε ≤ 1/2` (line 58) is redundant given `hsmall : 12Mε ≤ 1` (line 58) and `hM : 1 ≤ M`.
  - `hsmall : 12Mε ≤ 1` is a fixed explicit smallness condition in place of the paper's `ε < (CM)⁻¹` with `C = C(U,F,α)`. An explicit constant is a special case of an existential one, so this is no weakening.
  - `R₀` (line 42) bounds `‖x‖` on `U`, and the rate's constant depends only on `d, R₀, F, α`, as the paper's `C(U,F,α)` requires.

## SpherePackings.Support.Section3.GeneralRateFull
- `exp_neg_mul_log_inv_full` (40), `rate_factor_le_full` (47), `lipschitz_on_convex` (81), `list_sum_le_finset_sum` (92): private helpers.
- `cell_norm_le_of_closedVertices` (line 53): `‖x‖ ≤ R₀ + 1` on cells of `V̄[U]` under the diameter bound `ε ≤ 1/2`. Proved for the stated hypotheses. OK.
- `generaldim_full` (line 100): Theorem 3.6 with its full bound (tex 1147-1176). Faithful:
  - `hM : 1 ≤ M` (line 110) is the paper's `∨ 1` (tex 1161).
  - `hK : 1 ≤ K` (line 110) is the paper's `K ≥ 1` (tex 1163).
  - `hLgrad` (line 117) is `L = sup` over the cells of `V̄[U]`, which cover `Ĝ_U` (tex 1161).
  - `hDc` (lines 118-121) bounds `Σ diam` over every finite connected `Q ⊆ 𝒜 = {vol < ε^K}` (tex 1167-1168). This is equivalent to the paper's `D = sup over components`, since each component is connected and each connected set lies in one component.
  - `hsmall : 3Mε < 1/2` and `hε2 : ε ≤ 1/2` (line 122) are explicit replacements for `ε < (CM)⁻¹` with `C = C(U)`. This is a special case of the paper's existential constant.
  - The hypothesis `hε2` is needed by `cell_norm_le_of_closedVertices`. Junk: `Real.log (max (2d·vol) 1)` is junk-free because of the `max`.

## SpherePackings.Support.Section3.PlanarCuts
- `exists_unitLine_cuts_around` (line 18): ISSUE. The docstring (lines 6-9) says the hypothesis is that `Y` "meets a unit line in a set of one-dimensional measure at most ℓ". The statement's hypothesis `hY : μHE[1] Y ≤ ENNReal.ofReal ℓ` (line 19) is measured on the whole set `Y ⊆ Euc d`. This is strictly stronger than the docstring. Concrete example: in the plane with `u = (1,0)`, `Y` = the closed disc of radius 1 centred at `(0,2)` (disjoint from the line `ℝ·u`), together with the origin, and `ℓ = 0`. Then `Y ∩ (ℝ·u) = {0}` has measure `0 ≤ ℓ`, which is the docstring's hypothesis, but `μHE[1] Y = ∞`, so the Lean hypothesis fails. The docstring's conclusion is still true for this `Y`, but the Lean lemma does not state it. Effect on the use site: `PlanarRateFull.lean:181` applies it to `columnBadSet`, which lies in `e^⊥`, i.e. on the line, so the two readings coincide there. Fix: put the hypothesis on `Y ∩ {t • u | t : ℝ}`, or correct the docstring.

## SpherePackings.Support.Section3.PlanarRateFull
- `planar_box_dist_le` (line 33): a box with sides `≤ s` has diameter `≤ √2 s` on the open slab intersection. OK.
- `error_le_of_good_box_local` (line 67): internal maximum-principle step. OK.
- `planar_dirichlet_rate_printed` (line 107): ISSUE. Theorem 3.3 (tex 1030-1054) with the printed constant `inf_k(6kMε vol(Ĝ_U) + 2(√2/k + ε)L)`. The hypothesis `hLip` (lines 123-124) is `|h_C(w) − h_C(v)| ≤ L·dist(w,v)` for all pairs of vertices of `V̄[U]`. The paper's `L = sup_{Ĝ_U}|∇h_C|` (tex 1044) does not imply `hLip`, because the segment `[v,w]` can leave `Ĝ_U`. This is an open gap, not a false statement: the frozen statement (`SpherePackings/Frozen/Theorem33Planar.lean`, lines 14-15) says "That hypothesis is not known to be needed, so the theorem is open"; the README records it as PARTIAL. The module header (lines 21-23) describes the printed proof's segment step, which is the step that fails, so it should not be read as validation. Nonvacuity compiled (below).
- `planar_dirichlet_rate_full` (line 244): ISSUE, for the same reason (`hLip` at lines 261-262). Its second conjunct `≤ (6M·vol(B_{R₀+1}) + 2(√2+1)L)·√ε` for `ε ≤ 1/2` (line 254) is the paper's `C(U,M,L) ε^{1/2}`. The `ε ≤ 1/2` restriction is harmless for an asymptotic statement and is recorded in the frozen statement.

## Nonvacuity examples
Compiled from the repository root with
`lake env lean Nonvacuity.lean`.
The output was exit code 0 and only the two `#print axioms` lines:

```
'Batch19Nonvacuity.nonvacuous_theorem33_printed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Batch19Nonvacuity.nonvacuous_prop26' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file, verbatim:

```lean
import SpherePackings.Support.Guards.LatticeTilings
import SpherePackings.Support.Section3.PlanarRateFull

/-!
Nonvacuity for the hypothesis bundle of Theorem 3.3 (`planar_dirichlet_rate_printed`), audit batch 19.

The tiling is the Voronoi tiling of `(1/10) ℤ²` on the ball of radius `2`, the construction of
`SpherePackings/Support/Guards/LatticeTilings.lean` at `n = 9`.  The continuum function is `h_C = 0`
(harmonic, with Hessian and gradient bounds `M = L = 0`), `ε = 1/2` bounds the cell diameters.
-/

open MeasureTheory Metric Set BouRabeeGwynne BouRabeeGwynne.OrthogonalTiling SpherePackings.Voronoi
open SpherePackings

namespace Batch19Nonvacuity

/-- The Voronoi tiling of `(1/10) ℤ²` on the ball of radius `2`. -/
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

lemma GT_closure_sub : closure (ball (0 : Euc 2) 1) ⊆ ball (0 : Euc 2) 2 :=
  closure_ball_subset_closedBall.trans (closedBall_subset_ball (by norm_num))

lemma GT_closed_finite : (GT.closedVertices (ball (0 : Euc 2) 1)).Finite :=
  GT.closedVertices_finite isBounded_ball (by rw [GT_domain]; exact GT_closure_sub)
    (fun v hv => by rw [GT_domain]; exact GT_cell_sub v hv)

noncomputable instance GT_fintype : Fintype (GT.closedVertices (ball (0 : Euc 2) 1)) :=
  @Fintype.ofFinite _ GT_closed_finite.to_subtype

lemma hess_zero (x : Euc 2) : ‖fderiv ℝ (fderiv ℝ (fun _ : Euc 2 => (0 : ℝ))) x‖ ≤ 0 := by
  have h0 : fderiv ℝ (fderiv ℝ (fun _ : Euc 2 => (0 : ℝ))) x = 0 := by simp
  rw [h0, ContinuousLinearMap.opNorm_zero]

lemma GT_boundary_access :
    (GT.finiteNetwork (GT.closedVertices (ball (0 : Euc 2) 1))).BoundaryAccessible
      (GT.finiteInterior (ball (0 : Euc 2) 1)) :=
  GT.finiteNetwork_boundaryAccessible_of_cell_interior (R := GT.closedVertices (ball (0 : Euc 2) 1))
    (A := GT.finiteInterior (ball (0 : Euc 2) 1)) (by norm_num)
    (coordinateAxis (0 : Fin 2)) (coordinateAxis_ne_zero 0)
    (fun w hw x hwx => GT.neighbor_mem_closedVertices hw hwx)
    (fun w hw => by
      rw [GT_domain, isOpen_ball.interior_eq]
      exact GT_cell_sub w.1 hw)

/-- Theorem 3.3 (printed constant) has satisfiable hypotheses on the lattice tiling: with `h_C = 0`,
`M = L = 0`, `ε = 1/2`, a Dirichlet solution exists and the conclusion is instantiated. -/
theorem nonvacuous_theorem33_printed :
    ∃ f : GT.V → ℝ,
      GT.SolvesDirichlet (ball (0 : Euc 2) 1) (fun v => (fun _ : Euc 2 => (0 : ℝ)) (GT.pos v)) f ∧
      ∀ k : ℝ, 0 < k → ∀ v ∈ GT.interiorVertices (ball (0 : Euc 2) 1),
        |f v - (fun _ : Euc 2 => (0 : ℝ)) (GT.pos v)| ≤
          6 * k * 0 * (1 / 2) *
              (MeasureTheory.volume (⋃ w ∈ GT.closedVertices (ball (0 : Euc 2) 1),
                (GT.cell w).carrier)).toReal +
            2 * (Real.sqrt 2 / k + 1 / 2) * 0 := by
  obtain ⟨f, hf⟩ := GT.exists_dirichlet (ball (0 : Euc 2) 1) GT_boundary_access
    (fun _ : GT.V => (0 : ℝ))
  refine ⟨f, hf, ?_⟩
  have hcellD : ∀ v ∈ GT.interiorVertices (ball (0 : Euc 2) 1),
      (GT.cell v).carrier ⊆ interior GT.domain := fun v hv => by
    rw [GT_domain, isOpen_ball.interior_eq]
    exact GT_cell_sub v hv
  have hh : IsHarmonicOn (fun _ : Euc 2 => (0 : ℝ)) univ :=
    ⟨contDiff_const.contDiffOn, fun x _ => by simp⟩
  exact planar_dirichlet_rate_printed GT (ball (0 : Euc 2) 1) hcellD isOpen_univ hh
    (fun _ _ => subset_univ _) isOpen_univ contDiff_const.contDiffOn
    (fun _ _ _ _ _ _ => subset_univ _) (M := 0) (L := 0) (ε := 1 / 2) le_rfl le_rfl (by norm_num)
    (fun v _ => GT_diam_le v) (fun _ _ x _ => hess_zero x)
    (fun _ _ _ _ _ _ x _ => hess_zero x)
    (fun _ _ _ _ => by simp) f hf

/-- The corrected Proposition 2.6 (`harmonic_energy_bound_segment`) has satisfiable hypotheses on the
same tiling, with `h_C = 0`, `M = 0`, `ε = 1/2`. -/
theorem nonvacuous_prop26 :
    ∃ f : GT.V → ℝ,
      GT.SolvesDirichlet (ball (0 : Euc 2) 1) (fun v => (fun _ : Euc 2 => (0 : ℝ)) (GT.pos v)) f ∧
      GT.incidentEnergy (GT.closedVertices (ball (0 : Euc 2) 1))
          (GT.finiteInterior (ball (0 : Euc 2) 1))
          (fun v => f v - (fun _ : Euc 2 => (0 : ℝ)) (GT.pos v)) ≤
        9 * 0 ^ 2 * (1 / 2) ^ 2 *
          GT.incidentMass (GT.closedVertices (ball (0 : Euc 2) 1))
            (GT.finiteInterior (ball (0 : Euc 2) 1)) := by
  obtain ⟨f, hf⟩ := GT.exists_dirichlet (ball (0 : Euc 2) 1) GT_boundary_access
    (fun _ : GT.V => (0 : ℝ))
  refine ⟨f, hf, ?_⟩
  have hcellD : ∀ v ∈ GT.interiorVertices (ball (0 : Euc 2) 1),
      (GT.cell v).carrier ⊆ interior GT.domain := fun v hv => by
    rw [GT_domain, isOpen_ball.interior_eq]
    exact GT_cell_sub v hv
  have hh : IsHarmonicOn (fun _ : Euc 2 => (0 : ℝ)) univ :=
    ⟨contDiff_const.contDiffOn, fun x _ => by simp⟩
  exact SpherePackings.harmonic_energy_bound_segment (by norm_num) GT (ball (0 : Euc 2) 1) hcellD
    isOpen_univ hh (fun _ _ => subset_univ _) isOpen_univ contDiff_const.contDiffOn
    (fun _ _ _ _ _ _ => subset_univ _) (M := 0) (ε := 1 / 2) le_rfl
    (fun v _ => GT_diam_le v) (fun _ _ x _ => hess_zero x)
    (fun _ _ _ _ _ _ x _ => hess_zero x) f hf

#print axioms nonvacuous_theorem33_printed
#print axioms nonvacuous_prop26

end Batch19Nonvacuity
```

What the examples show:
- `nonvacuous_theorem33_printed`: the hypothesis bundle of `planar_dirichlet_rate_printed` is jointly satisfiable on an explicit tiling. The tiling is the Voronoi tiling of `(1/10)ℤ²` on `B₂`, rebuilt from the guard's construction. Its vertices of `V[U]` for `U = B₁` have cells inside `B₂` (`GT_cell_sub`, from the diameter bound `1/2`), the closed vertex set is finite, a Dirichlet solution exists through the network API, and `h_C = 0` gives `M = L = 0`. The conclusion is instantiated, so nothing in the hypothesis list is contradictory. `h_C = 0` is the trivial case: it exercises the containment, finiteness and solvability hypotheses, but not the nontrivial Hessian or Lipschitz parts (`hLip` with `L > 0`).
- `nonvacuous_prop26`: the same for the corrected Proposition 2.6 (`harmonic_energy_bound_segment`), including the edge-segment hypotheses (`hsegs`, `hHseg`) and the Dirichlet solution.
- Not attempted within the time budget: nonvacuity for the Theorem 3.6 and 3.7 bundles (`generaldim_full`, `generaldim_decay_rate`), whose extra hypotheses `hDc` and `hsmall` would need the same construction with `M = 1`. I expect them to be satisfiable by the same route, but this is not verified. The smaller bundles (`component_case_bound`, `hypIIICost_le_rate`, `exists_unitLine_cuts_around`, `dual_variational_principle_incident`) are satisfiable by inspection of their numerical or finite hypotheses; I did not compile examples for them.
- `HessTest.lean` in the same directory is a scratch probe of the operator-norm zero lemma used in `hess_zero`; it is not a nonvacuity result.
