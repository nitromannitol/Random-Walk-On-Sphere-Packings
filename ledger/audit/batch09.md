# Audit batch 9
| Module | Verdict | Summary |
|---|---|---|
| BouRabeeGwynne.Section3HarmonicIteration | NOTE | Recursion trims with the newest replacement (region_{n+1} from value_n), not the printed one-step-lagged recursion h_{i+1}=H(S_i), S_{i+1}=trim(h_i); bounds are proved for the Lean recursion. |
| BouRabeeGwynne.Section3MassDecay | NOTE | Docstring says the contraction is "not supplied as a premise", but the energy bound `henergy` and `hfactor` are premises. |
| BouRabeeGwynne.RadialBoundary | OK | Ray-to-frontier witness; statement is what the docstring says, no junk values. |
| BouRabeeGwynne.DualCoverage | OK | Cone cover from interior apex; `cellPyramid`/`dualPolytope` match paper Q_e (rw-spheres.tex:728). |
| BouRabeeGwynne.CellVolumeBound | OK | vol(P_v) ≤ Σ dualVolume over all contacts and over adjacent contacts; nonadjacent contacts have zero dual volume. |
| BouRabeeGwynne.Section3CellMass | OK | Cell volume ≤ 2·incidentMass; `incidentMass` = Σ_e |F_e||e| = Σ_e d·vol_d(Q_e) (matches rw-spheres.tex:742). |
| BouRabeeGwynne.Section3GeometricCutoff | NOTE | `geometricVolumeCutoff` uses ⌈·⌉₊ (0 for negative arguments); every lemma assumes 0 ≤ q and 1 ≤ K, so harmless. |
| BouRabeeGwynne.Section3CaseII | NOTE | `hvolume` uses `minTileVolume.toReal`, which is 0 for an empty tiling, so the hypothesis is false there (harmless); the general lemma takes `henergy` as a premise, which its docstring calls "upstream energy estimate". |
| BouRabeeGwynne.Section3CaseIITarget | NOTE | Conclusion is the qualitative convergence under (II), no rate (documented PARTIAL in README); `RegularityII` uses `mesh.toReal`, which is junk when mesh = ⊤, harmless given `happrox`. |
| BouRabeeGwynne.BoundaryEdgeResponse | OK | Responses are the exit probabilities for p(x,y)=a(x,y)/Σ_z a(x,z); they sum to 1 on A. |
| BouRabeeGwynne.BoundaryTaylorCorrection | NOTE | `dualEnergy` (DualDirichlet.lean:14) has junk x²/0 = 0; harmless because the corrected flux vanishes where a = 0 and `hsupport` is assumed. |
| BouRabeeGwynne.FacetAffineResidual | OK | Gradient variation controlled on the source cell only, as the docstring says. |
| BouRabeeGwynne.LocalFacetResidual | OK | Residual 3Mδ·area uses only the two endpoint diameters, as the docstring says. |
| BouRabeeGwynne.CorrectedSurfaceField | OK | Corrected flux = residual + Taylor reward, with consistent antisymmetry and support. |
| BouRabeeGwynne.BoundaryCorrectedSurfaceEnergy | OK | Energy ≤ 9M²δ²·incidentMass, the form of rw-spheres.tex:842. |
| BouRabeeGwynne.BoundaryCorrectedIteration | OK | Telescoping of the corrected error; hypotheses consistent. |
| BouRabeeGwynne.HypIIICorrectedTrimming | OK | Threshold KMδ, cutoff √(εδ); `hwidth` and `hsmall` give contraction 1/2; `hlength` uses 2ε as the docstring says. |
| BouRabeeGwynne.RegionDiameter | OK | `regionDiameter` is the max of cell diameters over A (0 on ∅); no junk. |
| BouRabeeGwynne.HypIIICorrectedRegions | OK | Each step uses the current region's corrected Dirichlet error and its actual maximum diameter. |
| BouRabeeGwynne.HypIIIGeometricScale | OK | `incidentScale` = sup over incident edges of (|e|·|F|)^α, the max in hypothesis (III) (rw-spheres.tex:271). |
| BouRabeeGwynne.HypIIIRegionScale | OK | Needs 0 < α, matching `RegularityIII`; conclusion is eventual emptiness, as stated. |
| BouRabeeGwynne.HypIIITaylorCost | OK | Constant 6 is documented as sufficient, not sharp. |
| BouRabeeGwynne.HypIIICostSeries | NOTE | `hypIIICost` uses `tsum`, which is 0 when not summable; every use carries `hypIIICost_summable` hypotheses, so no junk is reached. |
| BouRabeeGwynne.HypIIICostBound | OK | Finite partial sums ≤ `hypIIICost A (3M)`; the 6M → 2·(3M) rewrite is correct. |
| BouRabeeGwynne.HypIIIErrorBound | OK | `_of_mass_decay` takes `hmass` as a premise (documented); the main theorem discharges it via `correctedRegions_mass_le_geometric`. |
| BouRabeeGwynne.Section3CaseIIITarget | OK | Statement is the Dirichlet convergence claim under (III); `RegularityIII` matches rw-spheres.tex:271 (item diam). No nonvacuity example compiled for (III). |

## BouRabeeGwynne.Section3HarmonicIteration
- `HarmonicIterationState.step` (line 36) and `harmonicIteration` (line 55): the new region is `trimmedErrorSet s.region (s.value - g)` and the new value is the Dirichlet solution on that new region. Paper (3.8), rw-spheres.tex:1203–1215, has h_{i+1} = H(S_i) with S_{i+1} = trim(N(h_i)). Matching indices gives Lean value_n = h_{n+1} but Lean region_{n+1} is trimmed with value_n = h_{n+1}, whereas the paper trims S_{n+1} with h_n. The Lean recursion is one step ahead of the printed one. The definition is consistent and documented as "as in (3.8)" only for the trimming formula (Section3Iteration.lean:35). NOTE: the proved bounds are for the Lean recursion, so the user should decide whether the printed indexing is wanted.
- `harmonicIteration_cumulative_cost` (line 67), `harmonicIteration_error_outside` (line 89): statements are what the docstrings say; no junk.

## BouRabeeGwynne.Section3MassDecay
- `harmonicIteration_mass_le_geometric` (line 24): docstring (lines 22–23) says "The geometric contraction is derived from the tiling, not supplied as a premise". The contraction factor 1/2 is derived, but the energy premise `henergy` (lines 34–36) and the numeric `hfactor` (line 37) are premises. The docstring should say so. Statement is otherwise faithful to Proposition 2.6 with the stated constants.
- `finiteAmbientFunction` (line 15): zero extension, correct.

## BouRabeeGwynne.RadialBoundary
- `exists_frontier_segment` (line 14): correct for any anchor a, including anchors outside the cell, as its docstring says.

## BouRabeeGwynne.DualCoverage
- `exists_mem_cellPyramid` (line 17), `cell_eq_insert_iUnion_cellPyramids` (line 29): exact equality with an explicit apex; matches the paper's Q_e decomposition (rw-spheres.tex:728).
- `cell_eq_insert_iUnion_contactFinset_pyramids` (line 48), `cell_subset_insert_iUnion_dualPolytopes` (line 55): restatements, correct.

## BouRabeeGwynne.CellVolumeBound
- `cell_measure_le_sum_dualVolume` (line 16): μHE[d] of the cell ≤ Σ dualVolume over contacts; `dualVolume` = μHE[d] of the full dual polytope (DualCells.lean:56). Correct.
- `cell_measure_le_sum_adjacent_dualVolume` (line 41): removing nonadjacent contacts is justified by `dualVolume_eq_zero_of_nonadjacent_contact`. Correct.

## BouRabeeGwynne.Section3CellMass
- `cellVolume_ne_top` (line 17), `minTileVolume_toReal_le_cellVolume` (line 24): fine.
- `cellVolume_le_twice_incidentMass` (line 71): the factor 2 matches the docstring.

## BouRabeeGwynne.Section3GeometricCutoff
- `geometricVolumeCutoff` (line 14): `⌈(q + log K)/log 2⌉₊ + 1`. Nat ceiling is 0 on negative arguments; the lemmas take `0 ≤ q` and `1 ≤ K`, so this is harmless.
- `geometric_mass_lt_exp_neg` (line 27): K·2^{−N} < exp(−q) for the stated N; the statement is correct.
- `harmonicIteration_empty_at_volume_cutoff` (line 59), `harmonicIteration_uniform_error_of_volume_decay` (line 78): `hupper` quantifies over all j, as intended. Satisfiable in the trivial regime A = ∅ (not compiled).

## BouRabeeGwynne.Section3CaseII
- `caseIIThresholdCoefficient` (line 17), `caseII_mesh_scaled_contraction` (line 25): `(2ε)²/(2ε)²` = 1 needs ε > 0, which is a hypothesis.
- `geometricVolumeCutoff_mul_mesh_tendsto_zero` (line 44): correct; uses only ε·q → 0.
- `dirichlet_error_le_volume_cutoff` (line 68): `hvolume` (line 84) uses `minTileVolume.toReal`. Junk only for an empty tiling, where the hypothesis is false. `henergy` (lines 79–81) is an input; the docstring (lines 64–67) describes it as "the upstream energy estimate", which is accurate but it is a premise here.
- `dirichlet_error_le_volume_cutoff_of_harmonic` (line 109): derives `henergy` from harmonicity and the Hessian bound; the conclusion is what the docstring says.

## BouRabeeGwynne.Section3CaseIITarget
- `exists_unit_euc` (line 16): correct.
- `theoremB_part_a_caseII` (line 27): conclusion is `DirichletApproximationTarget` (TheoremBStatement.lean:48): existence and uniqueness of the discrete extension eventually, and uniform error ≤ η for every solution eventually. This matches the convergence claim in the paper's Dirichlet theorem (rw-spheres.tex:297–318) under hypothesis (II). The rate of paper Theorem 3.6 is not claimed, which README "Open" documents.
- `RegularityII` (PaperObjects.lean:207): `(mesh.toReal) * q n → 0` with `minTileVolume.toReal ≥ exp(-q n)`. This matches "volume ≥ exp(−o(ε_n⁻¹))" (rw-spheres.tex:271). Junk: `mesh.toReal = 0` when mesh = ⊤; the Tendsto is over the tail, and `happrox` forces mesh → 0, so no effect.

## BouRabeeGwynne.BoundaryEdgeResponse
- `boundaryEdgeSource` (line 64), `boundaryEdgeResponse` (line 68): the response is the exit distribution for the walk with p = a/deg. Source −a(u,w) at u corresponds to (I−P)f(u) = p(u,w), so f(v) = E_v[visits u]·p(u,w) = P_v(exit through (u,w)).
- `sum_boundaryEdgeResponse` (line 120): total exit probability 1 on A. Correct.

## BouRabeeGwynne.BoundaryTaylorCorrection
- `boundaryCorrectionSource` (line 22), `boundaryCorrection` (line 25): the Poisson correction with source −Σ_{w∉A} a·R. Correct.
- `boundaryCorrection_abs_le` (line 72): |correction| ≤ C from `hR` on boundary edges only. Correct.
- `boundaryRewardField` (line 152): antisymmetric; the outward reward has the correct sign.
- `energy_boundaryCorrected_le_flux` (line 208): uses `dualEnergy` (DualDirichlet.lean:14), where x²/0 = 0. Harmless: `correctedIncidentFlux_support` (line 190) makes the flux vanish where a = 0, and `hsupport` is a hypothesis.

## BouRabeeGwynne.FacetAffineResidual
- `gradient_variation_on_cell` (line 22), `surfaceFlux_affine_residual_bound` (line 44): bound M·ε·area using only the source cell's diameter and Hessian; matches the docstring.

## BouRabeeGwynne.LocalFacetResidual
- `surfaceFlux_residual_bound_of_cell_diameters` (line 33): 3Mδ·area from the two endpoint cell diameters; matches the docstring.

## BouRabeeGwynne.CorrectedSurfaceField
- `surfaceTaylorRemainder` (line 16), `correctedSurfaceField` (line 34): corrected flux = surface residual + Taylor reward, consistent with `boundaryRewardField`. Bounds at interior and boundary edges (lines 50–101) are correct.

## BouRabeeGwynne.BoundaryCorrectedSurfaceEnergy
- `energy_boundaryCorrected_le_hessian_diam_mass` (line 23): energy ≤ 9M²δ²·incidentMass R A, the form of rw-spheres.tex:842. Hypotheses are the interior diameters and Hessian bounds only, as the docstring says.

## BouRabeeGwynne.BoundaryCorrectedIteration
- `boundaryCorrectedError` (line 21), `boundaryCorrectedError_step_identity` (line 42): nested telescoping with only new boundary edges contributing.
- `boundaryCorrectedIteration_error_bound` (line 108): error ≤ C₀ + Σ(q_i + C_i). Correct, with C₀ the initial reward and summation over the genuine steps.

## BouRabeeGwynne.HypIIICorrectedTrimming
- `correctedError_trimmed_mass_le_half` (line 18): hypotheses `hwidth` (line 28) and `hsmall` (line 29) imply the factor 1/4 + 1/4 ≤ 1/2 in the displayed computation. Correct.
- `boundaryCorrected_trimmed_mass_le_half` (line 70): specialization, consistent.

## BouRabeeGwynne.RegionDiameter
- `regionDiameterNN` (line 28), `regionDiameter` (line 32): max over A with 0 on ∅; `regionDiameter_empty` (line 62) holds. No junk.
- `eventually_empty_of_regionDiameter_tendsto_zero` (line 79): correct.

## BouRabeeGwynne.HypIIICorrectedRegions
- `correctedRegionStep` (line 15), `correctedRegions` (line 26): each step uses the current region's corrected error and its own maximum diameter; nested by construction.
- `correctedRegions_mass_le_geometric` (line 46): mass ≤ mass(A)·(1/2)^n, consistent with the docstring.

## BouRabeeGwynne.HypIIIGeometricScale
- `edgeMass_le_twice_incidentMass` (line 15), `incidentScale_le_rpow_incidentMass` (line 41), `cell_diam_le_rpow_incidentMass` (line 74): correct, with `hC : C ≠ ∞`.

## BouRabeeGwynne.HypIIIRegionScale
- `regionDiameter_le_rpow_incidentMass` (line 17), `regionDiameter_le_geometric_of_mass` (line 28), `eventually_empty_of_geometric_mass_hypIII` (line 53): correct. `0 < α` is needed for r < 1 and matches `RegularityIII`.

## BouRabeeGwynne.HypIIITaylorCost
- `surfaceTaylorRemainder_abs_le` (line 14): |R| ≤ 6Mδ², a sufficient constant as documented.

## BouRabeeGwynne.HypIIICostSeries
- `hypIIICost` (line 25): `2Mε² + tsum(...)`. `tsum` is 0 when not summable. All uses are under summability hypotheses (`hypIIICost_summable`, `hypIIICost_tendsto_zero` derives the limit by dominated convergence), so no junk value is reached.
- `hypIIICost_tendsto_zero` (line 28): correct.

## BouRabeeGwynne.HypIIICostBound
- `hypIIICost_summable` (line 12), `finite_corrected_cost_le_hypIIICost` (line 49): finite partial sums are bounded by `hypIIICost A (3M)`. The 6M → 2·(3M) rewrite is correct.

## BouRabeeGwynne.HypIIIErrorBound
- `dirichlet_error_le_hypIIICost_of_mass_decay` (line 21): `hmass` (lines 35–36) is a premise; the docstring says it is supplied by `correctedRegions_mass_le_geometric`, and the main theorem does so.
- `dirichlet_error_le_hypIIICost` (line 97): the final finite estimate for the actual solution; hypotheses (`hreg`, `hIbound`, `hwidth`, `hsmall`) are not contradictory on their face; no tiling instance was compiled.

## BouRabeeGwynne.Section3CaseIIITarget
- `theoremB_part_a_caseIII` (line 19): conclusion is the same `DirichletApproximationTarget`. `hIII : RegularityIII G` is `∃ α > 0, ∃ C ≠ ∞, eventually ∀ v, diam(P_v) ≤ C·incidentScale α v` (PaperObjects.lean:216), matching rw-spheres.tex:271 item (III). Choice of δ via `Classical.choose` (line 150) is only used under `hδgood`, and `hδbounds` covers the junk branch, so it is harmless.

## Nonvacuity examples
Scratch file: `Nonvacuity.lean`. Compiled from the repository root with `lake env lean …`, exit status 0. Axioms: `[propext, Classical.choice, Quot.sound]` for both declarations. The only output is an unused-variable linter warning on the existential `N` in the second declaration.

```lean
import BouRabeeGwynne.Section3CaseIITarget
import SpherePackings.Support.Guards.LatticeTilings

/-!
Nonvacuity of the hypothesis bundle of `BouRabeeGwynne.theoremB_part_a_caseII` (Hypothesis II,
Theorem B(a)): the lattice tiling sequence of `exists_lattice_tilingSequence` supplies the
tilings, collar, nearest vertices, approximation condition (1.3) and Hypothesis II, and
the zero function is harmonic on `ball 0 2`, a neighbourhood of `closure (ball 0 1)`.
-/

open Metric

namespace BouRabeeGwynne

/-- The non-dimensional hypotheses of `theoremB_part_a_caseII` (with `1 ≤ d` assumed) are
simultaneously satisfied by a concrete instance. -/
theorem nonvacuity_caseII_hypotheses {d : ℕ} (hd : 1 ≤ d) :
    ∃ (G : TilingSequence d) (N : NearestVertexData G) (U : Set (Euc d)) (hC : Euc d → ℝ),
      Bornology.IsBounded U ∧ HasAmbientCollar U G.domain ∧ N.ApproximationCondition ∧
        RegularityII G ∧ HarmonicNearClosure hC U := by
  obtain ⟨G, hcol, ⟨N⟩, hall, hII⟩ := SpherePackings.exists_lattice_tilingSequence hd
  refine ⟨G, N, ball (0 : Euc d) 1, fun _ => 0, isBounded_ball, hcol, hall N, hII,
    ball (0 : Euc d) 2, isOpen_ball, ?_, contDiffOn_const, fun x _ => by simp⟩
  exact (closure_ball_subset_closedBall).trans (closedBall_subset_ball (by norm_num))

/-- The conclusion of Theorem B(a) under Hypothesis II is attained on the same instance:
the hypotheses of `theoremB_part_a_caseII` can all be met at once. -/
theorem nonvacuity_caseII_conclusion {d : ℕ} (hd : 1 ≤ d) :
    ∃ (G : TilingSequence d) (N : NearestVertexData G),
      DirichletApproximationTarget G (ball (0 : Euc d) 1) (fun _ => 0)
        (fun _n _v => (0 : ℝ)) := by
  obtain ⟨G, hcol, ⟨N⟩, hall, hII⟩ := SpherePackings.exists_lattice_tilingSequence hd
  have hh : HarmonicNearClosure (fun _ : Euc d => (0 : ℝ)) (ball (0 : Euc d) 1) :=
    ⟨ball (0 : Euc d) 2, isOpen_ball,
      (closure_ball_subset_closedBall).trans (closedBall_subset_ball (by norm_num)),
      contDiffOn_const, fun x _ => by simp⟩
  exact ⟨G, N, theoremB_part_a_caseII hd G N (ball (0 : Euc d) 1) (fun _ => 0)
    isBounded_ball hcol (hall N) hII hh⟩

end BouRabeeGwynne

#print axioms BouRabeeGwynne.nonvacuity_caseII_hypotheses
#print axioms BouRabeeGwynne.nonvacuity_caseII_conclusion
```

Output: `'BouRabeeGwynne.nonvacuity_caseII_hypotheses' depends on axioms: [propext, Classical.choice, Quot.sound]` and the same for `nonvacuity_caseII_conclusion`.

What these show:
- The non-dimensional hypothesis bundle of `theoremB_part_a_caseII` (bounded U, ambient collar `closure U ⊆ interior D`, approximation condition (1.3) for every nearest-vertex choice, Hypothesis II, harmonicity of h_C near closure U) is jointly satisfiable. The instance is the lattice tiling sequence from `SpherePackings.exists_lattice_tilingSequence`, U = ball 0 1, and h_C = 0 harmonic on ball 0 2.
- The conclusion `DirichletApproximationTarget` is obtained for this instance. With zero data it is trivially true, so this shows satisfiability, not content.

Not done (time-boxed):
- The Hypothesis III bundle (`RegularityIII` with `incidentScale`, `theoremB_part_a_caseIII`) has no concrete instance in the repository. Showing it would need the diameter and facet-volume computations for lattice Voronoi cells, which I did not attempt in the time box. Mathematically the cube grid with α = 1/d and C = √d should satisfy it.
- The finite-network bundles (`harmonicIteration_uniform_error_of_volume_decay`, `dirichlet_error_le_volume_cutoff`) and the tiling-level `henergy`/`hfactor` bundle are satisfiable only in trivial regimes (zero boundary data, or A = ∅) without further work. I did not compile these.
