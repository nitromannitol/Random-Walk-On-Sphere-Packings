# Audit batch 23
| Module | Verdict | Summary |
|---|---|---|
| SpherePackings.Support.Section3.PlanarInternal | NOTE | Theorem 3.3 (bound and rate) matches the corrected paper; hypotheses are satisfiable (example below). Differences are safe: harmonicity only on the cells of `V[U]`, `V[U]` defined as `{pos ∈ U}`, explicit rate constant. |
| SpherePackings.Support.Section3.GeneralInternal | NOTE | Theorem 3.6 matches the corrected paper with an explicit constant; the smallness condition is `12 M ε ≤ 1` (at least as strong as the paper's); extra `hR₀`, `hε2` are harmless; harmonicity only on the cells of `V[U]`. |
| SpherePackings.Support.Section3.InternalTaylor | NOTE | Statements match the internal-edge comparison. The header says the Laplacian bound sums over internal edges only, but the statement sums over all neighbours in `V̄[U]` (a weaker, correct statement). |
| SpherePackings.Frozen.Theorem33Planar | NOTE | Statement identical to `planar_dirichlet_bound_internal`. The header cites "Corrections 4, 8 and 10" (no Correction 10 exists) and quotes the corrected hypothesis as "harmonic on the cells of V[U]" where the paper says "harmonic on Û". |
| SpherePackings.Frozen.Theorem33Rate | NOTE | Statement identical to `planar_rate_internal`. Same wrong cross-reference. The "published rate is false" remark is informal (no ledger or GAP-CHECKS entry). |
| SpherePackings.Frozen.Theorem36Rate | NOTE | Statement identical to `generaldim_full_internal`. The header writes "ε < (CM)⁻¹ is 12Mε ≤ 1", which conflates the paper's unspecified C with the explicit 12; the Lean statement is at least as strong as the paper's. |

Counts: OK 0, ISSUE 0, NOTE 6.

## SpherePackings.Support.Section3.PlanarInternal
No new `def`, `structure`, `class`, `abbrev` or `instance` in the module. Definitions used: `incidentMass`, `interiorVertices`, `closedVertices`, `finiteInterior`, `finiteNetwork`, `SolvesDirichlet`, `CompleteCell`, `columnBadSet`, `slabIntersection`, `cellsContainedInterior`. Junk-value check: cells are compact, so cell diameters and volumes are finite; `ε ≥ 0` is forced by `hdiam`; `ε ^ (2/3)` is an rpow at `ε ≥ 0`; no `sSup`, `tsum` or `ncard` appears. `d - 1` (in `IsCodimOneFacet`) is not reached here (`d = 2`).
- `incidentMass_le_two_volume` (line 30): matches the paper's `m(A) ≤ 2 vol₂(Û)` used in the proof of Theorem 2d. `incidentMass` (`Section3ColumnEstimate.lean:20`, identity `incidentMass_eq_half_ordered` at `Section3EnergyNormalization.lean:75`) is ½ × (sum over ordered pairs of `facetVolume · ‖e‖`), i.e. the sum over undirected edges. That equals the paper's `m(S) = Σ_{e∈E[S̄]} d·vol_d(Q_e)` by the paper's geometry identity.
- `le_of_slack_sq` (line 53): the δ → 0 limit, using `c ≥ 0`. Matches its docstring.
- `abs_le_box_internal` (line 89): conclusion `|φ v| ≤ η + M/2 (ε + D)²` matches its docstring. The hypotheses (`hdiam` for the box, `hgood` on cut cells) are satisfiable in the lattice example.
- `abs_le_slack_internal` (line 158): for every `δ > 0`, `|φ v| ≤ η + M/2 (ε + √2(1/k + δ))²`. `hbad` uses `μHE[1]` of the column bad set, the correct 1-dimensional measure for `d = 2`. Matches its docstring.
- `planar_dirichlet_bound_internal` (line 224): matches the corrected Theorem 2d displayed bound (corrected paper lines 1248–1262). The `∀ k > 0` form is equivalent to `≤ inf_k`. Hypothesis check against the corrected paper:
  - `M₀` bounds the cell Hessian on the cells of `V̄[U]`, i.e. on `Û` (`Û` is `⋃_{v∈V̄[U]} P_v`, corrected paper line 599). ✓
  - `M ≥ M₀` with `hTaylor` only on edges with both endpoints in `V[U]`: this is the paper's `M_U°` (corrected paper lines 893–900). ✓
  - `hcomplete` on `V[U]`: `CompleteCell` (`Support/Complete/Basic.lean:26`) is finitely many neighbours plus `frontier ⊆ ⋃ neighbour cells`, equivalent to the paper's `∂P_v = ⋃_{w∼v}(P_v∩P_w)` (corrected paper lines 563–566). ✓
  - `ε` bounds the diameter on `V̄[U]`; `hsol` is `SolvesDirichlet` (discrete harmonic on `V[U]`, data on `∂V[U]`). ✓

  Differences:
  - (a) `hharm` is required only on the cells of `V[U]`. The corrected paper assumes `h_C` harmonic on all of `Û` (corrected paper line 1250). The Lean hypothesis is weaker, so the Lean theorem is stronger. The docstring describes it correctly.
  - (b) `[Fintype (T.closedVertices U)]` is an assumption. The paper gets finiteness from boundedness of `U` and local finiteness.
  - (c) `interiorVertices U = {v | T.pos v ∈ U}` (`BouRabeeGwynne/LocalRegion.lean:13`), not the interior of `U` as in the corrected paper's definition of `V_n[U]` (corrected paper line 305). The two agree for open `U` (the paper's "bounded domain"). The Lean statement quantifies over arbitrary `U`, and its proof cannot use openness because no hypothesis states it. The docstring's "`V[U]` from the paper" is accurate only for open `U`.
  - (d) The constant `3 M₀ ε²` is the corrected paper's displayed one. The proof gives `2 M₀ ε²` (`boundaryCorrection_abs_le_cells`), so the statement is weaker than the proof by `M₀ ε²` and equal to the paper's.
- `planar_rate_internal` (line 350): explicit `C = M(3 + 6 vol(B_{R₀+1}) + (√2+1)²/2)`, bound `C ε^{2/3}` for `0 ≤ ε ≤ 1/2`. `ε > 0` is forced by `hdiam` and the nonempty interior of a cell. This matches the corrected "in particular" with the constant made explicit. `ε^{2/3} ≤ ε^{1/2}` for `ε ≤ 1`, so it implies the paper's claim. It is stronger than the paper's `∃ C ≤ C ε^{1/2}`. The constant depends only on `M` and `R₀`.

## SpherePackings.Support.Section3.GeneralInternal
No new definitions. Private helpers are checked by name only.
- `generaldim_full_internal` (line 154): matches the corrected Theorem 3.6 (corrected paper lines 1367–1381 with `M := M_U°(h_C) ∨ 1`). Differences:
  - (a) `M` is any `M ≥ 1` with the cell-Hessian bound and the internal-Taylor bound. This is at least as strong as the paper's `M_U° ∨ 1`.
  - (b) `hDc` bounds `Σ diam` over every finite connected `Q` of small cells (connectivity in `adjGraphIn`, the induced facet graph, `ComponentChain.lean:23`). This is equivalent to the paper's `D = sup over components of 𝒜`: `V̄[U]` is finite, and sub-components sum to at most their component. Not stronger.
  - (c) The conclusion has an explicit constant `C_L(d, R₀) = C₀ + (4(D₀+1)+1)/log 2`, with `D₀ = R₀+1` and `C₀ = (24dD₀+3)(3+log K'/log 2)/log 2`, instead of the paper's `∃ C(U)`. The smallness is `12 M ε ≤ 1` (non-strict), instead of `ε < (CM)⁻¹`. Since `C_L ≥ 12` (indeed `C₀ ≥ 27·3/log 2 > 12`), the Lean hypothesis covers `ε < (C_L M)⁻¹`, so the Lean statement implies the paper's existential.
  - (d) Extra hypotheses `hR₀ : 0 ≤ R₀` (harmless: if `U ≠ ∅` it follows from `hUR`; if `U = ∅` then `V[U] = ∅` and the conclusion is vacuous) and `hε2 : ε ≤ 1/2` (implied by `hsmall` with `M ≥ 1`).
  - (e) `hharm` only on the cells of `V[U]` (paper: `Δh_C = 0` on `Û`), as in PlanarInternal (a).
- Junk check: `Real.log (1/ε)` is meaningful only for `ε > 0`, which is forced (`hdiam` plus the nonempty interior of a cell). `ε ^ K` is an rpow at `ε ≥ 0`, fine. `Real.log (max … 1)` is fine.
- Satisfiability note: the bundle needs every cell diameter `≤ ε ≤ 1/(12M) ≤ 1/12`. A square grid of mesh `1/10` (diameter `√2/10 ≈ 0.141`) does not satisfy it, so the Theorem 3.6 bundle is nonvacuous only on finer meshes. The paper has the same smallness, so this is not a defect. The example below uses mesh `1/40`.

## SpherePackings.Support.Section3.InternalTaylor
No new `def`, `structure` or `instance`. Definitions used: `surfaceTaylorRemainder` (`BouRabeeGwynne/CorrectedSurfaceField.lean:16`, `h(w) − h(v) − ∇h(v)(w−v)`, exact), `energy` (`DiscretePDEAlgebra.lean:113`), `laplacian` (`DiscretePDEAlgebra.lean:109`), `boundaryCorrection`, `externalBoundary` (`Section3LocalMaximum.lean:21`), `BoundaryAccessible` (`FiniteDirichlet.lean:18`), `IsCodimOneFacet` (`PaperObjects.lean:61`).
- `surfaceTaylorRemainder_abs_le_cells` (line 44): bound `2 M δ²`. The docstring chain `(M/2)(diam P_v + diam P_w)² ≤ 2Mδ²` is what the proof shows. ✓
- `boundaryCorrection_abs_le_cells` (line 105): `|b| ≤ 2 M ε²`. The corrected paper's displayed `eq:initial-boundary-correction` says `M₀ ε²`, while its Theorem 2d proof uses `2 M₀ ε²`. The Lean statement uses the constant the proof supports. This is an inconsistency inside the paper, not in the Lean.
- `correctedSurfaceField_bound_internal` (line 163) and private `correctedSurfaceField_bound_active` (line 122): flux bounds `3 M δ · facetVolume`. Helper statements, no junk.
- `energy_boundaryCorrected_le_internal` (line 183): `energy = ½ Σ_{v,w} a(v,w)(f w − f v)²`, i.e. the sum over undirected edges. This equals the paper's `D(f,A) = Σ_e cond(e)⁻¹ |∇^a f(e)|²` with `∇^a f(e) = cond(e)(f w − f v)` (corrected paper `eq:anabla`, `eq:dir.energy`). The bound `9 M² δ² · incidentMass` is the paper's `9 M² δ² m(S)` (corrected paper line 1230). The finite `SolvesDirichlet` requires `hD = g` on all of `R ∖ A`, which is `∂V[U]` here. ✓
- `laplacian_sq_dist_of_complete` (line 317): at complete `u`, `Δ‖· − z‖²(u) = Σ_w a(u,w)‖w−u‖²`. `laplacian` is the undivided `Σ_w a(u,w)(f w − f u)`, matching the paper's `Δ^a` (the identity fails with a total-conductance normalization). ✓ Matches the affine-harmonicity lemma at complete cells.
- `abs_laplacian_boundaryCorrected_le` (line 343): the RHS is `M/2 · Σ_{w ∈ V̄[U]} a(u,w)‖w−u‖²`, summing over all neighbours including boundary ones. The module header (lines 28–29) says "a sum over internal edges only". The statement is correct and is the form the comparison principle needs. Only the header is inaccurate. NOTE.
- `abs_le_of_abs_laplacian_le` (line 437): maximum-principle comparison. The hypothesis `0 ≤ c · q v` is used to drop `c q(v)` from `φ(v) + c q(v) ≤ η`. Matches the docstring. ✓
- `IsCodimOneFacet` (`d - 1` truncation): for `d = 0` the space is a point and has no edges, so the truncation is harmless.

## SpherePackings.Frozen.Theorem33Planar
- Statement (lines 25–47) is clause-for-clause identical to `planar_dirichlet_bound_internal`, including `hsol`, `hTaylor` and `hHcell` on the right sets. It matches the corrected Theorem 2d, with the reading in PlanarInternal (a)–(d).
- Header: "Corrections 4, 8 and 10". The corrected paper has no Correction 10. Its list (`paper/rw-spheres-corrected.tex:634–650`) has nine items, and its TeX tags are CORRECTION 4 and 8 and CLOSE 3 for this theorem. README items 5 and 6 are the right references. NOTE.
- Header says the corrected statement has "`h_C` … harmonic on the cells of `V[U]`". The corrected Theorem 2d says `h_C ∈ C²(Û)` harmonic on `Û` (corrected paper lines 1248–1253). The Lean hypothesis is weaker, so the theorem is stronger, but the header misquotes the paper.
- The printed bound quoted in the header (`rw-spheres.tex:1031–1049`) is the printed `inf_k(6kMε vol(Û) + 2(√2k⁻¹+ε)L)`, as stated. ✓
- G4 consistency: with sites at cell centres, the rows `y = 1/2, 3/2` are the vertex-boundary rows where `h_C = 0`, so `h_D ≡ 0` is consistent with the counterexample. I checked consistency only; I did not re-verify the Codex verdict in `ledger/gap-checks/`.

## SpherePackings.Frozen.Theorem33Rate
- Statement is clause-for-clause identical to `planar_rate_internal` (constant `M(3 + 6 vol(B_{R₀+1}) + (√2+1)²/2)`, `ε ≤ 1/2`, `ε^{2/3}`). Stronger than the paper's `∃ C ≤ C ε^{1/2}`. The header's "hence" is valid since `ε^{2/3} ≤ ε^{1/2}` for `ε ≤ 1`.
- Header: same wrong cross-reference as Theorem33Planar. NOTE.
- Header and README item 6 claim the published rate is false with a uniform constant, because "for large ε, a product tiling with a large central cell has an error of order ε". This is informal (no ledger or GAP-CHECKS entry; README says counterexamples are informal). The Lean statement does not depend on it.

## SpherePackings.Frozen.Theorem36Rate
- Statement is clause-for-clause identical to `generaldim_full_internal` (conclusion constant, `hsmall`, `hDc`, `hLgrad`, `hHcell`, `hTaylor`). Extra `hR₀ : 0 ≤ R₀` and `hε2 : ε ≤ 1/2` are harmless (GeneralInternal (d)).
- Header: "`ε < (C M)⁻¹` is `12 M ε ≤ 1`". This is misleading: the paper's `C` is unspecified, and the conclusion's constant is the explicit `C_L` (≥ 12), not 12. The Lean smallness is non-strict. The statement is at least as strong as the paper's (GeneralInternal (c)). NOTE.
- Header: "Corrections 4, 8 and 11". Correction 11 exists (CORRECTION 11, corrected paper lines 1401 and 1491), but it concerns the decay theorem's iteration, so the reference is at best partial. Same issue as above.
- Consistent with README item 5 (`M_U°` for Theorems 3.3, 3.6, 3.7) and with the Theorem 3.6 entry of CORRESPONDENCE.

## Nonvacuity examples
Now `SpherePackings/Audit/Nonvacuity/Batch23.lean`. It imports `SpherePackings.Audit.Nonvacuity.Batch20` (read only, for the lattice tiling `GT` and its boundary/fintype facts) and reuses that file's `GT` tiling. Compiled from the repository root with `lake env lean Nonvacuity.lean`, exit code 0:

```
Nonvacuity.lean:18:20: warning: `TensorProduct.induction_on` has been deprecated: Use `TensorProduction.inductionOn` instead
'AuditBatch23.nonvacuous_planar_internal' depends on axioms: [propext, Classical.choice, Quot.sound]
'AuditBatch23.nonvacuous_planar_rate_internal' depends on axioms: [propext, Classical.choice, Quot.sound]
'AuditBatch23.nonvacuous_generaldim_internal' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, so all three examples are kernel-checked with the standard axioms only. The only warning is a deprecation (`inductionOn` has different case names, so I kept `induction_on`).

What they show:
- `nonvacuous_planar_internal` and `nonvacuous_planar_rate_internal` (`GT`, `h_C = ⟪a, ·⟫`, `M₀ = M = 0`, `ε = 1/2`, `R₀ = 1`): every hypothesis of `planar_dirichlet_bound_internal` and `planar_rate_internal` holds together for a non-constant `h_C`. `hcomplete` comes from `CompleteCell.of_subset_interior`, `hsol` from `GT.exists_dirichlet`, and `hdiam` from `GT_diam_le`. The conclusion then forces the discrete solution to equal `h_C` on `V[U]`, which is correct for linear data. Limitation: with `M = 0` the Hessian and Taylor hypotheses are trivial. The quadratic case `h = x₀² − x₁²` with `M₀ = M = 2` is not compiled. On paper: the Hessian is `diag(2, −2)` (norm 2), the Taylor remainder is `(w₀−v₀)² − (w₁−v₁)² ≤ ‖w−v‖² = (M/2)‖w−v‖²`, and `h` is harmonic.
- `nonvacuous_generaldim_internal` (`GF`, the Voronoi tiling of `(1/40) ℤ²` on the ball of radius 2, `h_C = ⟪a, ·⟫`, `M = 1`, `K = 1`, `ε = 1/12`, `L = ‖a‖`, `R₀ = 1`, `D` = total diameter of all cells): every hypothesis of `generaldim_full_internal` holds, including `12 M ε ≤ 1` at equality and `hDc` with a finite `Dc`. Limitation: again the Hessian is zero. The reason for the finer mesh is that `GT` (mesh `1/10`, diameter `√2/10`) cannot satisfy `12 M ε ≤ 1` with `M ≥ 1`; this is the Theorem 3.6 smallness, not a defect.

### Source (compiled verbatim)
```lean
import SpherePackings.Audit.Nonvacuity.Batch20
import SpherePackings.Support.Section3.PlanarInternal
import SpherePackings.Support.Section3.GeneralInternal

-- They reuse the lattice tiling `GT` of `Audit20Nonvacuity` (voronoi tiling of `(1/10) ℤ²` on the
-- ball of radius `2`), its boundary accessibility and its interior-cell containment.

open MeasureTheory Metric Set BouRabeeGwynne BouRabeeGwynne.OrthogonalTiling SpherePackings
open SpherePackings.Voronoi
open scoped Laplacian
open Audit20Nonvacuity

namespace AuditBatch23

lemma lift_zero_apply (t : TensorProduct ℝ (Euc 2) (Euc 2)) :
    (TensorProduct.lift (0 : Euc 2 →ₗ[ℝ] Euc 2 →ₗ[ℝ] ℝ)) t = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => exact map_zero _
  | tmul m n => simp [TensorProduct.lift.tmul]
  | add x y hx hy => rw [map_add, hx, hy, add_zero]

/-- A Laplacian vanishes where the second derivative vanishes. -/
lemma lap_eq_zero_of_fderiv_fderiv (f : Euc 2 → ℝ) (x : Euc 2)
    (h : fderiv ℝ (fderiv ℝ f) x = 0) : Δ f x = 0 := by
  show tensorIteratedFDerivTwo ℝ f x (InnerProductSpace.canonicalCovariantTensor (Euc 2)) = 0
  simp [tensorIteratedFDerivTwo, bilinearIteratedFDerivTwo, h]
  exact lift_zero_apply _

/-- The linear function `x ↦ ⟪a, x⟫`: harmonic, with zero Hessian and zero Taylor remainder. -/
noncomputable def lin (a : Euc 2) : Euc 2 → ℝ := fun x => inner ℝ a x

lemma lin_fderiv (a : Euc 2) (x : Euc 2) : fderiv ℝ (lin a) x = innerSL ℝ a :=
  (innerSL ℝ a).hasFDerivAt.fderiv

lemma lin_fderiv_fderiv (a : Euc 2) (x : Euc 2) : fderiv ℝ (fderiv ℝ (lin a)) x = 0 := by
  have hfun : fderiv ℝ (lin a) = fun _ => innerSL ℝ a := funext (lin_fderiv a)
  rw [hfun]
  exact fderiv_const_apply _

lemma lin_hess (a : Euc 2) (x : Euc 2) : ‖fderiv ℝ (fderiv ℝ (lin a)) x‖ ≤ 0 := by
  rw [lin_fderiv_fderiv, ContinuousLinearMap.opNorm_zero]

lemma lin_harm (a : Euc 2) (x : Euc 2) : Δ (lin a) x = 0 :=
  lap_eq_zero_of_fderiv_fderiv _ x (lin_fderiv_fderiv a x)

lemma lin_contDiff (a : Euc 2) : ContDiffOn ℝ 2 (lin a) univ :=
  (innerSL ℝ a).contDiff.contDiffOn

lemma lin_taylor (a : Euc 2) (v w : Euc 2) :
    |lin a w - lin a v - (fderiv ℝ (lin a) v) (w - v)| ≤ 0 / 2 * ‖w - v‖ ^ 2 := by
  rw [lin_fderiv, innerSL_apply_apply]
  simp [lin, inner_sub_right]

lemma GT_complete (v : GT.V) (hv : v ∈ GT.interiorVertices (ball (0 : Euc 2) 1)) :
    CompleteCell GT v :=
  CompleteCell.of_subset_interior (by norm_num) (hcellD_ball v hv)

/-- The bundle of `planar_dirichlet_bound_internal` holds for `h_C = ⟪a, ·⟫` on `GT`, with
`M₀ = M = 0` and `ε = 1/2`; the discrete solution is the one supplied by the tiling. -/
theorem nonvacuous_planar_internal (a : Euc 2) :
    ∃ f : GT.V → ℝ,
      GT.SolvesDirichlet (ball (0 : Euc 2) 1) (fun v => lin a (GT.pos v)) f ∧
      ∀ k : ℝ, 0 < k → ∀ v ∈ GT.interiorVertices (ball (0 : Euc 2) 1),
        |f v - lin a (GT.pos v)| ≤
          3 * 0 * (1 / 2 : ℝ) ^ 2 +
            (6 * k * 0 * (1 / 2 : ℝ) *
                (MeasureTheory.volume (⋃ w ∈ GT.closedVertices (ball (0 : Euc 2) 1),
                  (GT.cell w).carrier)).toReal +
              0 / 2 * (Real.sqrt 2 / k + 1 / 2) ^ 2) := by
  obtain ⟨f, hf⟩ := GT.exists_dirichlet (ball (0 : Euc 2) 1) GT_boundary_access
    (fun v => lin a (GT.pos v))
  refine ⟨f, hf, ?_⟩
  exact planar_dirichlet_bound_internal GT (ball (0 : Euc 2) 1) GT_complete isOpen_univ
    (lin_contDiff a) (fun _ _ => subset_univ _) (fun _ _ x _ => lin_harm a x)
    (M₀ := 0) (M := 0) (ε := 1 / 2) le_rfl le_rfl (by norm_num) (fun v _ => GT_diam_le v)
    (fun _ _ x _ => lin_hess a x) (fun v _ w _ _ => lin_taylor a (GT.pos v) (GT.pos w)) f hf

/-- The bundle of `planar_rate_internal` holds for the same data, with `R₀ = 1`. -/
theorem nonvacuous_planar_rate_internal (a : Euc 2) :
    ∃ f : GT.V → ℝ,
      GT.SolvesDirichlet (ball (0 : Euc 2) 1) (fun v => lin a (GT.pos v)) f ∧
      ∀ v ∈ GT.interiorVertices (ball (0 : Euc 2) 1),
        |f v - lin a (GT.pos v)| ≤
          0 * (3 + 6 * (MeasureTheory.volume (Metric.closedBall (0 : Euc 2) (1 + 1))).toReal +
            (Real.sqrt 2 + 1) ^ 2 / 2) * (1 / 2 : ℝ) ^ ((2 : ℝ) / 3) := by
  obtain ⟨f, hf⟩ := GT.exists_dirichlet (ball (0 : Euc 2) 1) GT_boundary_access
    (fun v => lin a (GT.pos v))
  refine ⟨f, hf, ?_⟩
  exact planar_rate_internal GT (ball (0 : Euc 2) 1) GT_complete (R₀ := 1)
    (fun x hx => (mem_ball_zero_iff.mp hx).le) isOpen_univ (lin_contDiff a)
    (fun _ _ => subset_univ _) (fun _ _ x _ => lin_harm a x)
    (M₀ := 0) (M := 0) (ε := 1 / 2) le_rfl le_rfl (by norm_num) (by norm_num)
    (fun v _ => GT_diam_le v) (fun _ _ x _ => lin_hess a x)
    (fun v _ w _ _ => lin_taylor a (GT.pos v) (GT.pos w)) f hf

/-! Theorem 3.6: the smallness `12 M ε ≤ 1` with `M ≥ 1` needs cells of diameter at most `1/12`,
so the mesh is `1/40` here (`GT` has diameter `√2/10`). -/

noncomputable def GF : OrthogonalTiling 2 :=
  voronoiTiling (grid (1 / 40 : ℝ)) (ball (0 : Euc 2) 2)
    (goodVoronoi_grid (by norm_num) (by norm_num) isBounded_ball)

lemma GF_domain : GF.domain = ball (0 : Euc 2) 2 := voronoiTiling_domain _ _ _

lemma GF_mesh_le : GF.mesh ≤ ENNReal.ofReal (1 / 12) := by
  refine (voronoiTiling_mesh_le _).trans (ENNReal.ofReal_le_ofReal ?_)
  have hs : Real.sqrt ((2 : ℕ) : ℝ) ≤ 3 / 2 := by
    have := Real.sqrt_le_sqrt (show ((2 : ℕ) : ℝ) ≤ (3 / 2) ^ 2 by norm_num)
    rwa [Real.sqrt_sq (by norm_num)] at this
  linarith

lemma GF_diam_le (v : GF.V) : Metric.diam (GF.cell v).carrier ≤ 1 / 12 := by
  have hne : GF.mesh ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top GF_mesh_le
  have h1 : ENNReal.ofReal (Metric.diam (GF.cell v).carrier) ≤ GF.mesh :=
    le_iSup (fun w : GF.V => ENNReal.ofReal (Metric.diam (GF.cell w).carrier)) v
  exact ((ENNReal.ofReal_le_iff_le_toReal hne).mp h1).trans
    (ENNReal.toReal_le_of_le_ofReal (by norm_num) GF_mesh_le)

lemma GF_cell_sub (v : GF.V) (hv : GF.pos v ∈ ball (0 : Euc 2) 1) :
    (GF.cell v).carrier ⊆ ball (0 : Euc 2) 2 := by
  intro x hx
  have h1 : dist x (GF.pos v) ≤ 1 / 12 :=
    (Metric.dist_le_diam_of_mem (GF.cell v).compact.isBounded hx
      (interior_subset (GF.pos_mem_interior v))).trans (GF_diam_le v)
  have h2 := dist_triangle x (GF.pos v) 0
  rw [dist_zero_right, dist_zero_right] at h2
  rw [mem_ball_zero_iff] at hv ⊢
  linarith

lemma GF_closed_finite : (GF.closedVertices (ball (0 : Euc 2) 1)).Finite :=
  GF.closedVertices_finite isBounded_ball (by rw [GF_domain]; exact GT_closure_sub)
    (fun v hv => by rw [GF_domain]; exact GF_cell_sub v hv)

noncomputable instance GF_fintype : Fintype (GF.closedVertices (ball (0 : Euc 2) 1)) :=
  @Fintype.ofFinite _ GF_closed_finite.to_subtype

lemma GF_boundary_access :
    (GF.finiteNetwork (GF.closedVertices (ball (0 : Euc 2) 1))).BoundaryAccessible
      (GF.finiteInterior (ball (0 : Euc 2) 1)) :=
  GF.finiteNetwork_boundaryAccessible_of_cell_interior (R := GF.closedVertices (ball (0 : Euc 2) 1))
    (A := GF.finiteInterior (ball (0 : Euc 2) 1)) (by norm_num)
    (coordinateAxis (0 : Fin 2)) (coordinateAxis_ne_zero 0)
    (fun w hw x hwx => GF.neighbor_mem_closedVertices hw hwx)
    (fun w hw => by
      rw [GF_domain, isOpen_ball.interior_eq]
      exact GF_cell_sub w.1 hw)

lemma GF_cellD_ball : ∀ v ∈ GF.interiorVertices (ball (0 : Euc 2) 1),
    (GF.cell v).carrier ⊆ interior GF.domain := fun v hv => by
  rw [GF_domain, isOpen_ball.interior_eq]
  exact GF_cell_sub v hv

lemma GF_complete (v : GF.V) (hv : v ∈ GF.interiorVertices (ball (0 : Euc 2) 1)) :
    CompleteCell GF v :=
  CompleteCell.of_subset_interior (by norm_num) (GF_cellD_ball v hv)

/-- The bundle of `generaldim_full_internal` holds for `h_C = ⟪a, ·⟫` on `GF`, with `M = 1`,
`K = 1`, `ε = 1/12`, `L = ‖a‖`, `R₀ = 1` and `D` the total diameter of all cells, which is finite. -/
theorem nonvacuous_generaldim_internal (a : Euc 2) :
    ∃ f : GF.V → ℝ,
      GF.SolvesDirichlet (ball (0 : Euc 2) 1) (fun v => lin a (GF.pos v)) f ∧
      ∃ C : ℝ, ∀ v ∈ GF.interiorVertices (ball (0 : Euc 2) 1),
        |f v - lin a (GF.pos v)| ≤ C := by
  obtain ⟨f, hf⟩ := GF.exists_dirichlet (ball (0 : Euc 2) 1) GF_boundary_access
    (fun v => lin a (GF.pos v))
  refine ⟨f, hf, _, generaldim_full_internal (by norm_num) GF (ball (0 : Euc 2) 1) GF_complete
    (R₀ := 1) (by norm_num) (fun x hx => (mem_ball_zero_iff.mp hx).le) isOpen_univ
    (lin_contDiff a) (fun _ _ => subset_univ _) (fun _ _ x _ => lin_harm a x)
    (M := 1) (L := ‖a‖) (ε := 1 / 12) (K := 1) (Dc := ∑ u ∈ GF_closed_finite.toFinset,
      Metric.diam (GF.cell u).carrier) le_rfl le_rfl (fun v _ => GF_diam_le v)
    (fun _ _ x _ => (lin_hess a x).trans zero_le_one)
    (fun v _ w _ _ => (lin_taylor a (GF.pos v) (GF.pos w)).trans (by
      rw [zero_div, zero_mul]
      positivity))
    (fun _ _ x _ => le_of_eq (by rw [lin_fderiv, innerSL_apply_norm]))
    (fun Q hQ _ => Finset.sum_le_sum_of_subset_of_nonneg
      (fun u hu => GF_closed_finite.mem_toFinset.mpr (hQ u hu).1)
      (fun _ _ _ => Metric.diam_nonneg))
    (by norm_num) (by norm_num) f hf⟩

#print axioms nonvacuous_planar_internal
#print axioms nonvacuous_planar_rate_internal
#print axioms nonvacuous_generaldim_internal

end AuditBatch23
```
