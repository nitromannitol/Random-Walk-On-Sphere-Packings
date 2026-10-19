# Audit batch 20
| Module | Verdict | Summary |
|---|---|---|
| SpherePackings.Support.Section3.PlanarQuadratic | NOTE | No `def`s. The box lemma and both Theorem 3.3 statements match their docstrings and the corrected Proposition 2.6 hypotheses; the paper's `V[U]`, `Û`, `ε`, `M`, `h_D` are reproduced; the bundle of both theorems is satisfiable on a lattice tiling (compiled). Notes: `ε ≤ 1/2` restriction, extra `Fintype` hypothesis, `V[U]` read as `{pos ∈ U}`, exponent 1/2 not sharp for this bound. |

## SpherePackings.Support.Section3.PlanarQuadratic
- (no `def`, `structure`, `class`, `abbrev` or `instance` in this file; the definitions used are checked below)
- Definitions used, checked against the paper:
  - `interiorVertices U := {v | pos v ∈ U}` (`BouRabeeGwynne/LocalRegion.lean:13`), `closedVertices U = V[U] ∪ ∂V[U]` (`:33`), `∂` = vertices outside `A` sharing an edge with `A` (`vertexBoundary`, `:21`). Paper: `V[U]` is "the set of vertices contained in the interior of U" (`rw-spheres.tex`, induced-subgraph item, around line 549) and `∂A`, `Ā` as in the closure item (around line 563). Equal for open `U`; the Lean theorems take arbitrary `U`, so for non-open `U` they cover boundary vertices of `U` too. Harmless generalization.
  - `Û := ⋃ w ∈ V̄[U], cell w` = paper's `\GCU` (`rw-spheres.tex:571`, eq. graph-closure). Matches.
  - `ConvexPolytope` cells are compact (`BouRabeeGwynne/PaperObjects.lean`, `ConvexPolytope.compact`), so `Metric.diam` of a cell is its true diameter and `diamENN` has no junk.
  - `conductanceReal v w = (facetVolume v w).toReal / ‖pos w - pos v‖` if adjacent, else `0` (`BouRabeeGwynne/DiscretePDE.lean:17`): facet length over edge length, paper eq. (conductance) at `rw-spheres.tex:233`. Facets are compact and `pos` is injective, so no `x / 0` or `toReal ⊤` junk.
  - `SolvesDirichlet U g h := DiscreteHarmonicOn h V[U] ∧ ∀ v ∈ ∂V[U], h v = g v` (`DiscretePDE.lean:105`): paper's `Δ h_D = 0` on `V[U]`, `h_D = h_C` on `∂V[U]`. Matches.
  - `IsHarmonicOn h U := ContDiffOn ℝ 2 h U ∧ ∀ x ∈ U, Δ h x = 0` (`BouRabeeGwynne/Harmonic.lean:17`): paper's `h_C ∈ C²`, `\CLap h_C = 0`. Matches; Lean asks for an open `W ⊇ Û`, the usual reading.
  - `slabIntersection L lower upper = {x | ∀ i, lower i < L i x < upper i}` (`BouRabeeGwynne/Section3Boxes.lean:19`): an open box. Matches the uses in the file.
  - `cellsContainedInterior R A S = {v ∈ A | cell v ⊆ S}` (`Section3Boxes.lean:51`). Matches its use as the maximum-principle region.
- `error_le_of_good_box_quadratic` (line 27): the conclusion `|h v - hC (pos v)| ≤ η + M (ε + D)²` is the docstring's statement. `hgood` is the good-cut hypothesis (`|h w - h_C| ≤ η` on interior vertices whose cell meets a slab face), `hdiam` says the open box has diameter at most `D`, `hdiamR` bounds cell diameters by `ε`. Signs and `≤` vs `<` are as intended: the cut and box conditions are strict, the error bounds are non-strict. No junk value. Satisfiable on its own with `h = hC = 0` and any `η ≥ 0` (the good-cut hypothesis then holds trivially); not separately instantiated in the compiled file, only via the main bundle below.
- `planar_dirichlet_bound_quadratic` (line 151): the conclusion `∀ k > 0, ∀ v ∈ V[U], |h_D v - h_C (pos v)| ≤ 6 k M ε vol(Û) + M (ε + √2/k)²` is the docstring's statement, for every `k > 0` (not ∃ k).
  - `ε` bounds `diam` over `V̄[U]` (paper's `ε := sup_{v ∈ V̄[U]} diam P_v`, `rw-spheres.tex:1044`); `M` bounds the Hessian on `Û` (`hHcell`) and on the edge segments (`hHseg`, the disclosed Prop 2.6 correction). The Hessian norm is the operator norm of `fderiv (fderiv hC)`; this is ≤ any Frobenius-type norm, so the hypothesis is at least as weak as a paper-style one. Harmless (stronger theorem).
  - Hypothesis list = that of `harmonic_energy_bound_segment` (`SpherePackings/Support/Section3/EnergyMinimal.lean:196`), with `d` fixed to 2 (its `1 ≤ d`) and an extra `0 ≤ ε`. The extra hypothesis is redundant whenever `V[U] ≠ ∅` (it follows from `hdiam`), and the conclusion is vacuous when `V[U] = ∅`. So the header's claim "needs only the hypotheses of the corrected Proposition 2.6" holds.
  - This is not the printed bound: the `L` term `2(√2/k + ε)L` is replaced by `M(ε + √2/k)²`. Documented (header, docstring, CORRESPONDENCE, STATUS); neither bound implies the other. Not a misstatement.
  - `[Fintype (T.closedVertices U)]` is a genuine extra assumption (finiteness of `V̄[U]`). In the paper this comes from `Ū ⊂ 𝒟` plus local finiteness. I could not derive it from the other hypotheses (`hcellD` puts the cells of `V[U]` in the interior of `D`, but nothing bounds `V[U]` inside a compact part of `D`). CORRESPONDENCE says it "replaces boundedness"; for this theorem that is accurate (no `hUR`), but it is a separate, non-derivable assumption. Harmless: the nonvacuity instance satisfies it.
  - Junk check: `(volume (⋃ w ∈ V̄[U], cell w)).toReal` is over a compact set, hence finite; `Real.sqrt 2 / k` with `k > 0`; no `tsum`, `ncard`, `sSup`, `ENNReal.toReal ⊤`. None of the traps changes the meaning.
  - Quantifiers and inequalities: `∀ k`, `∀ v`, `≤` throughout; `0 < k` is the right side condition.
- `planar_dirichlet_rate_half` (line 304): the conclusion `∀ v ∈ V[U], |h_D v - h_C (pos v)| ≤ (6 M vol(B_{R₀+1}) + (1+√2)² M) √ε` matches the docstring. It matches the paper's "in particular" (`rw-spheres.tex:1050-1053`, "there exists C = C(U,M,L)") with `C` depending on `U` (via `R₀`) and `M` only. That is a strengthening of the paper's clause: `L` is dropped and the constant is explicit.
  - `hUR` (`‖x‖ ≤ R₀` on `U`) is needed to make `C` explicit; the proof uses it (with `hε2`) to put `Û ⊆ closedBall 0 (R₀+1)` (line 346).
  - `ε ≤ 1/2` (`hε2`) is an extra restriction relative to the paper's unqualified "there exists C". The paper's own bound `6kMεvol + 2(√2/k+ε)L` with `k = ε^{-1/2}` gives `≤ C ε^{1/2}` only for bounded `ε` (the term `2εL` is not `O(ε^{1/2})` for large `ε`), so the restriction is the paper's implicit regime. Documented in the docstring.
  - Exponent: the same hypotheses give more. Taking `k = ε^{-1/3}` in `planar_dirichlet_bound_quadratic` yields `(6 M V + (1+√2)² M) ε^{2/3}` for `ε ≤ 1` (hand computation, not compiled), which implies the stated `ε^{1/2}` bound. The statement is correct and matches the paper's exponent, but it is not the sharpest rate this bound gives. Recorded, not a defect.
  - Junk check: the same as above; `Real.sqrt ε` with `hε : 0 ≤ ε`; `volume (closedBall …)` is finite.
- Satisfiability: the full bundle of both theorems (tiling, `U`, `h_C`, `W`, `W'`, `M`, `ε`, `D`, `Fintype`) holds on the lattice tiling `GT` (see Nonvacuity below). Note that the Hessian hypotheses hold only in the trivial case `M = 0`; the nonvacuity does not show that a nonzero Hessian bound can be attained together with the segment hypothesis.

## Nonvacuity examples
Command (from the repo root): `lake env lean Nonvacuity.lean`
Result: exit 0, no errors or warnings; `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for both examples (no `sorryAx`), so the module's theorems used by them are also free of `sorry`.

(Integration note: in the repository the examples are `SpherePackings/Audit/Nonvacuity/Batch20.lean`, which imports `PlanarQuadratic` instead of copying it.)  The scratch file `Nonvacuity.lean` (505 lines) = the imports `SpherePackings.Support.Guards.LatticeTilings` and `SpherePackings.Support.Section3.PlanarRateFull`, then a verbatim copy of `SpherePackings/Support/Section3/PlanarQuadratic.lean` (first line, the import, dropped), then `Examples20.lean` (118 lines, the appended examples). The copy is needed because `PlanarQuadratic` has no `.olean` in `.lake/build` and I did not build it.

The two examples, verbatim (the helper lemmas `GT_*`, `hess_zero`, `hcellD_ball`, `harmonic_zero` and the instance `GT_fintype` are in `Examples20.lean`):

```lean
/-- The Voronoi tiling of `(1/10) ℤ²` on the ball of radius `2` (as in `Batch19.lean`). -/
noncomputable def GT : OrthogonalTiling 2 :=
  voronoiTiling (grid (1 / 10 : ℝ)) (ball (0 : Euc 2) 2)
    (goodVoronoi_grid (by norm_num) (by norm_num) isBounded_ball)

theorem nonvacuous_quadratic :
    ∃ f : GT.V → ℝ,
      GT.SolvesDirichlet (ball (0 : Euc 2) 1) (fun v => (fun _ : Euc 2 => (0 : ℝ)) (GT.pos v)) f ∧
      ∀ k : ℝ, 0 < k → ∀ v ∈ GT.interiorVertices (ball (0 : Euc 2) 1),
        |f v - (fun _ : Euc 2 => (0 : ℝ)) (GT.pos v)| ≤
          6 * k * 0 * (1 / 2) *
              (MeasureTheory.volume (⋃ w ∈ GT.closedVertices (ball (0 : Euc 2) 1),
                (GT.cell w).carrier)).toReal +
            0 * (1 / 2 + Real.sqrt 2 / k) ^ 2 := by
  obtain ⟨f, hf⟩ := GT.exists_dirichlet (ball (0 : Euc 2) 1) GT_boundary_access
    (fun _ : GT.V => (0 : ℝ))
  refine ⟨f, hf, ?_⟩
  exact planar_dirichlet_bound_quadratic GT (ball (0 : Euc 2) 1) hcellD_ball isOpen_univ
    harmonic_zero (fun _ _ => subset_univ _) isOpen_univ contDiff_const.contDiffOn
    (fun _ _ _ _ _ _ => subset_univ _) (M := 0) (ε := 1 / 2) le_rfl (by norm_num)
    (fun v _ => GT_diam_le v) (fun _ _ x _ => hess_zero x)
    (fun _ _ _ _ _ _ x _ => hess_zero x) f hf

theorem nonvacuous_rate_half :
    ∃ f : GT.V → ℝ,
      GT.SolvesDirichlet (ball (0 : Euc 2) 1) (fun v => (fun _ : Euc 2 => (0 : ℝ)) (GT.pos v)) f ∧
      ∀ v ∈ GT.interiorVertices (ball (0 : Euc 2) 1),
        |f v - (fun _ : Euc 2 => (0 : ℝ)) (GT.pos v)| ≤
          (6 * 0 * (MeasureTheory.volume (Metric.closedBall (0 : Euc 2) (1 + 1))).toReal +
            (1 + Real.sqrt 2) ^ 2 * 0) * Real.sqrt (1 / 2) := by
  obtain ⟨f, hf⟩ := GT.exists_dirichlet (ball (0 : Euc 2) 1) GT_boundary_access
    (fun _ : GT.V => (0 : ℝ))
  refine ⟨f, hf, ?_⟩
  exact planar_dirichlet_rate_half GT (ball (0 : Euc 2) 1) hcellD_ball (R₀ := 1)
    (fun x hx => (mem_ball_zero_iff.mp hx).le) isOpen_univ harmonic_zero
    (fun _ _ => subset_univ _) isOpen_univ contDiff_const.contDiffOn
    (fun _ _ _ _ _ _ => subset_univ _) (M := 0) (ε := 1 / 2) le_rfl (by norm_num) le_rfl
    (fun v _ => GT_diam_le v) (fun _ _ x _ => hess_zero x)
    (fun _ _ _ _ _ _ x _ => hess_zero x) f hf
```

What they show:
- `GT` is the Voronoi tiling of `(1/10)ℤ²` restricted to the ball of radius 2 (the batch-19 construction). Its cells have diameter ≤ 1/2 (`GT_diam_le`), and `GT.closedVertices` is finite for `U = ball 0 1` (`GT_closed_finite`).
- Both examples discharge the full bundle: `hcellD` (cells of `V[U]` in the interior of the domain), `hW`/`hh` (harmonic on `univ`), `hcells`, `hW'`/`hC2`, `hsegs`, `M = 0` with `hHcell`/`hHseg` (Hessian of the zero function is zero), `ε = 1/2`, `hdiam`, a Dirichlet solution `f` from `exists_dirichlet`, and the `Fintype` instance. The rate example also discharges `hUR` with `R₀ = 1` and `ε ≤ 1/2`.
- The conclusions are instances with `M = 0` and `h_C = 0`, so they say `|f v| ≤ 0`. They show that the hypotheses can hold together, not that the bounds have content.
- Not done (time): a nonzero `M` with a non-affine `h_C`, the box lemma on its own, and a check with a nonzero Lipschitz constant.
