# Correspondence: paper ↔ Lean

Maps every frozen declaration to *Random walk on sphere packings and Delaunay triangulations in
arbitrary dimension* (Ahmed Bou-Rabee and Ewain Gwynne, arXiv:2405.11673v2).

## Conventions

- The paper is pinned at `paper/rw-spheres.tex` (the unchanged arXiv v2 source); its SHA-256 is in
  `ledger/manifest.yaml`.  Source locations are `rw-spheres.tex:<line range>` plus the LaTeX
  `\label`.  Theorems A and B are the two `theoremA` environments; the other results keep the
  printed numbering (Proposition 1.1, Lemma 2.1, …, Theorem 6.1).
- The bytes between `-- FROZEN-STATEMENT-BEGIN` and `-- FROZEN-STATEMENT-END` are the contract:
  take the text just past the BEGIN marker line up to the start of the END marker line, and take
  the SHA-256 of its UTF-8 encoding; `python3 tools/check_manifest.py` is the authority.
- The corrected paper is `paper/rw-spheres-corrected.tex` (the same source with the corrections
  marked in comments), also pinned by its SHA-256 in `ledger/manifest.yaml`.
- `form` in the manifest: *as printed*; *corrected* (the statement of the corrected paper, where the
  printed statement is changed; for each change the README and the sections below say whether the
  printed version is false, with a counterexample, or open); *reformulated* (the same content in
  different terms, possibly stronger); *weakened* (state `PARTIAL`: proved under a hypothesis
  stronger than the corrected paper's).
- **Ambient objects.**  `Euc d` is `EuclideanSpace ℝ (Fin d)`.  Tilings, polytopes, conductances,
  the Dirichlet problem, curves modulo time parametrization, the stopped walk and Brownian laws are
  leobon12's definitions (`BouRabeeGwynne/PaperObjects.lean`, `CurveSpace.lean`,
  `StoppedCurveLaws.lean`, `StoppedWalk.lean`, `DiscretePDE.lean`, `LocalRegion.lean`):
  - a cell is a compact convex set with nonempty interior given by finitely many halfspaces; cells
    cover `D`, have disjoint interiors and are locally finite on compact subsets of `D`;
  - `v ~ w` iff `P_v ∩ P_w` is nonempty with affine span of dimension `d - 1`; orthogonality is
    required for all such pairs;
  - `V_n[U]` is `interiorVertices U` (positions in `U`), `∂V_n[U]` is `boundaryVertices U`
    (outside `U`, adjacent to `V_n[U]`), `V̄_n[U]` is `closedVertices U`;
  - the curve metric (1.2) is the Fréchet extended distance over order automorphisms of `[0,1]`
    on curves reparametrized to `[0,1]`, and `CurveSpace d` is the metric quotient; Prokhorov
    distance is Mathlib's `levyProkhorovEDist`;
  - the walk is the Markov chain on the finite closed region with the tiling conductances, absorbed
    outside `U`, built by the Ionescu-Tulcea theorem; its stopped curve is the polygonal
    interpolation through the first exit vertex;
  - a standard Brownian law is a probability measure on `C(ℝ≥0, ℝ^d)` with independent coordinate
    processes that are real Brownian motions in Mathlib's sense.
- The nearest vertex `z^n` is any nearest vertex (`NearestVertexData`); the paper's lexicographic
  tie-breaking is one choice.  Theorem A holds for every choice.

## Corrections and differences in formulation

### Ambient set and edges (Theorems A, B and Sections 2–4)

The paper's `D` is any subset covered by the tiles; Theorem A and Theorem B(b) ask
`closure U ⊆ D`, and Theorem B(a) only `U ⊆ D`.  The square grid of mesh `1/n` (`n` odd) of
`D = [0,1] × [0,2]`, `U = (0,1) × (1/2, 3/2)` and `h_C(x,y) = cosh(π(x - 1/2)) cos(π(y - 1))` satisfy
the hypotheses; the discrete solution is `0` while `h_C → 1` at the centre, and the walk can only
exit through the top or bottom.  The same grid of the open rectangle refutes Theorem B(a).
leobon12's statements use the ambient collar `closure U ⊆ interior D`, adopted here.  This
counterexample, like the others recorded here, is an informal argument; none is formalized in Lean.

Edges are read as in the paper (a reading, not a correction): `v ~ w` when "`P_v ∩ P_w` is a
`(d-1)`-dimensional facet" (`rw-spheres.tex:226`), that is, when `P_v ∩ P_w` has dimension `d - 1`,
with orthogonality across every such contact (leobon12).  The paper uses the word this way (it calls
`𝒞_s ∩ 𝒞_{s'}` "the `(d-1)`-dimensional facet", line 354), and its proof of Lemma 2.2 sums the flux
through `∂P_v` over the edges at `v`.  Under a stricter reading, in which `P_v ∩ P_w` must be a whole
facet of both cells, rows of unit squares shifted by `1/2` would form a tiling all of whose edges
are horizontal and orthogonal, on which the walk stays on horizontal lines.

### Theorem B(b)

The boundary value at `v ∈ ∂V_n[U]` is `h_C` at "the nearest point in the cell `P_v` for which
it is defined" (footnote at `rw-spheres.tex:305`), which may not exist (`P_v ∩ closure U` can be
empty, for `h_C` given on `closure U`).  leobon12's statement samples `h_C` at any nearest point of
`closure U`, for every choice of such points; where the printed point exists, the two points are
within `2ε_n` of each other, so by uniform continuity and the maximum principle the two statements
agree; the statement also
asserts that these points lie on `frontier U` within two meshes of `v`, and that a choice exists.
The proof here follows the paper (`rw-spheres.tex:1494-1496`) with Theorem A in place of Theorem
4.1: the discrete solution is the mean of the boundary values under the exit law of the walk, the
continuum solution is the mean under the Brownian exit law (proved here for data only continuous on
`closure U`, by exhausting `U`), and Theorem A gives closeness of the two laws uniformly in the start.

### Proposition 1.1

Printed: for `μ` with `r^{β⁺} ≤ μ(B_r(z)) ≤ r^{β⁻}` for `z ∈ U`.  If `U` is the unit ball and `μ` the
Lebesgue measure restricted to `U`, these hold (with `β⁺ = d + 1`, `β⁻ = d - 1/2`), the points of
`Λ_m` lie in `U`, and the cell of an extreme point of `Λ_m` is unbounded and meets `U`; the conclusion
fails almost surely for all large `m`.  The printed proof applies (1.4) at points outside `U`.  Corrected: (1.4) holds on an
open set `W ⊇ closure U` (`HolderMassBounds μ W β⁺ β⁻`).  A Poisson point process with intensity
`ν` is a random point set with finitely many points in every bounded set and almost surely in
every measurable set `B` of finite intensity, whose counts in such sets are Poisson with mean `ν B`,
independent for disjoint sets (`IsPoissonPointProcess`); the proof uses
only the one-dimensional laws, and the processes for different `m` need not be independent.  The
union bound for cubes with two points uses `∑ λ_x² ≤ (max λ_x) ∑ λ_x` and the bounded overlap of the
cubes in place of the printed partition into mass levels.
`IsPoissonPointProcess` asks that `Λ ∩ B` be finite for every bounded `B` and every `ω`, not only
almost surely; this is equivalent, since the conclusion is almost sure and an almost surely locally
finite process can be changed on a null set.  The points form a set, so a Poisson
point process has an intensity with no atoms (the count in a singleton is at most one).  The
paper's `μ` is defined near `closure U` and has no atoms on `W` by (1.4), but may have atoms
elsewhere.  So the registered statements assume only that the points of `Λ_m` in `W` form a
Poisson point process of intensity `m μ|_W` (and, for the "in particular" clause, that `Λ_m` is
locally finite); both follow from `Λ_m` being a Poisson point process of intensity `m μ`
(`IsPoissonPointProcess.restrict_inter`), and the proofs use the process only in `W`.  The repository does
not construct a Poisson point process: no Lean example exhibits one, for Lebesgue measure or any
other intensity.

The "in particular" clause is formalized for the tilings of `D = thickening ρ U` whose vertices are
the points of `Λ_m` with cells meeting `D` (`IsVoronoiTilingOf`); before the first index from which
the cell bounds hold, the sequence repeats that tiling.  Hypothesis (II) holds with
`q_n = -log vol(B_{r_n})`.

### Lemmas 2.1–2.5, Proposition 2.6, Section 3

- **Lemma 2.1**: finite degree at each vertex of `A`; stated for any `SimpleGraph`, with the
  incoming divergence and both orientations of each edge, as printed.
- **Complete cells.**  Lemmas 2.2, 2.5 and 3.1, Propositions 2.6 and 3.2 and Theorems 3.3, 3.6 and
  3.7 ask that the cells of `V[U]` be complete (`CompleteCell`, `Support/Complete/Basic.lean`):
  finitely many neighbours, and `frontier P_v ⊆ ⋃_{w ~ v} P_w`.  Each printed statement is false
  without some such hypothesis (README, item 1; for Theorems 3.3, 3.6 and 3.7, check G4 in
  `GAP-CHECKS.md`, on the grid of the previous section): the printed proofs apply the divergence
  theorem on each cell, or follow a column of cells to a boundary vertex, and omit the flux through
  facets shared with no other cell (`rw-spheres.tex:850-854`).  Completeness is the hypothesis of the
  corrected paper (Correction 4).  It is implied by `P_v ⊆ interior D` (`CompleteCell.of_subset_interior`),
  and it allows cells that meet `∂D` only in a lower-dimensional set (the centre square of a 3 × 3
  grid of unit squares with a corner square removed).  leobon12's estimates that took
  `P_v ⊆ interior D` (polytope Gauss–Green, the column traversal, cell masses, accessibility, the
  trimming of the corrected iteration) are re-proved for complete cells in `Support/Complete/`.
- **Lemma 2.2**: at vertices with complete cells.  Proof: the surface flux of `ℓ_p` through each
  contact is `a(v,w)(ℓ_p(w) - ℓ_p(v))`, and the fluxes sum to `∫_{P_v} Δ ℓ_p = 0` (the polytope
  Gauss–Green identity for complete cells, `sum_surfaceFlux_eq_integral_laplacian_of_complete`).
  Stated for `d ≥ 1`.
- **Lemma 2.3**: on any finite network with symmetric nonnegative conductances; `E[Ā]` is the set
  of directed pairs of positive conductance with an endpoint in `A`, and `θ` vanishes elsewhere.  `θ` is
  antisymmetric, the printed convention for vector fields (`rw-spheres.tex:576`).
- **Lemma 2.4**: as printed (leobon12).
- **Lemma 2.5** (`dual_coverage_complete`): the printed first inclusion `U ⊆ ⋃_{e ∈ E[Ū]} Q_e` is
  false (a small ball inside one square of the unit grid contains no vertex); it is replaced by
  `⋃_{v ∈ V[U]} P_v ⊆ ⋃_{e ∈ E[Ū]} Q_e`, for complete cells of `V[U]`, for `d ≥ 1`.  Proof: a cell
  is covered by its marked point and the pyramids `conv(v, P_v ∩ P_w)` over its contacts with its
  (finitely many) neighbours, and the dual polytopes `Q_e` contain these pyramids.  Boundedness of
  `U` and `U ⊆ D` are not needed and are dropped (a stronger statement).
- **Proposition 2.6** (`harmonic_energy_bound_complete`): one tiling and one set `U`, as in the
  corrected paper (Corrections 4 and 8): complete cells of `V[U]`; `h_C` is `C²` on an open set
  containing the cells of `V̄[U]` and harmonic on the cells of `V[U]`; `M` bounds the Hessian on the
  cells of `V[U]` and, for each edge of `E[Ū]`, the finite Taylor remainder
  `|h_C(w) - h_C(v) - ∇h_C(v)·(w - v)| ≤ (M/2) ‖w - v‖²` at one active endpoint.  The printed version
  is false: without completeness (README item 1), and with complete cells for a slit-domain harmonic
  function (README item 5, check G2; an edge need not cross its own facet, so the segment `[v, w]`
  can leave `Û`, where the Hessian is not controlled).  A Hessian bound `M` on the edge segments
  implies the Taylor condition.  `ε` bounds the diameters of the cells of `V̄[U]`, as printed.
  `[Fintype (T.closedVertices U)]` replaces boundedness (weaker).
- **Proposition 3.2** (`harmonic_column_bound_complete`): the hypotheses of the corrected
  Proposition 2.6.  The printed version is false: without completeness (README item 1), and with
  complete cells for a thin reflected Voronoi configuration (README item 5).
- **Lemma 3.1** (`column_poincare_measure_bound_of_complete`): leobon12's form: columns in any
  direction `e ≠ 0`; the bad set is the set of `y` in the projection of the cell of a vertex of
  `V[U]` where `|f| > τ`, a superset of the printed one, so the bound is stronger; the cells of `A`
  are complete (for two unit squares with `f = 1` the printed bound fails: there is no boundary
  vertex, `D(f, U) = 0`, and the bad set has length 2).
- **The internal-edge constant** (`Support/Section3/InternalTaylor.lean`).  Theorems 3.3, 3.6 and 3.7
  use, as in the corrected paper, the Hessian bound on the cells of `V̄[U]` and the finite Taylor
  inequality only on the internal edges (both endpoints in `V[U]`, both orientations).  The error
  `h_D - h_C` is split, after leobon12's corrected iteration, as `b + f₀`: `b` is the Poisson
  solution on `V[U]` whose source is the Taylor remainders of the boundary edges, and
  `|b| ≤ 2 M₀ ε²` from the cell Hessian alone, along the broken segment `v, z, w` through a contact
  point `z` (`surfaceTaylorRemainder_abs_le_cells`, `boundaryCorrection_abs_le_cells`); the energy of
  `f₀` is at most `9 M² ε²` times the incident mass, and its Laplacian at `u ∈ V[U]` is minus the
  conductance sum of the Taylor remainders over the internal edges at `u`, so
  `±f₀ + (M/2) ‖· - v‖²` is discrete subharmonic.  Whether Theorems 3.3, 3.6 and 3.7 hold with the
  published cell Hessian constant alone is open.
- **Theorem 3.3**, the bound (`planar_dirichlet_bound_internal`): the bound of the corrected paper,
  `3 M₀ ε² + 6 k M ε vol(Û) + (M/2)(√2 k⁻¹ + ε)²` for every `k > 0`, with `M₀` the Hessian bound on the
  cells of `V̄[U]` and `M ≥ M₀` the internal Taylor constant; no local oscillation or Lipschitz
  hypothesis.  The proof is the printed one applied to `f₀`: the energy of `f₀` gives, through
  Lemma 3.1, bad columns of measure at most `k⁻¹` in each direction, hence a rectangle of diameter at
  most `√2 k⁻¹` around `v` whose boundary cells carry `|f₀|` below `3 k M ε ∑ ‖e‖ vol(H_e) ≤ 6 k M ε vol(Û)`
  (`exists_unitLine_cuts_around`); on the cells inside it, the comparison with `(M/2) ‖· - v‖²` gives
  `|f₀(v)| ≤ 6 k M ε vol(Û) + (M/2)(ε + √2 k⁻¹)²`, and `|b| ≤ 2 M₀ ε² ≤ 3 M₀ ε²`.  The printed bound
  `inf_k (6 k M ε vol(Û) + 2(√2 k⁻¹ + ε) L)` is false without completeness (check G4); with complete
  cells, whether it holds is not settled here: the printed proof applies the mean value theorem on
  the segment between two vertices (`rw-spheres.tex:1071-1074`), which can leave `Û`.
- **Theorem 3.3**, the rate (`planar_rate_internal`): for `ε ≤ 1/2`,
  `sup |h_D - h_C| ≤ M (3 + 6 vol(B_{R₀+1}) + (√2 + 1)²/2) ε^{2/3}`, from the bound with `k = ε^{-1/3}`
  (and `ε^{2/3} ≤ ε^{1/2}`); `C` depends on `U` (through `R₀`) and `M` only, which the printed
  `C(U, M, L)` allows.  With a constant uniform over all meshes the printed rate is false (for large
  `ε`, a product tiling with a large central cell); the range `ε ≤ 1/2` is the correction.
  `incidentEnergy` and `incidentMass` sum over undirected edges, so each is half the printed
  directed sum: in Proposition 2.6 both sides halve and the constant `9` is unchanged; in
  Proposition 3.2 the Lean threshold `3 k M ε · incidentMass` is half the printed one (a stronger
  statement).
- **Lemma 3.5**: leobon12's form, for any finite family of edges of length at most `δ`.
- **Theorem 3.6** (`generaldim_full_internal`): the bound `C M K ε log(1/ε) + D L` of the corrected
  paper, with `M = M_U° ∨ 1`, for `12 M ε ≤ 1` and `ε ≤ 1/2`, with `C` explicit in `d` and a bound
  `R₀` on `‖x‖` over `U` (the paper's `C(U)`), `L` a bound on the gradient on the cells of `V̄[U]`,
  `K ≥ 1` arbitrary, and `D` bounding the total diameter of every connected set of cells of `V̄[U]`
  of volume below `ε^K` (equivalently the supremum over the components of `𝒜`).  The proof uses
  leobon12's corrected iteration (`correctedRegions`) in place of the printed harmonic replacement:
  each step costs at most `(24 d (R₀ + 1) + 3) M ε` and halves the incident mass, and after
  `O(K log(1/ε))` steps the remaining cells have volume below `ε^K`.  Step 2 is completed at the exit
  cell: on a component `Q` the error is at most both `L (D_Q + ε)` (oscillation along the cells of `Q`
  and the exit cell) and `M ρ²`, with `ρ` the distance to the exit vertices (through the corrected
  error of the last region, which vanishes on the boundary of `Q`); the minimum of the two is at most
  `D L + C M K ε log(1/ε)` (`component_case_bound`).  The printed theorem is false without
  completeness (check G4); with the published cell Hessian constant alone it is open.  The
  qualitative consequence under (II) (`rw-spheres.tex:1405-1408`), used for Theorem B(a), is
  leobon12's theorem (`BouRabeeGwynne/Section3CaseIITarget.lean`).
- **Theorem 3.7** (`generaldim_decay_rate_internal`): the rate `C M ε log(1/ε)` of the corrected
  paper, with `M = M_U° ∨ 1`, for `12 M ε ≤ 1` and `ε ≤ 1/2`, with an explicit constant in `d`, `F`,
  `α` and a bound `R₀` on `‖x‖` over `U` (the paper's `C(U, F, α)`).  The printed proof has a gap at
  `rw-spheres.tex:1371` (check G1, `GAP-CHECKS.md`): its estimates involve the cells on the boundary of
  the bad set, whose diameters the printed iteration does not control.  leobon12's corrected
  iteration (`correctedRegions`) controls them with a boundary-corrected energy and the trimming
  cutoff `√(ε δ_i)`, at the cost `hypIIICost`; that cost is at most `C M ε log(1/ε)`
  (`hypIIICost_le_rate`).  Its boundary-edge Taylor remainders at the first step are bounded by the
  cell Hessian alone, and the later ones are internal edges (`Support/Section3/DecayInternal.lean`).
  The printed theorem is false without completeness (check G4); with the published cell Hessian
  constant alone it is open.  The decay hypothesis is leobon12's form
  `diam(P_v) ≤ F sup_w (‖w - v‖ vol_{d-1}(P_v ∩ P_w))^α`, the printed one by Lemma 2.4 (`F` scaled by
  `d^α`).  The qualitative consequence under (III), used for Theorem B(a), is leobon12's theorem
  (`BouRabeeGwynne/Section3CaseIIITarget.lean`).

### Section 4

- **Setting** (`SpherePackings.NearestNeighbourWalk`): a vertex set `V ⊆ ℝ^d`, a symmetric edge
  relation, and a Markov kernel on `V` (with the Borel structure of `ℝ^d`) whose steps follow the
  edges almost surely: any time-homogeneous nearest-neighbour Markov chain.  `V_n[S]` is the set of
  vertices in the interior of `S`, `∂V_n[S]` the set of the other vertices adjacent to one of them
  (`rw-spheres.tex:296`).  The chain is built by the Ionescu–Tulcea theorem
  (`SpherePackings.MarkovChain.law`).
- **Assumption D** (`SpherePackings.AssumptionD`), as printed: a domain `D`, `δ > 0`, and for all
  `r > 0` and `x ∈ B_δ(D)`, with `B = B_r(x) ∩ B_δ(D)` (closed neighbourhoods, the paper's `B_r(·)`),
  (4.1) uniform convergence of the vertex selection `z^n` on `B`, and (4.2) for every `h_C`
  harmonic on an open set containing `B`, uniform convergence to `h_C` on `V_n[B]` of the solutions
  of the Dirichlet problem on `V_n[B]` with data `h_C` on `∂V_n[B]`.  The existence of these
  solutions, which the paper presupposes, is not assumed, and (4.2) is required of every solution;
  for large `n` this forces uniqueness and almost sure exit when a solution exists (for bounded data
  the exit expectation is a solution, and convergence of all solutions forces almost sure exit
  (`MarkovChain.survival_eq_zero_of_forall_solution_bounded`)).  The selection `z^n` is a parameter: the paper's nearest vertex
  is one choice, and the results hold for every selection satisfying (4.1).
- **Proposition 4.2** (`PROVED`, corrected): for every ball whose closure lies in `B_δ(D)` (README,
  correction 10; the printed statement leaves this implicit, and its proof applies (4.2) to the unit
  ball), uniformly over the open ball, in the Lévy–Prokhorov metric.  The discrete
  harmonic measure is the law of the exit position on the event of exit; (4.2) forces almost sure
  exit for large `n`.  The paper's Poisson extension of
  the test function to a larger ball is replaced by a harmonic polynomial close to it near the
  sphere (leobon12's `exists_harmonic_polynomial_near_sphere_collar`).
- **Theorem 4.1** (`PROVED`, as printed; `SpherePackings.theorem41`): for any sequence of
  nearest-neighbour walks under Assumption D as printed, a bounded Lipschitz domain `U ⊆ D`, and
  `z^n` any nearest vertex of `z` (the paper's lexicographic tie-break is one choice; the nearest
  vertex also makes the vertex set closed, hence measurable in `ℝ^d`).  The laws are those of the
  free walk from `z^n`, interpolated and stopped at its first exit from `V_n[U]`
  (`NearestNeighbourWalk.stoppedWalkLaw`), and of Brownian motion from `z` stopped at its exit from
  `U`, as laws on curves modulo time parametrization with the metric (1.2); the convergence is
  `∀ η > 0, ∀ᶠ n, ∀ z ∈ U, d_LP ≤ η`, i.e. of the supremum over `z`.  The theorem also states that
  the walk leaves `V_n[U]` almost surely for large `n` (the paper uses this implicitly).
  `U ⊆ D` is all that is needed: Assumption D speaks on the `δ`-neighbourhood of `D`, which
  contains a collar of `closure U`.  "Domain" is `IsLipschitzDomain` (open, nonempty,
  preconnected, Lipschitz boundary); the proof uses only openness and the Lipschitz boundary.
  The proof is leobon12's proof of Theorem A (finite couplings of the walk and Brownian
  excursions from balls, with partitions of the exit points), generalized to the chain of an
  arbitrary Markov kernel (`SpherePackings/General/Walk/`), with the ball-exit laws from
  Proposition 4.2.  Where leobon12 uses a deterministic bound on the steps of the tiling walk, the
  proof uses the shape of the excursions from balls (`actualWalkStage_shape`): on the good event of
  the coupling, where walk and Brownian exit points are close, this bounds the ranges of the walk
  excursions (`walk_range_of_goodExcursionPairs`) and the steps before the exit
  (`actualWalkStage_step_le_of_range`).

### Section 5

- **Lemma 5.1(a)** (`geometric_constraint_inner_collar`): as in the corrected paper, the hypothesis
  is asked of every grid point `x ∈ r ℤ^d` whose cube `x + [-r, r]^d` meets `U`; conclusion for the
  closed ball.  The proof rounds each coordinate of `s` towards the corresponding coordinate of a
  second site `s'` at distance less than `2r`, giving a tested grid point whose cube
  `x + [-2r, 2r]^d` contains both.  The printed hypothesis (`x ∈ r ℤ^d ∩ U`) is false near `∂U`: in
  `ℝ`, `U = (0,10)`, `r = 1`, `S = {0.1, -1.5}` (the same example, with the other coordinates fixed at
  `5` and `U = (0,10)^d`, works in every dimension).  Boundedness of `U` and local finiteness of `S`
  are not needed and are dropped.
- **Lemma 5.1(b)** (`geometric_constraint_outer`): as in the corrected paper, there are constants
  `δ = δ(d) ∈ (0, 1)` and `R = R(d) ≥ 2` such that the hypothesis on the grid points of
  `k ℤ^d ∩ B_{Rk}(U)` gives `𝒞_s ⊆ B_{4k√d}(s)`; for any sets `U` and `S`.  The proof takes `δ = 1/10`
  and `R = max(2, 1.1√d)` (so `R = 2` for `d ≤ 3`): if `z ∈ 𝒞_s` had `‖z - s‖ > (3/5) k√d`, a point `p`
  of the segment `[s, z]` slightly beyond distance `(3/5) k√d` rounds to a grid point within
  `1.1 k√d` of `s` (finitely many grid points lie in a bounded set, so "slightly" can be chosen to
  keep this bound), whose cube contains a site strictly closer to `z` than `s`.  The printed radius
  `2k` is false for every `d ≥ 13`: with `k = 1`, `s = (-1/100, 1/2, …, 1/2)`, `U = B_{1/1000}(s)` and
  `S = {s} ∪ (ℤ^d ∩ B_2(U))`, every tested grid point is a site, so the hypothesis holds for every
  `δ > 0`, every tested grid point has first coordinate at most `0`, and `s + 5√d e₁ ∈ 𝒞_s`
  (corrected paper, after the proof of Lemma 5.1; for `d ≥ 14` the whole ray `s + t e₁` lies in
  `𝒞_s`, check G3 in `GAP-CHECKS.md`).  For `4 ≤ d ≤ 12` the printed radius also suffices, with a
  smaller `δ`, by a separate rounding argument that is not formalized (the paper does not need
  it); there the registered statement is weaker than the printed one.  The printed proof treats `s` as a grid point: its witnesses
  near `s ± k e_i` (`rw-spheres.tex:1673`) are not supplied by the hypothesis.  Proposition 1.1 uses
  the lemma through its constants `δ` and `R` only.
- **Lemma 5.2**: as printed, for `d ≥ 1`, with `δ' = 1/(4d)`; the proof bounds `|y|_∞` directly
  instead of showing `B_R ⊆ P`.

### Section 6

- **Theorem 6.1**: a sphere packing is a family of spheres with pairwise disjoint open balls; the
  tangency graph joins distinct tangent spheres; simple random walk has unit conductances.  "Does
  not converge to Brownian motion modulo time parametrization in the scaling limit" is formalized as:
  for the walk from the centre `0`, positions scaled by `1/n`, stopped on leaving the unit ball, the
  laws exist for every `n ≥ 1` and do not converge to the stopped Brownian law in Lévy–Prokhorov
  distance.  In dimension `k + 3` the big spheres sit at `2x`, `x ∈ ℤ^{k+3}`, `x₀ ≤ 0`, and the small
  ones at `(√7/2, 1/2, 1/2, 0, …) + y`, `y₀ ≥ 0`, with `y_j` even for `j ≥ 3` (for `k = 0` the paper's
  packing; for `k ≥ 1` the printed packing has small middle spheres with no big neighbour).  The
  function equal to `4x₀` on big spheres and `y₀ + 1` on small ones is harmonic for the walk (this is
  what makes the printed probability `2/3`), and is within `1/n` of `g(x) = x₀ + min(x₀, 0)` after
  scaling; so the walk's exit mean of `g` tends to `0`, while for Brownian motion it is negative,
  which a Lipschitz test function detects.
- **Covering** (`SpherePacking.Covered`, `rw-spheres.tex:331-333`): a sphere is covered when the
  closed half-spaces bounded by its tangent hyperplanes, on its side
  (`⟪x - c_i, c_j - c_i⟫ ≤ r_i ‖c_j - c_i‖` for each tangent sphere `j`), meet in a bounded set; the
  intersection always contains the ball of the sphere, and it is a polytope when the sphere has
  finitely many neighbours.  The registered statement adds that in dimension three every sphere is
  covered (`Counterexample.packing_covered`: each sphere has tangent neighbours whose half-spaces
  bound every coordinate).  Like the printed statement, it does not ask that the packing cover `ℝ^d`;
  for `d ≥ 4` the packing used here does not (a small sphere other than the middle ones touches
  others only in the first three coordinate directions).

## Node table

<!-- NODE-TABLE-BEGIN (generated by tools/sync_docs.py) -->

| Paper result | Lean statement | Form | Proved by | Note |
|---|---|---|---|---|
| [Theorem A](paper/rw-spheres.tex#L259): Convergence of random walk<br>`theorem:convergence-of-rw-trace` | [SpherePackings.Frozen.theoremA](SpherePackings/Frozen/TheoremA.lean#L25) | corrected | leobon12 | Ambient collar `closure U ⊆ interior D`; every codimension-one contact of two cells is an edge (the paper's reading). |
| [Theorem B(a)](paper/rw-spheres.tex#L297): Convergence of the Dirichlet problem, data harmonic near `closure U`<br>`theorem:convergence-of-the-dirichlet-problem` | [SpherePackings.Frozen.theoremB_a](SpherePackings/Frozen/TheoremBa.lean#L18) | corrected | leobon12 | Ambient collar; eventual existence and uniqueness of the discrete solution are part of the conclusion. |
| [Theorem B(b)](paper/rw-spheres.tex#L297): Convergence of the Dirichlet problem, data continuous on `closure U`<br>`theorem:convergence-of-the-dirichlet-problem` | [SpherePackings.Frozen.theoremB_b](SpherePackings/Frozen/TheoremBb.lean#L21) | corrected | this repository | Ambient collar; boundary values sampled at nearest points of `closure U`. leobon12's statement, proved here. |
| [Proposition 1.1](paper/rw-spheres.tex#L371): Voronoi cells of Poisson processes lie between two balls<br>`prop:min-max-edge-length` | [SpherePackings.Frozen.prop11_cells](SpherePackings/Frozen/Prop11Cells.lean#L24) | corrected | this repository | As in the corrected paper: the mass bounds (1.4) on a neighbourhood `W` of `closure U`; the printed version (on `U` only) is false (Lebesgue measure restricted to the unit ball: the cells of the extreme points are unbounded). Only the points in `W` are assumed to form a Poisson point process, of intensity `m μ|_W`. |
| [Proposition 1.1](paper/rw-spheres.tex#L378): Theorems A and B for Poisson–Voronoi tilings<br>`prop:min-max-edge-length` | [SpherePackings.Frozen.prop11_theoremAB](SpherePackings/Frozen/Prop11TheoremAB.lean#L20) | corrected | this repository | The "in particular" clause; tilings of a neighbourhood of `closure U` by the cells meeting it. Hypotheses as in the first part, and `Λ_m` locally finite. |
| [Lemma 2.1](paper/rw-spheres.tex#L633): Discrete divergence theorem<br>`lemma:discrete-divergence-theorem` | [SpherePackings.Frozen.lemma21FiniteDegrees](SpherePackings/Frozen/Lemma21FiniteDegrees.lean#L20) | corrected | this repository | Finite degree at the vertices of `A`; any simple graph. |
| [Lemma 2.2](paper/rw-spheres.tex#L657): Affine functions are discrete harmonic<br>`lemma:linear-lie-in-kernel` | [SpherePackings.Frozen.lemma22_affine_kernel](SpherePackings/Frozen/Lemma22AffineKernel.lean#L18) | corrected | this repository | At vertices whose cell is complete (finitely many neighbours, boundary covered by the cells of the neighbours), as in the corrected paper; the printed identity is false at a cell with a facet shared with no other cell (two unit squares). |
| [Lemma 2.3](paper/rw-spheres.tex#L684): Dual variational principle<br>`lemma:dual-variational-principle` | [SpherePackings.Frozen.lemma23_dual_variational](SpherePackings/Frozen/Lemma23DualVariational.lean#L20) | as printed | leobon12 (paper form here) | On any finite network with symmetric conductances; sums over `E[Ā]`. |
| [Lemma 2.4](paper/rw-spheres.tex#L739): Volume of the dual polytope<br>`lemma:geometry-bound` | [SpherePackings.Frozen.lemma24_dual_volume](SpherePackings/Frozen/Lemma24DualVolume.lean#L16) | as printed | leobon12 |  |
| [Lemma 2.5](paper/rw-spheres.tex#L769): Dual polytopes cover the cells<br>`lemma:easy-global-qe-bounds` | [SpherePackings.Frozen.lemma25_dual_coverage](SpherePackings/Frozen/Lemma25DualCoverage.lean#L19) | corrected | this repository (from leobon12) | `⋃_{v ∈ V[U]} P_v ⊆ ⋃_{e ∈ E[Ū]} Q_e` for complete cells of `V[U]`, as in the corrected paper, in place of the printed `U ⊆ ⋃_{e ∈ E[Ū]} Q_e`, which is false (a small ball inside one square of a grid contains no vertex); the upper inclusion as printed. |
| [Proposition 2.6](paper/rw-spheres.tex#L822): Energy bound<br>`prop:energy-bound` | [SpherePackings.Frozen.prop26_energy](SpherePackings/Frozen/Prop26Energy.lean#L27) | corrected | this repository (from leobon12) | As in the corrected paper: complete cells of `V[U]`; `h_C` `C²` near the cells of `V̄[U]` and harmonic on the cells of `V[U]`; `M` bounds the Hessian on the cells of `V[U]` and, for each edge of `E[Ū]`, the finite Taylor remainder at one active endpoint. The printed version is false: two unit squares (without completeness), and a slit-domain harmonic function (check G2). |
| [Lemma 3.1](paper/rw-spheres.tex#L937): Poincaré-type inequality<br>`lemma:ptype-inequality` | [SpherePackings.Frozen.lemma31_poincare](SpherePackings/Frozen/Lemma31Poincare.lean#L23) | corrected | leobon12 | Complete cells of `V[U]`, as in the corrected paper (the printed version is false without it: two unit squares, `f = 1`); columns in any direction and the bad set through projected cells (stronger). |
| [Proposition 3.2](paper/rw-spheres.tex#L980): Closeness on columns<br>`prop:energy-poincare-bound` | [SpherePackings.Frozen.prop32_columns](SpherePackings/Frozen/Prop32Columns.lean#L26) | corrected | this repository (from leobon12) | The hypotheses of the corrected Proposition 2.6, as in the corrected paper. The printed version is false: two unit squares (without completeness), and a thin reflected Voronoi configuration (with complete cells). Threshold half the printed one (stronger). |
| [Theorem 3.3](paper/rw-spheres.tex#L1030): Planar bound<br>`theorem:2d` | [SpherePackings.Frozen.theorem33_planar](SpherePackings/Frozen/Theorem33Planar.lean#L31) | corrected | this repository (from leobon12) | As in the corrected paper: `3 M₀ ε² + inf_k (6 k M ε vol(Û) + (M/2)(√2 k⁻¹ + ε)²)`, `M₀` the Hessian bound on the cells of `V̄[U]`, `M ≥ M₀` the finite Taylor constant of the internal edges; complete cells; no oscillation or Lipschitz hypothesis. The printed bound is false without completeness (check G4); with complete cells whether the published linear bound holds is not settled, and the theorem with the published cell Hessian constant alone is open. |
| [Theorem 3.3](paper/rw-spheres.tex#L1050): Planar rate `C ε^{2/3}`<br>`theorem:2d` | [SpherePackings.Frozen.theorem33_rate](SpherePackings/Frozen/Theorem33Rate.lean#L29) | corrected | this repository (from leobon12) | As in the corrected paper: `sup |h_D - h_C| ≤ C ε^{2/3}` (hence `C ε^{1/2}`) for `ε ≤ 1/2`, `C = M (3 + 6 vol(B_{R₀+1}) + (√2 + 1)²/2)`, with the hypotheses of the bound. The printed rate is false with a constant uniform over all meshes (a product tiling with a large central cell), and false without completeness (check G4); with the published cell Hessian constant alone it is open. |
| [Lemma 3.5](paper/rw-spheres.tex#L1128): Weighted gradient-energy estimate<br>`lemma:gradient-energy-estimate` | [SpherePackings.Frozen.lemma35_weighted_energy](SpherePackings/Frozen/Lemma35WeightedEnergy.lean#L16) | as printed | leobon12 | `d vol_d(Q_e)` written as `‖e‖ vol_{d-1}(H_e)` (Lemma 2.4). |
| [Theorem 3.6](paper/rw-spheres.tex#L1147): General dimension, small cells<br>`theorem:generaldim` | [SpherePackings.Frozen.theorem36_rate](SpherePackings/Frozen/Theorem36Rate.lean#L33) | corrected | this repository (from leobon12) | As in the corrected paper: complete cells of `V[U]`; `M = M_U°(h_C) ∨ 1`, the Hessian bound on the cells of `V̄[U]` and the finite Taylor remainder on internal edges only. The bound `C M K ε log(1/ε) + D L` for `12 M ε ≤ 1`, `C` explicit in `d` and a bound on `U`, through leobon12's corrected iteration; the printed Step 2 completed at the exit cell. The printed version is false without completeness (check G4); with the published cell Hessian constant alone it is open. |
| [Theorem 3.7](paper/rw-spheres.tex#L1314): General dimension, decay hypothesis<br>`theorem:generaldim-decay` | [SpherePackings.Frozen.theorem37_rate](SpherePackings/Frozen/Theorem37Rate.lean#L33) | corrected | this repository (from leobon12) | As in the corrected paper: complete cells of `V[U]`; `M = M_U°(h_C) ∨ 1`, the Hessian bound on the cells of `V̄[U]` and the finite Taylor remainder on internal edges only. The printed version is false without completeness (check G4); with the published cell Hessian constant alone it is open. The rate `C M ε log(1/ε)` for `ε < (C M)⁻¹`, `C` explicit in `d`, `F`, `α` and a bound on `U`, through leobon12's corrected iteration (the printed one has a gap, check G1). |
| [Theorem 4.1](paper/rw-spheres.tex#L1481): Central limit theorem under Assumption D<br>`theorem:general-clt` | [SpherePackings.Frozen.theorem41](SpherePackings/Frozen/Theorem41.lean#L24) | as printed | this repository (from leobon12's proof of Theorem A) | Any nearest-neighbour walks on graphs in `ℝ^d` under Assumption D as printed (existence of the discrete Dirichlet solutions is not assumed, and (4.2) is required of every solution); `z^n` any nearest vertex; also: the walk eventually leaves `V_n[U]` almost surely. |
| [Proposition 4.2](paper/rw-spheres.tex#L1511): Convergence of harmonic measure<br>`prop:convergence-of-harmonic-measure` | [SpherePackings.Frozen.prop42_general](SpherePackings/Frozen/Prop42General.lean#L23) | corrected | this repository | Any nearest-neighbour walks on graphs in `ℝ^d` under Assumption D as printed; any ball whose closure lies in `B_δ(D)` (the printed statement leaves this implicit and fails without it); Lévy–Prokhorov, uniformly over the ball. |
| [Lemma 5.1(a)](paper/rw-spheres.tex#L1627): Inner balls of Voronoi cells<br>`lemma:geometric-constraint` | [SpherePackings.Frozen.lemma51a_inner](SpherePackings/Frozen/Lemma51Inner.lean#L18) | corrected | this repository | The grid points `x` whose cube `x + [-r, r]^d` meets `U`, as in the corrected paper; the printed version (grid points in `U`) is false: if `U` contains no grid point, its hypothesis is empty, while two sites of `U` at distance less than `r` violate its conclusion. |
| [Lemma 5.1(b)](paper/rw-spheres.tex#L1635): Outer balls of Voronoi cells<br>`lemma:geometric-constraint` | [SpherePackings.Frozen.lemma51b_outer](SpherePackings/Frozen/Lemma51Outer.lean#L23) | corrected | this repository | As in the corrected paper: there are `δ = δ(d) ∈ (0, 1)` and `R = R(d) ≥ 2` such that the grid points within `R k` of `U` suffice (proved with `δ = 1/10`, `R = max(2, 1.1√d)`), for any sets `U`, `S`. The printed radius `2k` fails for every `d ≥ 13` (counterexample in the corrected paper; check G3 for `d ≥ 14`); for `4 ≤ d ≤ 12` it also suffices, with a smaller `δ`, by a rounding argument not formalized here, so there the registered statement is weaker than the printed one. |
| [Lemma 5.2](paper/rw-spheres.tex#L1650): Polar of a perturbed cross-polytope<br>`lemma:dual-polytope-bound` | [SpherePackings.Frozen.lemma52_dual_polytope](SpherePackings/Frozen/Lemma52DualPolytope.lean#L14) | as printed | this repository |  |
| [Theorem 6.1](paper/rw-spheres.tex#L1791): Simple random walk counterexample<br>`theorem:counter-example` | [SpherePackings.Frozen.theorem61_counterexample](SpherePackings/Frozen/Theorem61Counterexample.lean#L26) | as printed | this repository | Non-convergence on the unit ball from the origin; modified packing for `d ≥ 4`. |

Labelled items with no registered statement:

| Paper item | Reason |
|---|---|
| [Remark 1.2](paper/rw-spheres.tex#L385) | A remark citing Berestycki, Theorem 3.26, for GMC measures; not formalized. |
| [Remark 3.4](paper/rw-spheres.tex#L1100) | A remark on adapting the proof to orthodiagonal maps; not formalized. |
| [Assumption D](paper/rw-spheres.tex#L1438) | A hypothesis, not a result: formalized as printed, for any nearest-neighbour walks, as the definition `SpherePackings.AssumptionD`, which is the hypothesis of Theorem 4.1 and Proposition 4.2 (the existence of the discrete Dirichlet solutions is not assumed, and (4.2) is required of every solution). `SpherePackings.TilingAssumptionD` is a localized variant for orthogonal tilings, used by an earlier tiling proof. The domain `D` of Assumption D need not be the domain of a tiling: the conductance walks on lattice Voronoi tilings of the ball of radius 2 satisfy Assumption D as printed with `D` the unit ball (`theorem41_hypotheses_satisfiable`). |

Supporting statements that establish properties of the formal model:

| Role | Lean statement |
|---|---|
| The open unit ball is a Lipschitz domain in the sense of `IsLipschitzDomain`. | [SpherePackings.isLipschitzDomain_ball](SpherePackings/Support/Guards/LipschitzBall.lean) |
| The lattice `h ℤ^d` satisfies `GoodVoronoi` on every bounded set (its cells are cubes). | [SpherePackings.Voronoi.goodVoronoi_grid](SpherePackings/Support/Guards/LatticeVoronoi.lean) |
| The hypotheses of Theorems A and B are satisfiable: lattice Voronoi tilings of a ball, with the collar, (1.3) and (II). | [SpherePackings.exists_lattice_tilingSequence](SpherePackings/Support/Guards/LatticeTilings.lean) |
| The localized Assumption D (`TilingAssumptionD`, used by the earlier tiling proof of Theorem 4.1) holds under (1.3) and (I), (II) or (III), by Theorem B(a). | [SpherePackings.tilingAssumptionD_of_paperRegularity](SpherePackings/Support/Section4/AssumptionD.lean) |
| Assumption D as printed holds for the conductance walks on lattice Voronoi tilings with nearest vertices (by Theorem B(a)); with the unit ball and a standard Brownian law, the hypotheses of Theorem 4.1 and Proposition 4.2 are satisfiable. | [SpherePackings.theorem41_hypotheses_satisfiable](SpherePackings/Support/Guards/AssumptionDLattice.lean) |
| A standard Brownian law exists (leobon12). | [BouRabeeGwynne.isStandardBrownianLaw_euclideanWienerLaw](BouRabeeGwynne/EuclideanWienerLaw.lean) |
| Lemma 2.1 applies to a star whose centre, a boundary vertex, has infinite degree. | [SphereSBPALocal.InfiniteStarCheck.checked_identity](SpherePackings/Support/Guards/Lemma21InfiniteStar.lean) |

<!-- NODE-TABLE-END -->
