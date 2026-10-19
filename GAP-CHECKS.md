# Gap checks

A claim that the paper has a gap, or that a printed statement is false, is checked here before it
is recorded as fact or used to justify a correction, when it rests on informal reasoning and
affects the formalization.  Each claim gets one run of Codex (`gpt-6.1-sol`, reasoning effort
`max`, read-only sandbox) with a short prompt that quotes the relevant lines of
`paper/rw-spheres.tex` and asks it to refute the claim first: repair the printed proof, or show
that the counterexample fails the paper's definitions.  Prompts and answers are in
[`ledger/gap-checks/`](ledger/gap-checks/).

Until a claim is confirmed it is only **suspected**, and it is labelled so wherever it appears.
Corrections backed by a counterexample proved in Lean are not re-checked.

| Id | Claim | Verdict | Consequence |
|---|---|---|---|
| [G1](ledger/gap-checks/G1.md) | The proof of Theorem 3.7 has a gap at `rw-spheres.tex:1371` ("we may replace every instance of `ε` in Step 3 of the previous proof by `δ_j`"): applied on `U'_i`, Propositions 2.6 and 3.2 involve the cells of `∂S'_i`, whose diameters are not bounded by `δ_i` | **Confirmed** (2026-10-18).  Proposition 3.2 gives only `vol(Y'_i) ≤ 3 η_i Σ_i / (A δ_i)` with `η_i` the largest diameter over `S'_i ∪ ∂S'_i`; neither the trimming nor the decay hypothesis controls `∂S'_i`; the interior-only strengthening of Proposition 3.2 is false (a singleton cell of a rectangular tiling with `h_C = x² − y²`).  Codex expects Theorem 3.7 to be true, with a proof of the rate needing an additional boundary-control argument or a modified iteration | The printed proof cannot be followed (also, "smallest" at line 1371 is a typo for "largest", line 1360).  The rate is proved through leobon12's corrected iteration, which controls the cells of the boundary of the bad set (`SpherePackings/Support/Section3/DecayInternal.lean`), as in the corrected paper: with the Hessian bound on the cells and the finite Taylor inequality on the internal edges only |
| [G2](ledger/gap-checks/G2.md) | Proposition 2.6 is false as printed: in a planar Voronoi tiling with four cocircular sites `v, y, z, w` at angles `−α, −α/3, α/3, α`, `V[U] = {v}` and `h_C` the real part of a function with `F'' = R^{-1/2}(ζ − c)^{1/2}`, cut through the thin cell `P_z ⊄ Û`, the energy tends to `∞` as `α → 0` while the right side stays bounded | **Confirmed** (2026-10-18).  Codex completes the configuration to a locally finite Voronoi tiling of `ℝ²` (radial copies of the four sites at radius `L > 4ρ`, four cardinal sites, a lattice outside `B_{10L}`), with the cut avoiding `Û`; with `c_α = (ρ/4) e^{i(π/2 − α/3)}` and `F = (4/15) R^{-1/2} (ζ − c_α)^{5/2}`, `J = (4√2/15) R^{-1/2} (3ρ/4)^{5/2} > 0`, `f(v) → J (L − ρ)/(4L + 2ρ)` and `D(f, U) ≍ α⁻¹`, while the right side stays bounded.  This holds also when `C²(Û)` means `C²` on a neighbourhood of `Û`.  Smallest repair it proposes: a `C²` extension of `h_C` to every edge segment `[v, w]`, `e ∈ E[Ū]`, with the same Hessian bound `M` there (harmonicity only on `Û`), or the segments lying in `Û` | Proposition 2.6 is false as printed.  As in the corrected paper, it is registered with `M` bounding the cell Hessian and the finite Taylor remainder at one active endpoint of each edge of `E[Ū]`, which a Hessian bound on the edge segments implies (README, correction 5).  Theorems 3.3, 3.6 and 3.7 need the Taylor inequality only on internal edges; whether they hold with the cell Hessian alone is open |
| [G3](ledger/gap-checks/G3.md) | Lemma 5.1(b) (i) holds as printed for `d ≤ 3`: with `δ = 1/10` and `t = (1/2 + δ) k√d + 0.05 k`, a point `y` of `𝒞_s` farther than `t` from `s` gives, through the grid point nearest to the point at distance `t` on `[s, y]`, a point of `S` closer to `y` than `s`; (ii) is false for every `d ≥ 14`: `k = 1`, `s = (0.01, 1/2, …, 1/2)`, `U = B_{0.01}(s)`, `S = {s} ∪ (ℤ^d ∩ B_2(U))` | **Confirmed**, both parts (2026-10-19).  (i) holds, with the bound `1.956 k` in place of `1.955 k` (any bound below `2k` suffices), also when `‖y - s‖ = t`.  (ii) The printed cube hypothesis holds for every `δ`, since `B_2(U)` is the closed neighbourhood (`rw-spheres.tex:1432-1435`) and every grid point in it has first coordinate at most `0`; `S` is finite, hence locally finite; and the ray `s + t e_1` lies in `𝒞_s`.  Adding the integer sites outside radius `12√d` makes every cell bounded and keeps the counterexample.  Codex also notes that the coordinate-direction witnesses of the printed proof (`rw-spheres.tex:1673`) are not supplied by the hypothesis | Lemma 5.1(b) is registered as in the corrected paper, with constants `δ(d) ∈ (0, 1)` and `R(d) ≥ 2` (proved with `δ = 1/10` and `R = max(2, 1.1√d)`, so `R = 2` for `d ≤ 3`).  The corrected paper also refutes the printed radius for `d = 13` (`s = (-1/100, 1/2, …, 1/2)`, `U = B_{1/1000}(s)`, the point `s + 5√d e_1`) |
| [G4](ledger/gap-checks/G4.md) | Theorems 3.3, 3.6 and 3.7 are false as printed without the hypothesis that the cells of `V[U]` lie in the interior of `D`: the square grid of mesh `1/n` (`n` odd) of `D = [0,1] × [0,2]`, `U = (0,1) × (1/2, 3/2)`, `h_C = cosh(π(x - 1/2)) cos(π(y - 1))` | **Confirmed** for all three (2026-10-19).  `D` is any subset (line 226); an unshared facet creates no boundary vertex (lines 563-564), so `∂V[U]` is the two rows at `y = 1/2, 3/2`, where `h_C = 0`, and `h_D ≡ 0`, while `|h_D - h_C| = cos(π/(2n)) → 1` at `(1/2, 1 + 1/(2n))`.  `Û = [0,1] × [1/2 - 1/(2n), 3/2 + 1/(2n)]`, `ε = √2/n`, and `L`, `M` stay bounded.  Theorem 3.3: `k = ε^{-1/2}` makes the bound `O(ε^{1/2})`; Theorem 3.6: `K = 3`, `𝒜 = ∅`; Theorem 3.7: `vol(Q_e) = 1/(2n²)` and `diam(P_v) = 2 vol(Q_e)^{1/2}`, so `F = 2`, `α = 1/2`.  The printed proofs omit the flux through unshared facets (`rw-spheres.tex:850-854`) | Completeness of the cells of `V[U]` (the corrected paper's hypothesis) in Theorems 3.3, 3.6 and 3.7 is a correction with a counterexample (README, correction 1) |

## Confirmed by inspection

- **Theorem 3.6, Step 2** (`rw-spheres.tex:1222-1250`): the printed Step 2 loses a term `ε L` at the
  exit cell.  Display (1241) bounds `|h_C(x) - h_C(y)|` on `Q̄ = Q ∪ ∂Q` by `∑_{v ∈ Q} diam(P_v) L`,
  but reaching an exit vertex `w ∈ ∂Q` also crosses `P_w`, which adds up to `diam(P_w) L ≤ ε L`, so
  (1252) should carry `+ ε L`.  Confirmed by inspection; the registered statement (the corrected
  paper's) is proved with the exit cell handled by a separate comparison (`CORRESPONDENCE.md`,
  Theorem 3.6).
- **Theorem 6.1 in dimension at least four** (`rw-spheres.tex:1791-1794` and the construction
  after it): in the printed packing, a small middle sphere has centre
  `(√7/2, 1/2 + y₂, 1/2 + y₃, y₄, …)` with `y ∈ ℤ^d`, and a big middle sphere has centre
  `(0, a₂, …)` with every `a_i` even.  If some `y_i` with `i ≥ 4` is odd, the squared distance
  between the centres is at least `7/4 + 1/4 + 1/4 + 1 = 13/4 > 9/4`, and big spheres with
  `x₁ ≤ −2` are farther still; so that sphere touches no big sphere, and the printed count of one
  big middle neighbour fails.  Confirmed by inspection in the independent review.  The registered
  statement, like the printed one, does not ask for a covering packing; the proof places the
  small spheres at even coordinates beyond the third (README, correction 9).
- **Theorem A from Theorem 4.1** (`rw-spheres.tex:1490-1491`): the one-line derivation applies
  Theorem B to the sets `B_r(x) ∩ B_δ(D)`, which need not be domains.  The corrected paper spells
  out this transfer for arbitrary finite active sets (its Correction 12), and Theorem A is proved
  here directly (leobon12).

## Suspected, not checked

None at present.
