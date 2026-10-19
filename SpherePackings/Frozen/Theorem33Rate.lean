/-
Theorem 3.3 of rw-spheres.tex, the "in particular" clause, frozen.

Paper statement, `rw-spheres.tex:1050-1053` (label `theorem:2d`): in the plane there is
`C = C(U, M, L) < ∞` with `sup_{V[U]} |h_D - h_C| ≤ C ε^{1/2}`, where `ε = sup_{V̄[U]} diam(P_v)`,
`L = sup_Û |∇ h_C|` and `M = sup_Û |∇² h_C|`.

Corrected statement (`rw-spheres-corrected.tex`, Corrections 4 and 8 and the revised Theorem 3.3,
corrections items 1, 5 and 6): for `0 < ε ≤ 1/2`, `sup_{V[U]} |h_D - h_C| ≤ C ε^{2/3}` (hence `≤ C
ε^{1/2}`), with `C = M (3 + 6 vol(B_{R₀+1}) + (√2 + 1)²/2)`, `R₀` a bound on `‖x‖` over `U`, and `M₀
≤ M` as in the bound (`M₀` the Hessian bound on the cells of `V̄[U]`, `M` the finite Taylor constant
of the internal edges); the cells of `V[U]` are complete (finitely many neighbours, boundary covered
by the cells of the neighbours); `h_C` is `C²` on an open set containing the cells of `V̄[U]` and
harmonic on the cells of `V[U]` (the corrected paper asks harmonicity on `Û`, all cells of `V̄[U]`:
a stronger statement).  The published rate is false with a constant uniform over all meshes: for
large `ε`, a product tiling with a large central cell has an error of order `ε`; the range `ε ≤ 1/2`
is the correction.  The printed theorem is false without completeness (check G4 in `GAP-CHECKS.md`:
on the square grid of mesh `1/n`, `n` odd, of `D = [0,1] × [0,2]`, with `U = (0,1) × (1/2, 3/2)` and
`h_C = cosh(π(x - 1/2)) cos(π(y - 1))`, the discrete solution is `0` while `h_C → 1` near the
centre, and the printed bound tends to `0`).  Whether the rate holds with the published cell Hessian
constant alone is open.  Proof: the bound with `k = ε^{-1/3}`.
-/
import SpherePackings.Support.Section3.PlanarInternal

open BouRabeeGwynne BouRabeeGwynne.OrthogonalTiling SpherePackings
open scoped MeasureTheory Laplacian

-- FROZEN-STATEMENT-BEGIN
theorem SpherePackings.Frozen.theorem33_rate (T : OrthogonalTiling 2) (U : Set (Euc 2))
    [Fintype (T.closedVertices U)]
    (hcomplete : ∀ v ∈ T.interiorVertices U, CompleteCell T v)
    {R₀ : ℝ} (hUR : ∀ x ∈ U, ‖x‖ ≤ R₀)
    {W : Set (Euc 2)} (hW : IsOpen W) {hC : Euc 2 → ℝ} (hC2 : ContDiffOn ℝ 2 hC W)
    (hcells : ∀ v ∈ T.closedVertices U, (T.cell v).carrier ⊆ W)
    (hharm : ∀ v ∈ T.interiorVertices U, ∀ x ∈ (T.cell v).carrier, Δ hC x = 0)
    {M₀ M ε : ℝ} (hM₀ : 0 ≤ M₀) (hM₀M : M₀ ≤ M) (hε : 0 ≤ ε) (hε2 : ε ≤ 1 / 2)
    (hdiam : ∀ v ∈ T.closedVertices U, Metric.diam (T.cell v).carrier ≤ ε)
    (hHcell : ∀ v ∈ T.closedVertices U, ∀ x ∈ (T.cell v).carrier,
      ‖fderiv ℝ (fderiv ℝ hC) x‖ ≤ M₀)
    (hTaylor : ∀ v ∈ T.interiorVertices U, ∀ w ∈ T.interiorVertices U, T.adj v w →
      |hC (T.pos w) - hC (T.pos v) - (fderiv ℝ hC (T.pos v)) (T.pos w - T.pos v)| ≤
        M / 2 * ‖T.pos w - T.pos v‖ ^ 2)
    (hD : T.V → ℝ) (hsol : T.SolvesDirichlet U (fun v => hC (T.pos v)) hD) :
    ∀ v ∈ T.interiorVertices U, |hD v - hC (T.pos v)| ≤
      M * (3 + 6 * (MeasureTheory.volume (Metric.closedBall (0 : Euc 2) (R₀ + 1))).toReal +
        (Real.sqrt 2 + 1) ^ 2 / 2) * ε ^ ((2 : ℝ) / 3)
-- FROZEN-STATEMENT-END
:= SpherePackings.planar_rate_internal T U hcomplete hUR hW hC2 hcells hharm hM₀ hM₀M hε hε2 hdiam hHcell hTaylor hD hsol
