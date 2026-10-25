module

/-
Theorem 3.3 of rw-spheres.tex, the bound, frozen.

Paper statement, `rw-spheres.tex:1030-1049` (label `theorem:2d`): in the plane,
`sup_{V[U]} |h_D - h_C| ≤ inf_{k > 0} (6 k M ε vol(Û) + 2 (√2 k⁻¹ + ε) L)`, with
`ε = sup_{V̄[U]} diam(P_v)`, `L = sup_Û |∇ h_C|`, `M = sup_Û |∇² h_C|`.

Corrected statement (`rw-spheres-corrected.tex`, Corrections 4 and 8 and the revised Theorem 3.3,
corrections items 1, 5 and 6): `sup_{V[U]} |h_D - h_C| ≤ 3 M₀ ε² + inf_{k > 0} (6 k M ε vol(Û) +
(M/2)(√2 k⁻¹ + ε)²)`, where `M₀` bounds the Hessian on the cells of `V̄[U]` and `M ≥ M₀` the finite
Taylor remainder `|h(w) - h(v) - ∇h(v)·(w - v)| ≤ (M/2) ‖w - v‖²` on the internal edges (both
endpoints in `V[U]`); the cells of `V[U]` are complete (finitely many neighbours, boundary covered
by the cells of the neighbours); `h_C` is `C²` on an open set containing the cells of `V̄[U]` and
harmonic on the cells of `V[U]` (the corrected paper asks harmonicity on `Û`, all cells of `V̄[U]`:
a stronger statement).  No local oscillation or Lipschitz condition.  The printed theorem is false
without completeness (check G4 in `GAP-CHECKS.md`: on the square grid of mesh `1/n`, `n` odd, of `D
= [0,1] × [0,2]`, with `U = (0,1) × (1/2, 3/2)` and `h_C = cosh(π(x - 1/2)) cos(π(y - 1))`, the
discrete solution is `0` while `h_C → 1` near the centre, and the printed bound tends to `0`).
Whether the published linear bound holds is not settled here, and whether the theorem holds with the
published cell Hessian constant alone is open.  Proof: the error is split, after leobon12, into a
boundary correction of size at most `2 M₀ ε²` and a corrected error whose energy gives good
rectangles (Lemma 3.1) and which is controlled inside them by the subharmonic comparison with `(M/2)
‖· - v‖²`.
-/
public import SpherePackings.Support.Section3.PlanarInternal

@[expose] public section

open BouRabeeGwynne BouRabeeGwynne.OrthogonalTiling SpherePackings
open scoped MeasureTheory Laplacian

-- FROZEN-STATEMENT-BEGIN
theorem SpherePackings.Frozen.theorem33_planar (T : OrthogonalTiling 2) (U : Set (Euc 2))
    [Fintype (T.closedVertices U)]
    (hcomplete : ∀ v ∈ T.interiorVertices U, CompleteCell T v)
    {W : Set (Euc 2)} (hW : IsOpen W) {hC : Euc 2 → ℝ} (hC2 : ContDiffOn ℝ 2 hC W)
    (hcells : ∀ v ∈ T.closedVertices U, (T.cell v).carrier ⊆ W)
    (hharm : ∀ v ∈ T.interiorVertices U, ∀ x ∈ (T.cell v).carrier, Δ hC x = 0)
    {M₀ M ε : ℝ} (hM₀ : 0 ≤ M₀) (hM₀M : M₀ ≤ M) (hε : 0 ≤ ε)
    (hdiam : ∀ v ∈ T.closedVertices U, Metric.diam (T.cell v).carrier ≤ ε)
    (hHcell : ∀ v ∈ T.closedVertices U, ∀ x ∈ (T.cell v).carrier,
      ‖fderiv ℝ (fderiv ℝ hC) x‖ ≤ M₀)
    (hTaylor : ∀ v ∈ T.interiorVertices U, ∀ w ∈ T.interiorVertices U, T.adj v w →
      |hC (T.pos w) - hC (T.pos v) - (fderiv ℝ hC (T.pos v)) (T.pos w - T.pos v)| ≤
        M / 2 * ‖T.pos w - T.pos v‖ ^ 2)
    (hD : T.V → ℝ) (hsol : T.SolvesDirichlet U (fun v => hC (T.pos v)) hD) :
    ∀ k : ℝ, 0 < k → ∀ v ∈ T.interiorVertices U, |hD v - hC (T.pos v)| ≤
      3 * M₀ * ε ^ 2 + (6 * k * M * ε * (MeasureTheory.volume (⋃ w ∈ T.closedVertices U,
        (T.cell w).carrier)).toReal + M / 2 * (Real.sqrt 2 / k + ε) ^ 2)
-- FROZEN-STATEMENT-END
:= SpherePackings.planar_dirichlet_bound_internal T U hcomplete hW hC2 hcells hharm hM₀ hM₀M hε hdiam hHcell hTaylor hD hsol
