module

/-
Theorem 3.6 of rw-spheres.tex, frozen.

Paper statement, `rw-spheres.tex:1147-1176` (label `theorem:generaldim`): there is `C = C(U)` such
that for `ε < (C M)⁻¹`, `sup_{V[U]} |h_D - h_C| ≤ C M K ε log(1/ε) + D L`, where `ε = sup_{V̄[U]}
diam(P_v)`, `L = sup_Û |∇ h_C|`, `M = sup_Û |∇² h_C| ∨ 1`, `K ≥ 1` is arbitrary, `𝒜 = {v ∈ V̄[U] :
vol_d(P_v) < ε^K}` and `D` is the largest total diameter of a connected component of `𝒜`.

Corrected statement (`rw-spheres-corrected.tex`, Corrections 4, 8 and 11; Theorem 3.6 with `M =
M_U°(h_C) ∨ 1`): the cells of `V[U]` are complete (finitely many neighbours, boundary covered by the
cells of the neighbours); `h_C` is `C²` on an open set containing the cells of `V̄[U]` and harmonic
on the cells of `V[U]` (the corrected paper asks harmonicity on `Û`, all cells of `V̄[U]`: a
stronger statement); `M ≥ 1` bounds the Hessian on the cells of `V̄[U]` and the finite Taylor
remainder `|h(w) - h(v) - ∇h(v)·(w - v)| ≤ (M/2) ‖w - v‖²` on the internal edges (both endpoints in
`V[U]`); `L` bounds the gradient on the cells of `V̄[U]`; `D` bounds the total diameter of every
connected set of cells of `𝒜`.  The printed theorem is false without completeness (check G4 in
`GAP-CHECKS.md`: on the square grid of mesh `1/n`, `n` odd, of `D = [0,1] × [0,2]`, with `U = (0,1)
× (1/2, 3/2)` and `h_C = cosh(π(x - 1/2)) cos(π(y - 1))`, the discrete solution is `0` while `h_C →
1` near the centre, and the printed bound tends to `0`).  Whether the theorem holds with the
published cell Hessian constant alone is open.  The constant is explicit in `d` and a bound `R₀` on
`‖x‖` over `U`; the smallness condition is `12 M ε ≤ 1` and `ε ≤ 1/2`, an instance of the paper's `ε
< (C M)⁻¹`.  The printed proof has gaps (the exit cell, and estimates on boundary cells that the
iteration does not control); the proof here uses leobon12's corrected iteration, whose boundary-edge
Taylor remainders are bounded by the cell Hessian alone, and on a remaining component `Q` bounds the
error by both `L (D_Q + ε)` and `M ρ²`.
-/
public import SpherePackings.Support.Section3.GeneralInternal

@[expose] public section

open BouRabeeGwynne BouRabeeGwynne.OrthogonalTiling SpherePackings
open scoped MeasureTheory Laplacian

-- FROZEN-STATEMENT-BEGIN
theorem SpherePackings.Frozen.theorem36_rate {d : ℕ} (hd : 1 ≤ d) (T : OrthogonalTiling d) (U : Set (Euc d))
    [Fintype (T.closedVertices U)]
    (hcomplete : ∀ v ∈ T.interiorVertices U, CompleteCell T v)
    {R₀ : ℝ} (hR₀ : 0 ≤ R₀) (hUR : ∀ x ∈ U, ‖x‖ ≤ R₀)
    {W : Set (Euc d)} (hW : IsOpen W) {hC : Euc d → ℝ} (hC2 : ContDiffOn ℝ 2 hC W)
    (hcells : ∀ v ∈ T.closedVertices U, (T.cell v).carrier ⊆ W)
    (hharm : ∀ v ∈ T.interiorVertices U, ∀ x ∈ (T.cell v).carrier, Δ hC x = 0)
    {M L ε K Dc : ℝ} (hM : 1 ≤ M) (hK : 1 ≤ K)
    (hdiam : ∀ v ∈ T.closedVertices U, Metric.diam (T.cell v).carrier ≤ ε)
    (hHcell : ∀ v ∈ T.closedVertices U, ∀ x ∈ (T.cell v).carrier,
      ‖fderiv ℝ (fderiv ℝ hC) x‖ ≤ M)
    (hTaylor : ∀ v ∈ T.interiorVertices U, ∀ w ∈ T.interiorVertices U, T.adj v w →
      |hC (T.pos w) - hC (T.pos v) - (fderiv ℝ hC (T.pos v)) (T.pos w - T.pos v)| ≤
        M / 2 * ‖T.pos w - T.pos v‖ ^ 2)
    (hLgrad : ∀ v ∈ T.closedVertices U, ∀ x ∈ (T.cell v).carrier, ‖fderiv ℝ hC x‖ ≤ L)
    (hDc : ∀ Q : Finset T.V,
      (∀ u ∈ Q, u ∈ T.closedVertices U ∧ (T.cell u).volume.toReal < ε ^ K) →
      (∀ a ∈ Q, ∀ b ∈ Q, (adjGraphIn T ↑Q).Reachable a b) →
      ∑ u ∈ Q, Metric.diam (T.cell u).carrier ≤ Dc)
    (hsmall : 12 * M * ε ≤ 1) (hε2 : ε ≤ 1 / 2)
    (hD : T.V → ℝ) (hsol : T.SolvesDirichlet U (fun v => hC (T.pos v)) hD) :
    ∀ v ∈ T.interiorVertices U, |hD v - hC (T.pos v)| ≤
      ((24 * d * (R₀ + 1) + 3) *
          (3 + Real.log (max (2 * d * (μHE[d] (Metric.closedBall (0 : Euc d) (R₀ + 1))).toReal) 1)
            / Real.log 2) / Real.log 2 + (4 * (R₀ + 1 + 1) + 1) / Real.log 2) *
        M * K * ε * Real.log (1 / ε) + Dc * L
-- FROZEN-STATEMENT-END
:= SpherePackings.generaldim_full_internal hd T U hcomplete hR₀ hUR hW hC2 hcells hharm hM hK hdiam hHcell hTaylor hLgrad hDc hsmall hε2 hD hsol
