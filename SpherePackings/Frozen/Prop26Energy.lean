/-
Proposition 2.6 of rw-spheres.tex, frozen.

Paper statement, `rw-spheres.tex:822-844` (label `prop:energy-bound`):
`D(h_D - h_C, U) ≤ 9 M² ε² ∑_{e ∈ E[Ū]} d vol_d(Q_e)`, with `ε = sup_{V̄[U]} diam(P_v)` and
`M = sup_{Û} |∇² h_C|`, for `h_C ∈ C²(Û)` harmonic on `Û`.

Corrected statement (`rw-spheres-corrected.tex`, Corrections 4 and 8): the cells of `V[U]` are
complete; `h_C` is `C²` on an open set containing the cells of `V̄[U]` and harmonic on the cells of
`V[U]`; `M` bounds the Hessian on the cells of `V[U]` and, for each edge of `E[Ū]`, the finite
Taylor remainder at one active endpoint, `|h(w) - h(v) - ∇h(v)·(w - v)| ≤ (M/2) ‖w - v‖²`
(harmonicity and the Hessian bound are asked only on the cells of `V[U]`, not on all cells of
`V̄[U]` as in the corrected paper: a stronger statement).  The
published version is false: without completeness (two unit squares, energy `2`, right side `0`),
and, with complete cells, for a slit-domain harmonic function (the Hessian bound on the cells does
not control the edge segments that leave `Û`; check G2 in `GAP-CHECKS.md`).  A Hessian bound `M`
on the edge segments implies the Taylor condition.  `incidentEnergy` and `incidentMass` sum over
undirected edges, each half the printed directed sum, so the constant `9` is unchanged.  Proved
from leobon12's flux-residual bounds.
-/
import SpherePackings.Support.Section3.EnergyComplete

open BouRabeeGwynne BouRabeeGwynne.OrthogonalTiling SpherePackings
open scoped MeasureTheory Laplacian

-- FROZEN-STATEMENT-BEGIN
theorem SpherePackings.Frozen.prop26_energy {d : ℕ} (hd : 1 ≤ d) (T : OrthogonalTiling d) (U : Set (Euc d))
    [Fintype (T.closedVertices U)]
    (hcomplete : ∀ v ∈ T.interiorVertices U, CompleteCell T v)
    {W : Set (Euc d)} (hW : IsOpen W) {hC : Euc d → ℝ} (hC2 : ContDiffOn ℝ 2 hC W)
    (hcells : ∀ v ∈ T.closedVertices U, (T.cell v).carrier ⊆ W)
    (hharm : ∀ v ∈ T.interiorVertices U, ∀ x ∈ (T.cell v).carrier, Δ hC x = 0)
    {M ε : ℝ} (hM : 0 ≤ M)
    (hdiam : ∀ v ∈ T.closedVertices U, Metric.diam (T.cell v).carrier ≤ ε)
    (hHcell : ∀ v ∈ T.interiorVertices U, ∀ x ∈ (T.cell v).carrier,
      ‖fderiv ℝ (fderiv ℝ hC) x‖ ≤ M)
    (hTaylor : ∀ v w, T.adj v w → v ∈ T.interiorVertices U ∨ w ∈ T.interiorVertices U →
      (v ∈ T.interiorVertices U ∧
        |hC (T.pos w) - hC (T.pos v) - (fderiv ℝ hC (T.pos v)) (T.pos w - T.pos v)| ≤
          M / 2 * ‖T.pos w - T.pos v‖ ^ 2) ∨
      (w ∈ T.interiorVertices U ∧
        |hC (T.pos v) - hC (T.pos w) - (fderiv ℝ hC (T.pos w)) (T.pos v - T.pos w)| ≤
          M / 2 * ‖T.pos v - T.pos w‖ ^ 2))
    (hD : T.V → ℝ) (hsol : T.SolvesDirichlet U (fun v => hC (T.pos v)) hD) :
    T.incidentEnergy (T.closedVertices U) (T.finiteInterior U) (fun v => hD v - hC (T.pos v)) ≤
      9 * M ^ 2 * ε ^ 2 * T.incidentMass (T.closedVertices U) (T.finiteInterior U)
-- FROZEN-STATEMENT-END
:= SpherePackings.harmonic_energy_bound_complete hd T U hcomplete hW hC2 hcells hharm hM hdiam hHcell hTaylor hD hsol
