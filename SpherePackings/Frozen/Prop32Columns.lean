/-
Proposition 3.2 of rw-spheres.tex, frozen.

Paper statement, `rw-spheres.tex:980-1001` (label `prop:energy-poincare-bound`): the
`(d-1)`-volume of the set of `y ∈ π_j(U)` with
`max_{v ∈ L_y^j[U]} |h_D(v) - h_C(v)| > 3 k M ε ∑_{e ∈ E[Ū]} d vol_d(Q_e)` is at most `1/k`.

Corrected statement (`rw-spheres-corrected.tex`, Corrections 4 and 8), with the hypotheses of the
corrected Proposition 2.6: complete cells of `V[U]`, and `M` bounding the Hessian on the cells of
`V[U]` and the finite Taylor remainder at one active endpoint of each edge of `E[Ū]` (harmonicity
and the Hessian bound only on the cells of `V[U]`: stronger than the corrected paper).  The
published version is false: without completeness (two unit squares, `U` a small disk around the
centre of one and `h_C(x) = x₁`: `M = 0` while the error at that centre is `1`), and, with complete
cells, for a thin reflected Voronoi configuration in which the Hessian bound on `Û` alone does not
control the edge segments.  Columns in any direction `e ≠ 0`, the bad set being the set of `y` in
the projection of the cell of a vertex of `V[U]` where the error exceeds the threshold.
`incidentMass` is the undirected sum, half the printed one, so the threshold is half the printed one
(stronger).  Proved from leobon12's column lemmas, adapted to complete cells.
-/
import SpherePackings.Support.Section3.EnergyComplete

open BouRabeeGwynne BouRabeeGwynne.OrthogonalTiling SpherePackings
open scoped MeasureTheory Laplacian

-- FROZEN-STATEMENT-BEGIN
theorem SpherePackings.Frozen.prop32_columns {d : ℕ} (hd : 1 ≤ d) (T : OrthogonalTiling d) (U : Set (Euc d))
    [Fintype (T.closedVertices U)]
    (hcomplete : ∀ v ∈ T.interiorVertices U, CompleteCell T v)
    {W : Set (Euc d)} (hW : IsOpen W) {hC : Euc d → ℝ} (hC2 : ContDiffOn ℝ 2 hC W)
    (hcells : ∀ v ∈ T.closedVertices U, (T.cell v).carrier ⊆ W)
    (hharm : ∀ v ∈ T.interiorVertices U, ∀ x ∈ (T.cell v).carrier, Δ hC x = 0)
    {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε)
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
    (hD : T.V → ℝ) (hsol : T.SolvesDirichlet U (fun v => hC (T.pos v)) hD)
    (e : Euc d) (he : e ≠ 0) {k : ℝ} (hk : 0 < k) :
    μHE[d - 1] (T.columnBadSet (T.closedVertices U) (T.finiteInterior U) e he
        (fun v => hD v - hC (T.pos v))
        (3 * k * M * ε * T.incidentMass (T.closedVertices U) (T.finiteInterior U))) ≤
      ENNReal.ofReal (1 / k)
-- FROZEN-STATEMENT-END
:= SpherePackings.harmonic_column_bound_complete hd T U hcomplete hW hC2 hcells hharm hM hε hdiam hHcell hTaylor hD hsol e he hk
