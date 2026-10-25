module

/-
Theorem 3.7 of rw-spheres.tex, frozen.

Paper statement, `rw-spheres.tex:1314-1340` (label `theorem:generaldim-decay`): under
`diam(P_v) ≤ F sup_{e = (w, v)} vol_d(Q_e)^α` for `v ∈ V[U]`, there is `C = C(U, F, α)` such that
for `ε < (C M)⁻¹`, `sup_{V[U]} |h_D - h_C| ≤ C M ε log(1/ε)`, with `ε = sup_{V̄[U]} diam(P_v)` and
`M = sup_Û |∇² h_C| ∨ 1`.

Corrected statement (`rw-spheres-corrected.tex`, Corrections 4, 8 and 11; Theorem 3.7 with `M =
M_U°(h_C) ∨ 1`): the cells of `V[U]` are complete (finitely many neighbours, boundary covered by the
cells of the neighbours); `h_C` is `C²` on an open set containing the cells of `V̄[U]` and harmonic
on the cells of `V[U]` (the corrected paper asks harmonicity on `Û`, all cells of `V̄[U]`: a
stronger statement); `M ≥ 1` bounds the Hessian on the cells of `V̄[U]` and the finite Taylor
remainder `|h(w) - h(v) - ∇h(v)·(w - v)| ≤ (M/2) ‖w - v‖²` on the internal edges (both endpoints in
`V[U]`).  The printed theorem is false without completeness (check G4 in `GAP-CHECKS.md`: on the
square grid of mesh `1/n`, `n` odd, of `D = [0,1] × [0,2]`, with `U = (0,1) × (1/2, 3/2)` and `h_C =
cosh(π(x - 1/2)) cos(π(y - 1))`, the discrete solution is `0` while `h_C → 1` near the centre, and
the printed bound tends to `0`).  Whether the theorem holds with the published cell Hessian constant
alone is open.  The rate has an explicit constant (`hypIIIRateConstant`, in `d`, `F`, `α` and a
bound `R₀` on `‖x‖` over `U`); the smallness condition is `12 M ε ≤ 1` and `ε ≤ 1/2`, an instance of
the paper's `ε < (C M)⁻¹`.  The printed proof has a gap at `rw-spheres.tex:1371` (check G1,
`GAP-CHECKS.md`); the proof here uses leobon12's corrected iteration, whose boundary-edge Taylor
remainders are bounded by the cell Hessian alone.  The decay hypothesis is in leobon12's form
`diam(P_v) ≤ F sup_w (‖w - v‖ vol_{d-1}(P_v ∩ P_w))^α`, equivalent to the printed one by Lemma 2.4
(`F` scaled by `d^α`).
-/
public import SpherePackings.Support.Section3.DecayInternal

@[expose] public section

open BouRabeeGwynne BouRabeeGwynne.OrthogonalTiling SpherePackings
open scoped ENNReal MeasureTheory Laplacian

-- FROZEN-STATEMENT-BEGIN
theorem SpherePackings.Frozen.theorem37_rate {d : ℕ} (hd : 1 ≤ d) (T : OrthogonalTiling d) (U : Set (Euc d))
    [Fintype (T.closedVertices U)]
    (hcomplete : ∀ v ∈ T.interiorVertices U, CompleteCell T v)
    {R₀ : ℝ} (hR₀ : 0 ≤ R₀) (hUR : ∀ x ∈ U, ‖x‖ ≤ R₀)
    {W : Set (Euc d)} (hW : IsOpen W) {hC : Euc d → ℝ} (hC2 : ContDiffOn ℝ 2 hC W)
    (hcells : ∀ v ∈ T.closedVertices U, (T.cell v).carrier ⊆ W)
    (hharm : ∀ v ∈ T.interiorVertices U, ∀ x ∈ (T.cell v).carrier, Δ hC x = 0)
    {M ε : ℝ} (hM : 1 ≤ M)
    (hdiam : ∀ v ∈ T.closedVertices U, Metric.diam (T.cell v).carrier ≤ ε)
    (hHcell : ∀ v ∈ T.closedVertices U, ∀ x ∈ (T.cell v).carrier,
      ‖fderiv ℝ (fderiv ℝ hC) x‖ ≤ M)
    (hTaylor : ∀ v ∈ T.interiorVertices U, ∀ w ∈ T.interiorVertices U, T.adj v w →
      |hC (T.pos w) - hC (T.pos v) - (fderiv ℝ hC (T.pos v)) (T.pos w - T.pos v)| ≤
        M / 2 * ‖T.pos w - T.pos v‖ ^ 2)
    {α : ℝ} (hα : 0 < α) {F : ℝ≥0∞} (hF : F ≠ ⊤)
    (hreg : ∀ v ∈ T.interiorVertices U, (T.cell v).diamENN ≤ F * T.incidentScale α v)
    (hsmall : 12 * M * ε ≤ 1) (hε2 : ε ≤ 1 / 2)
    (hD : T.V → ℝ) (hsol : T.SolvesDirichlet U (fun v => hC (T.pos v)) hD) :
    ∀ v ∈ T.interiorVertices U, |hD v - hC (T.pos v)| ≤
      hypIIIRateConstant (12 * ((d : ℝ) * ((R₀ + 1) - -(R₀ + 1))) + 1)
          (F.toReal * (2 * ((d : ℝ) *
            (μHE[d] (Metric.closedBall (0 : Euc d) (R₀ + 1))).toReal)) ^ α) ((1 / 2 : ℝ) ^ α) *
        (3 * M) * ε * Real.log (1 / ε)
-- FROZEN-STATEMENT-END
:= SpherePackings.generaldim_decay_rate_internal hd T U hcomplete hR₀ hUR hW hC2 hcells hharm hM hdiam hHcell hTaylor hα hF hreg hsmall hε2 hD hsol
