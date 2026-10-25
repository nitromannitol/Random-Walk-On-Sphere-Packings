module

/-
Theorem B, alternative (b), of rw-spheres.tex, frozen.

Paper statement, `rw-spheres.tex:297-321` (label `theorem:convergence-of-the-dirichlet-problem`),
alternative (b): for a bounded Lipschitz domain `U` with `closure U ⊆ D` and `h_C` harmonic on `U`
and continuous on `closure U`, the discrete harmonic extensions converge uniformly on `V_n[U]`.

Statement of leobon12 (`BouRabeeGwynne.TheoremBPartBStatement`), proved here.  The ambient
collar is `closure U ⊆ interior D`.  The boundary value at an exterior boundary vertex is `h_C` at a
nearest point of `closure U`, for every choice of such points (the printed footnote,
`rw-spheres.tex:305`, "the nearest point in the cell `P_v` for which it is defined", may have no such
point; where it exists, the two statements agree); the statement also asserts that these points lie on the
frontier of `U`, within two meshes of the vertex.
-/
public import SpherePackings.Support.TheoremBPartB.Proof

@[expose] public section

open scoped Topology ENNReal
open BouRabeeGwynne

-- FROZEN-STATEMENT-BEGIN
theorem SpherePackings.Frozen.theoremB_b :
  ∀ (d : ℕ) (G : TilingSequence d) (N : NearestVertexData G)
    (U : Set (Euc d)) (hC : Euc d → ℝ),
    1 ≤ d → IsLipschitzDomain U → Bornology.IsBounded U →
    HasAmbientCollar U G.domain → N.ApproximationCondition → PaperRegularity G →
    IsHarmonicOn hC U → ContinuousOnClosure hC U →
      Nonempty (NearestClosureBoundaryChoices G U) ∧
      ∀ S : NearestClosureBoundaryChoices G U,
        (∀ n v, S.point n v ∈ frontier U) ∧
        (∀ᶠ n in Filter.atTop, ∀ v : (G.tiling n).boundaryVertices U,
          dist ((G.tiling n).pos v) (S.point n v) ≤ 2 * (G.tiling n).mesh.toReal) ∧
        DirichletApproximationTarget G U hC (S.boundaryData hC)
-- FROZEN-STATEMENT-END
:= SpherePackings.theoremB_part_b
