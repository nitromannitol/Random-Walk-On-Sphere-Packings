module

/-
Lemma 2.5 of rw-spheres.tex, frozen.

Paper statement, `rw-spheres.tex:769-784` (label `lemma:easy-global-qe-bounds`): for every bounded
`U ⊆ D`, `U ⊆ ⋃_{e ∈ E[Ū]} Q_e ⊆ Ĝ_U`.

The statement of the corrected paper (`rw-spheres-corrected.tex`, Corrections 4 and 7): when the
cells of `V[U]` are complete (finitely many neighbours, and every boundary point of the cell lies in
the cell of a neighbour), `⋃_{v ∈ V[U]} P_v ⊆ ⋃_{e ∈ E[Ū]} Q_e ⊆ Ĝ_U`.  The published first inclusion
is false (informal counterexample: a small ball inside one square of the unit grid contains no
vertex, so the union is empty), and without completeness the cells need not be covered (two unit
squares).  The second inclusion holds as printed.  Proved from leobon12's cell pyramids.
-/
public import SpherePackings.Support.Complete.Basic

@[expose] public section

open BouRabeeGwynne SpherePackings

-- FROZEN-STATEMENT-BEGIN
theorem SpherePackings.Frozen.lemma25_dual_coverage {d : ℕ} (hd : 1 ≤ d) (T : OrthogonalTiling d) (U : Set (Euc d))
    (hcomplete : ∀ v ∈ T.interiorVertices U, CompleteCell T v) :
    (⋃ v ∈ T.interiorVertices U, (T.cell v).carrier) ⊆
      ⋃ v ∈ T.interiorVertices U, ⋃ w ∈ T.neighbors v, T.toTilingData.dualPolytope v w ∧
    (⋃ v ∈ T.interiorVertices U, ⋃ w ∈ T.neighbors v, T.toTilingData.dualPolytope v w) ⊆
      ⋃ v ∈ T.closedVertices U, (T.cell v).carrier
-- FROZEN-STATEMENT-END
:= SpherePackings.dual_coverage_complete hd T U hcomplete
