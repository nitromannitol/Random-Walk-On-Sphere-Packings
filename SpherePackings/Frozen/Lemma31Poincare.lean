module

/-
Lemma 3.1 of rw-spheres.tex, frozen.

Paper statement, `rw-spheres.tex:937-943` (label `lemma:ptype-inequality`): for `f` zero on
`∂V[U]`, the `(d-1)`-volume of the set of `y ∈ π_j(U)` with
`max_{v ∈ L_y^j[U]} |f(v)| > k (D(f, U) ∑_{e ∈ E[Ū]} d vol_d(Q_e))^{1/2}` is at most `1/k`.

On a finite set `R` of vertices containing the neighbours of `A`: columns in any direction `e ≠ 0`;
the bad set is the set of `y` in the projection of the cell of a vertex of `A` with `|f| > τ`;
`incidentEnergy` is `D(f, U)` and `incidentMass` is `∑ ‖e‖ vol_{d-1}(H_e)`.

Corrected statement (`rw-spheres-corrected.tex`, Correction 4): the cells of `A` are complete.  The
published lemma is false without it: for two unit squares in a row and `U` containing both
centres, `∂V[U]` is empty, and `f = 1` has `D(f, U) = 0` while the bad set at threshold `0` is
`π_1(U)`, of positive length.  Proved from leobon12's column lemmas, adapted to complete cells.
-/
public import SpherePackings.Support.Complete.Columns

@[expose] public section

open scoped Classical BigOperators MeasureTheory ENNReal
open MeasureTheory BouRabeeGwynne BouRabeeGwynne.OrthogonalTiling SpherePackings

-- FROZEN-STATEMENT-BEGIN
theorem SpherePackings.Frozen.lemma31_poincare {d : ℕ} (hd : 1 ≤ d) (T : OrthogonalTiling d)
    (e : Euc d) (he : e ≠ 0) (R : Set T.V) [Fintype R] (A : Set R)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    (hcomplete : ∀ v ∈ A, CompleteCell T v)
    (f : T.V → ℝ) (hzero : ∀ v : R, v ∉ A → f v = 0)
    {k : ℝ} (hk : 0 < k) :
    μHE[d - 1] (T.columnBadSet R A e he f
      (k * (Real.sqrt (T.incidentEnergy R A f) * Real.sqrt (T.incidentMass R A)))) ≤
      ENNReal.ofReal (1 / k)
-- FROZEN-STATEMENT-END
:= SpherePackings.column_poincare_measure_bound_of_complete hd T e he R A hneighbors hcomplete f hzero hk
