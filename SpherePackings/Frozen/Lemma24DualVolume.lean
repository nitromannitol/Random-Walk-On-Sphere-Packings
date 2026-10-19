/-
Lemma 2.4 of rw-spheres.tex, frozen.

Paper statement, `rw-spheres.tex:739-744` (label `lemma:geometry-bound`): for each edge
`e = (w, v)`, `‖w - v‖ vol_{d-1}(H_e) = d vol_d(Q_e)`, where `Q_e = conv(w, H_e) ∪ conv(v, H_e)`.

leobon12's theorem; `dualVolume` is the volume of `dualPolytope v w`, the union of the two
pyramids over the contact.
-/
import BouRabeeGwynne.DualVolume

open scoped ENNReal MeasureTheory
open MeasureTheory BouRabeeGwynne

-- FROZEN-STATEMENT-BEGIN
theorem SpherePackings.Frozen.lemma24_dual_volume {d : ℕ} (T : BouRabeeGwynne.OrthogonalTiling d) (hd : 1 ≤ d) {v w : T.V} (hvw : T.adj v w) :
    ‖T.pos w - T.pos v‖ * (T.facetVolume v w).toReal =
      (d : ℝ) * (T.toTilingData.dualVolume v w).toReal
-- FROZEN-STATEMENT-END
:= BouRabeeGwynne.OrthogonalTiling.edgeLength_mul_facetVolume_eq_dim_mul_dualVolume T hd hvw
