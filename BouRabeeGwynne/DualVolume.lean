module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/DualVolume.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.PyramidVolume
public import BouRabeeGwynne.FacetPyramidHeights
public import BouRabeeGwynne.DualAdditivity

@[expose] public section

open scoped ENNReal MeasureTheory
open MeasureTheory

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

/-- Exact volume of the paper's union of two pyramids, with no assumption that
the marked edge crosses the facet itself. -/
theorem dualVolume_eq (hd : 1 ≤ d) {v w : T.V} (hvw : T.adj v w) :
    T.toTilingData.dualVolume v w = ‖T.pos w - T.pos v‖ₑ * ENNReal.ofReal (1 / (d : ℝ)) *
      T.facetVolume v w := by
  obtain ⟨r, hr, hr1, hbase⟩ := T.exists_facet_height hd hvw
  let e := T.pos w - T.pos v
  have he : e ≠ 0 := sub_ne_zero.mpr (T.toTilingData.pos_injective.ne hvw.1.symm)
  have hfirst := pyramid_volume hd (T.pos v) he (T.toTilingData.facet_compact v w)
    (T.toTilingData.facet_convex v w) hvw.2.1 hr hbase
  have hbase' : T.facet w v ⊆ perpendicularSlice (T.pos w) (-e) (1 - r) := by
    have hrev := perpendicularSlice_reverse (T.pos v) e r
    have hpos : T.pos v + e = T.pos w := by dsimp [e]; abel
    rw [hpos] at hrev
    have hfacet : T.facet w v = T.facet v w := T.toTilingData.facet_symm w v
    rw [hrev, hfacet]
    exact hbase
  have hsecond := pyramid_volume hd (T.pos w) (neg_ne_zero.mpr he)
    (T.toTilingData.facet_compact w v) (T.toTilingData.facet_convex w v) (T.toTilingData.adj_symm hvw).2.1
    (sub_pos.mpr hr1) hbase'
  change μHE[d] (T.toTilingData.cellPyramid v w) =
    ‖e‖ₑ * ENNReal.ofReal (r / (d : ℝ)) * T.facetVolume v w at hfirst
  change μHE[d] (T.toTilingData.cellPyramid w v) =
    ‖-e‖ₑ * ENNReal.ofReal ((1 - r) / (d : ℝ)) * T.facetVolume w v at hsecond
  have harea : T.facetVolume w v = T.facetVolume v w :=
    T.toTilingData.facetVolume_symm w v
  rw [enorm_neg, harea] at hsecond
  rw [T.toTilingData.dualVolume_eq_pyramid_add hd hvw.1, hfirst, hsecond]
  have hdpos : (0 : ℝ) < d := lt_of_lt_of_le zero_lt_one (by exact_mod_cast hd)
  have hsum : ENNReal.ofReal (r / (d : ℝ)) +
      ENNReal.ofReal ((1 - r) / (d : ℝ)) = ENNReal.ofReal (1 / (d : ℝ)) := by
    rw [← ENNReal.ofReal_add (div_nonneg hr.le hdpos.le)
      (div_nonneg (sub_nonneg.mpr hr1.le) hdpos.le)]
    congr 1
    ring
  calc
    _ = ‖e‖ₑ * (ENNReal.ofReal (r / (d : ℝ)) +
        ENNReal.ofReal ((1 - r) / (d : ℝ))) * T.facetVolume v w := by ring
    _ = _ := by rw [hsum]

/-- Lemma 2.4 in real-valued form for the actual geometric dual cell. -/
theorem edgeLength_mul_facetVolume_eq_dim_mul_dualVolume
    (hd : 1 ≤ d) {v w : T.V} (hvw : T.adj v w) :
    ‖T.pos w - T.pos v‖ * (T.facetVolume v w).toReal =
      (d : ℝ) * (T.toTilingData.dualVolume v w).toReal := by
  rw [T.dualVolume_eq hd hvw, ENNReal.toReal_mul, ENNReal.toReal_mul,
    toReal_enorm, ENNReal.toReal_ofReal (by positivity)]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hd)
  field_simp

end BouRabeeGwynne.OrthogonalTiling
