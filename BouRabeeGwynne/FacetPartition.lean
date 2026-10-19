-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/FacetPartition.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.TripleContact
import BouRabeeGwynne.LocalFacetCoverage
import Mathlib.MeasureTheory.Integral.Bochner.Set

open scoped BigOperators ENNReal MeasureTheory
open MeasureTheory

namespace BouRabeeGwynne.TilingData

variable {d : ℕ} (T : TilingData d)

/-- The finite family of all nonempty contacts, including lower-dimensional ones. -/
noncomputable def contactFinset (v : T.V) (hvD : (T.cell v).carrier ⊆ T.domain) :
    Finset T.V := (T.touchingCells_finite v hvD).toFinset

@[simp] lemma mem_contactFinset {v w : T.V} (hvD : (T.cell v).carrier ⊆ T.domain) :
    w ∈ T.contactFinset v hvD ↔ w ∈ T.touchingCells v := by
  classical
  simp only [contactFinset, Set.Finite.mem_toFinset]

lemma frontier_eq_iUnion_contactFinset (v : T.V)
    (hvD : (T.cell v).carrier ⊆ interior T.domain) :
    frontier (T.cell v).carrier =
      ⋃ w ∈ T.contactFinset v (hvD.trans interior_subset), T.facet v w := by
  simpa only [T.mem_contactFinset] using T.frontier_eq_iUnion_contacts v hvD

/-- Contacts partition the boundary up to surface-null intersections. This is
valid for partial contacts and does not impose a face-to-face tiling condition. -/
theorem frontier_restrict_eq_sum_contacts (hd : 1 ≤ d) (v : T.V)
    (hvD : (T.cell v).carrier ⊆ interior T.domain) :
    (μHE[d - 1]).restrict (frontier (T.cell v).carrier) =
      ∑ w ∈ T.contactFinset v (hvD.trans interior_subset),
        (μHE[d - 1]).restrict (T.facet v w) := by
  classical
  let F := T.contactFinset v (hvD.trans interior_subset)
  have hrep : frontier (T.cell v).carrier = ⋃ w : F, T.facet v w := by
    rw [T.frontier_eq_iUnion_contactFinset v hvD]
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨w, hw, hx⟩
      exact ⟨⟨w, hw⟩, hx⟩
    · rintro ⟨w, hx⟩
      exact ⟨w.val, w.property, hx⟩
  have hdisj : Pairwise (fun w u : F => AEDisjoint (μHE[d - 1])
      (T.facet v w) (T.facet v u)) := by
    intro w u hwu
    have hw := (T.mem_contactFinset (hvD.trans interior_subset)).mp w.property
    have hu := (T.mem_contactFinset (hvD.trans interior_subset)).mp u.property
    exact T.facet_inter_facet_measure_zero hd hw.1.symm hu.1.symm
      (fun heq => hwu (Subtype.ext heq))
  rw [hrep, Measure.restrict_iUnion_ae hdisj]
  · exact Measure.sum_coe_finset F (fun w => (μHE[d - 1]).restrict (T.facet v w))
  · intro w
    exact (T.facet_compact v w).isClosed.measurableSet.nullMeasurableSet

/-- The boundary surface measure is the sum of the actual contact areas. -/
theorem frontier_measure_eq_sum_contacts (hd : 1 ≤ d) (v : T.V)
    (hvD : (T.cell v).carrier ⊆ interior T.domain) :
    μHE[d - 1] (frontier (T.cell v).carrier) =
      ∑ w ∈ T.contactFinset v (hvD.trans interior_subset), T.facetVolume v w := by
  have h := congrArg (fun μ : Measure (Euc d) => μ Set.univ)
    (T.frontier_restrict_eq_sum_contacts hd v hvD)
  simpa only [Measure.restrict_apply_univ, Measure.finsetSum_apply, MeasurableSet.univ,
    facetVolume] using h

/-- Local tiling geometry gives finite codimension-one measure of the whole
cell boundary, with lower-dimensional contacts contributing zero. -/
theorem frontier_measure_ne_top (hd : 1 ≤ d) (v : T.V)
    (hvD : (T.cell v).carrier ⊆ interior T.domain) :
    μHE[d - 1] (frontier (T.cell v).carrier) ≠ ∞ := by
  classical
  rw [T.frontier_measure_eq_sum_contacts hd v hvD]
  apply ENNReal.sum_ne_top.mpr
  intro w hw
  by_cases h : T.adj v w
  · exact T.facetVolume_ne_top h
  · have hne := ((T.mem_contactFinset (hvD.trans interior_subset)).mp hw).1.symm
    rw [T.facetVolume_eq_zero_of_not_adj hd hne h]
    exact ENNReal.zero_ne_top

/-- Integrating over the entire boundary is exactly summing over its contacts.
This is a measure decomposition, not an assumed continuum flux theorem. -/
theorem integral_frontier_eq_sum_contacts (hd : 1 ≤ d) (v : T.V)
    (hvD : (T.cell v).carrier ⊆ interior T.domain) {g : Euc d → ℝ}
    (hg : IntegrableOn g (frontier (T.cell v).carrier) (μHE[d - 1])) :
    ∫ x in frontier (T.cell v).carrier, g x ∂μHE[d - 1] =
      ∑ w ∈ T.contactFinset v (hvD.trans interior_subset),
        ∫ x in T.facet v w, g x ∂μHE[d - 1] := by
  rw [T.frontier_restrict_eq_sum_contacts hd v hvD]
  apply integral_finsetSum_measure
  intro w hw
  have hne := ((T.mem_contactFinset (hvD.trans interior_subset)).mp hw).1.symm
  exact hg.mono_set (T.facet_subset_frontier_left hne)

end BouRabeeGwynne.TilingData
