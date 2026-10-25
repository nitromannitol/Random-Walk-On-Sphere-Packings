module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/Section3Boxes.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.Section3LocalMaximum
public import BouRabeeGwynne.Section3Iteration
public import BouRabeeGwynne.TilingNetwork
public import BouRabeeGwynne.LocalGeometry
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.Convex.Topology

@[expose] public section

/-! Cell-contained boxes and the actual local maximum principle. -/

open scoped Classical ENNReal

namespace BouRabeeGwynne

/-- A region cut out by lower and upper levels of continuous linear functionals.
Coordinate functionals give the rectangles used in the planar argument. -/
def slabIntersection {d : ℕ} {I : Type*} (L : I → Euc d →L[ℝ] ℝ)
    (lower upper : I → ℝ) : Set (Euc d) :=
  {x | ∀ i, lower i < L i x ∧ L i x < upper i}

namespace ConvexPolytope

lemma exists_cut_of_not_subset {d : ℕ} (P : ConvexPolytope d) {I : Type*}
    (L : I → Euc d →L[ℝ] ℝ) (lower upper : I → ℝ)
    {z : Euc d} (hz : z ∈ P.carrier) (hzbox : z ∈ slabIntersection L lower upper)
    (hnot : ¬ P.carrier ⊆ slabIntersection L lower upper) :
    ∃ i, ∃ x ∈ P.carrier, L i x = lower i ∨ L i x = upper i := by
  obtain ⟨p, hp, hpbox⟩ := Set.not_subset.mp hnot
  have hi : ∃ i, ¬ (lower i < L i p ∧ L i p < upper i) := by
    simpa only [slabIntersection, Set.mem_setOf_eq, not_forall] using hpbox
  obtain ⟨i, hi⟩ := hi
  by_cases hlo : L i p ≤ lower i
  · obtain ⟨x, hx, hxi⟩ := P.convex.isPreconnected.intermediate_value hp hz
      (L i).continuous.continuousOn ⟨hlo, (hzbox i).1.le⟩
    exact ⟨i, x, hx, Or.inl hxi⟩
  · have hhi : upper i ≤ L i p := by
      by_contra h
      exact hi ⟨lt_of_not_ge hlo, lt_of_not_ge h⟩
    obtain ⟨x, hx, hxi⟩ := P.convex.isPreconnected.intermediate_value hz hp
      (L i).continuous.continuousOn ⟨(hzbox i).2.le, hhi⟩
    exact ⟨i, x, hx, Or.inr hxi⟩

end ConvexPolytope

namespace OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

def cellsContainedInterior (R : Set T.V) (A : Set R) (S : Set (Euc d)) : Set R :=
  {v | v ∈ A ∧ (T.cell v).carrier ⊆ S}

lemma cellsContainedInterior_subset (R : Set T.V) (A : Set R) (S : Set (Euc d)) :
    T.cellsContainedInterior R A S ⊆ A := fun _ h => h.1

lemma boundary_cell_meets_cut (R : Set T.V) [Fintype R] (A : Set R)
    {I : Type*} (L : I → Euc d →L[ℝ] ℝ) (lower upper : I → ℝ)
    {w : R} (hw : w ∈ (T.finiteNetwork R).externalBoundary
      (T.cellsContainedInterior R A (slabIntersection L lower upper))) (hwA : w ∈ A) :
    ∃ i, ∃ x ∈ (T.cell w).carrier, L i x = lower i ∨ L i x = upper i := by
  obtain ⟨v, hv, ha⟩ := hw.2
  have hvw : T.adj v w := T.conductanceReal_pos_iff.mp ha
  obtain ⟨z, hzv, hzw⟩ := hvw.2.1
  apply (T.cell w).exists_cut_of_not_subset L lower upper hzw (hv.2 hzv)
  intro hsub
  exact hw.1 ⟨hwA, hsub⟩

lemma boundary_cell_dist_le_box_diameter (R : Set T.V) [Fintype R]
    (A : Set R) (S : Set (Euc d)) (hmesh : T.mesh ≠ ∞) {D : ℝ}
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ D)
    {v w : R} (hvS : T.pos v ∈ S)
    (hw : w ∈ (T.finiteNetwork R).externalBoundary
      (T.cellsContainedInterior R A S)) :
    dist (T.pos w) (T.pos v) ≤ T.mesh.toReal + D := by
  obtain ⟨u, hu, ha⟩ := hw.2
  have huw : T.adj u w := T.conductanceReal_pos_iff.mp ha
  obtain ⟨z, hzu, hzw⟩ := huw.2.1
  calc
    _ ≤ dist (T.pos w) z + dist z (T.pos v) := dist_triangle _ _ _
    _ ≤ T.mesh.toReal + D := add_le_add
      (by simpa only [dist_comm] using T.toTilingData.dist_pos_le_mesh hzw hmesh)
      (hdiam z (hu.2 hzu) (T.pos v) hvS)

/-- Good cut lines and continuity on nearby marked points control the error
inside the box. This is the maximum-principle stage of the planar proof. -/
theorem error_le_of_good_box (R : Set T.V) [Fintype R] (A : Set R)
    (haccess : (T.finiteNetwork R).BoundaryAccessible A)
    (h g : R → ℝ) (hsol : (T.finiteNetwork R).SolvesDirichlet A g h)
    {I : Type*} (L : I → Euc d →L[ℝ] ℝ) (lower upper : I → ℝ)
    {η ω D : ℝ} (hη : 0 ≤ η) (hω : 0 ≤ ω)
    (hgood : ∀ w ∈ A, (∃ i, ∃ x ∈ (T.cell w).carrier,
      L i x = lower i ∨ L i x = upper i) → |h w - g w| ≤ η)
    (hmesh : T.mesh ≠ ∞)
    (hdiam : ∀ x ∈ slabIntersection L lower upper,
      ∀ y ∈ slabIntersection L lower upper, dist x y ≤ D)
    {v : R} (hvA : v ∈ A) (hvS : T.pos v ∈ slabIntersection L lower upper)
    (hmod : ∀ w : R, dist (T.pos w) (T.pos v) ≤ T.mesh.toReal + D →
      |g w - g v| ≤ ω) : |h v - g v| ≤ η + ω := by
  let B := T.cellsContainedInterior R A (slabIntersection L lower upper)
  by_cases hvB : v ∈ B
  · have hBA : B ⊆ A := T.cellsContainedInterior_subset R A _
    have hboundary : ∀ w ∈ (T.finiteNetwork R).externalBoundary B,
        |h w - g w| ≤ η := by
      intro w hw
      by_cases hwA : w ∈ A
      · exact hgood w hwA (T.boundary_cell_meets_cut R A L lower upper hw hwA)
      · simpa only [hsol.2 w hwA, sub_self, abs_zero] using hη
    exact (T.finiteNetwork R).harmonic_error_le_boundary_error_add_oscillation B
      ((T.finiteNetwork R).boundaryAccessible_mono hBA haccess) h g
      (fun w hw => hsol.1 w (hBA hw)) hboundary hvB
      (fun w hw => hmod w
        (T.boundary_cell_dist_le_box_diameter R A _ hmesh hdiam hvS hw))
  · have hcut := (T.cell v).exists_cut_of_not_subset L lower upper
      (interior_subset (T.pos_mem_interior v)) hvS
      (fun hsub => hvB ⟨hvA, hsub⟩)
    exact (hgood v hvA hcut).trans (le_add_of_nonneg_right hω)

end OrthogonalTiling
end BouRabeeGwynne
