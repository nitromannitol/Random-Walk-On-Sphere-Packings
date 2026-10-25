module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/LocalFacetCoverage.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.PaperObjects
public import BouRabeeGwynne.PolytopeBoundary

@[expose] public section

open scoped Topology

namespace BouRabeeGwynne.TilingData

variable {d : ℕ} (T : TilingData d)

/-- An exposed cell boundary point in the covered open region belongs to another
cell. The proof uses local finiteness, so remote cells outside D are irrelevant. -/
theorem frontier_point_mem_other_cell {v : T.V} {x : Euc d}
    (hx : x ∈ frontier (T.cell v).carrier) (hxD : x ∈ interior T.domain) :
    ∃ w : T.V, w ≠ v ∧ x ∈ (T.cell w).carrier := by
  obtain ⟨r, hr, hrD⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (isOpen_interior.mem_nhds hxD)
  let S : Set T.V := {w | ((T.cell w).carrier ∩ Metric.closedBall x r).Nonempty}
  have hS : S.Finite :=
    T.locallyFinite _ (isCompact_closedBall x r) (hrD.trans interior_subset)
  let J : Set T.V := S \ {v}
  let C : Set (Euc d) := ⋃ w ∈ J, (T.cell w).carrier
  have hC : IsClosed C := hS.sdiff.isClosed_biUnion (fun w _ => (T.cell w).compact.isClosed)
  have hcover : Metric.ball x r ∩ (T.cell v).carrierᶜ ⊆ C := by
    intro y hy
    obtain ⟨w, hw⟩ := T.exists_mem_cell (interior_subset (hrD (Metric.ball_subset_closedBall hy.1)))
    have hwv : w ≠ v := by
      intro heq
      subst w
      exact hy.2 hw
    have hwJ : w ∈ J := ⟨⟨y, hw, Metric.ball_subset_closedBall hy.1⟩, hwv⟩
    exact Set.mem_iUnion.mpr ⟨w, Set.mem_iUnion.mpr ⟨hwJ, hw⟩⟩
  have hxcomp : x ∈ closure (T.cell v).carrierᶜ := by
    rw [frontier_eq_closure_inter_closure] at hx
    exact hx.2
  have hxclose : x ∈ closure (Metric.ball x r ∩ (T.cell v).carrierᶜ) :=
    Metric.isOpen_ball.inter_closure ⟨Metric.mem_ball_self hr, hxcomp⟩
  have hxC := closure_minimal hcover hC hxclose
  obtain ⟨w, hwJ, hw⟩ := Set.mem_iUnion₂.mp hxC
  exact ⟨w, hwJ.2, hw⟩

/-- All other cells meeting the given cell, including lower-dimensional contacts. -/
def touchingCells (v : T.V) : Set T.V :=
  {w | w ≠ v ∧ (T.facet v w).Nonempty}

/-- A cell contained in D has only finitely many contacts of any dimension. -/
lemma touchingCells_finite (v : T.V) (hvD : (T.cell v).carrier ⊆ T.domain) :
    (T.touchingCells v).Finite := by
  apply (T.locallyFinite _ (T.cell v).compact hvD).subset
  intro w hw
  obtain ⟨x, hxv, hxw⟩ := hw.2
  exact ⟨x, hxw, hxv⟩

/-- Inside the covered open region the entire cell boundary is covered by its
contacts. Lower-dimensional contacts remain explicit until their measure is handled. -/
theorem frontier_eq_iUnion_contacts (v : T.V)
    (hvD : (T.cell v).carrier ⊆ interior T.domain) :
    frontier (T.cell v).carrier = ⋃ w ∈ T.touchingCells v, T.facet v w := by
  ext x
  constructor
  · intro hx
    have hxv : x ∈ (T.cell v).carrier :=
      (by simpa only [(T.cell v).compact.isClosed.closure_eq] using hx.1)
    obtain ⟨w, hwv, hxw⟩ := T.frontier_point_mem_other_cell hx (hvD hxv)
    have hw : w ∈ T.touchingCells v := ⟨hwv, ⟨x, hxv, hxw⟩⟩
    exact Set.mem_iUnion.mpr ⟨w, Set.mem_iUnion.mpr ⟨hw, ⟨hxv, hxw⟩⟩⟩
  · intro hx
    obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx
    exact T.facet_subset_frontier_left hw.1.symm hxw

end BouRabeeGwynne.TilingData
