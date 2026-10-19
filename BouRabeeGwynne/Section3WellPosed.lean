-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/Section3WellPosed.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.Section3Accessibility
import BouRabeeGwynne.TheoremBStatement

/-! Eventual well-posedness follows from actual collar geometry and column paths. -/

open scoped Classical Topology

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

/-- A genuine accessible interior vertex has an incident positive-length edge,
so a finite mesh is positive. Empty interiors need no division by the mesh. -/
theorem mesh_toReal_pos_of_accessible_vertex (R : Set T.V) [Fintype R]
    (A : Set R) (hA : (T.finiteNetwork R).BoundaryAccessible A)
    (hmesh : T.mesh ≠ ⊤) {v : R} (hv : v ∈ A) : 0 < T.mesh.toReal := by
  obtain ⟨w, hw, hpath⟩ := hA v hv
  rcases hpath.cases_head with h | ⟨z, hvz, _⟩
  · exact False.elim (hw (h ▸ hv))
  · have hadj := T.conductanceReal_pos_iff.mp hvz
    have hdist : 0 < dist (T.pos v) (T.pos z) :=
      dist_pos.mpr (T.toTilingData.pos_injective.ne hadj.1)
    have hle := T.toTilingData.edge_dist_le_two_mesh hadj hmesh
    linarith

end BouRabeeGwynne.OrthogonalTiling

namespace BouRabeeGwynne.NearestVertexData

variable {d : ℕ} {G : TilingSequence d} (N : NearestVertexData G)

theorem eventually_uniqueDirichletExtension (hd : 1 ≤ d) (e : Euc d) (he : e ≠ 0)
    (h : N.ApproximationCondition) {U : Set (Euc d)}
    (hU : Bornology.IsBounded U) (hUD : HasAmbientCollar U G.domain)
    (g : (n : ℕ) → (G.tiling n).V → ℝ) :
    ∀ᶠ n in Filter.atTop, ((G.tiling n).closedVertices U).Finite ∧
      (G.tiling n).HasUniqueDirichletExtension U (g n) := by
  filter_upwards [N.eventually_closedVertices_finite h hU hUD,
    N.eventually_interior_cells_subset_domain h hU hUD] with n hfin hcells
  letI : Fintype ((G.tiling n).closedVertices U) := hfin.fintype
  have hneighbors : ∀ v ∈ (G.tiling n).finiteInterior U, ∀ w,
      (G.tiling n).adj v w → w ∈ (G.tiling n).closedVertices U := by
    intro v hv w hvw
    exact (G.tiling n).neighbor_mem_closedVertices hv hvw
  have hcellD : ∀ v ∈ (G.tiling n).finiteInterior U,
      ((G.tiling n).cell v).carrier ⊆ interior (G.tiling n).domain := by
    intro v hv
    simpa only [G.common_domain n] using hcells v hv
  have ha := (G.tiling n).finiteNetwork_boundaryAccessible_of_cell_interior
    hd e he ((G.tiling n).closedVertices U) ((G.tiling n).finiteInterior U)
    hneighbors hcellD
  let hD := (G.tiling n).dirichletSolution U ha (g n)
  have hsol := (G.tiling n).dirichletSolution_spec U ha (g n)
  refine ⟨hfin, hD, hsol, ?_⟩
  intro k hk
  exact (G.tiling n).dirichlet_unique_on_closed ha hk hsol

end BouRabeeGwynne.NearestVertexData
