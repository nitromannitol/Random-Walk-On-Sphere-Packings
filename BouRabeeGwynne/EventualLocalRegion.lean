module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/EventualLocalRegion.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.ApproximationGeometry
public import BouRabeeGwynne.LocalRegion
public import BouRabeeGwynne.NearestVertexExistence

@[expose] public section

open scoped ENNReal Topology

namespace BouRabeeGwynne.NearestVertexData

variable {d : ℕ} {G : TilingSequence d} (N : NearestVertexData G)

/-- The finite graph region used by the Dirichlet problem is eventually supplied
by the approximation and collar hypotheses. -/
theorem eventually_closedVertices_finite (h : N.ApproximationCondition)
    {U : Set (Euc d)} (hU : Bornology.IsBounded U) (hUD : HasAmbientCollar U G.domain) :
    ∀ᶠ n in Filter.atTop, ((G.tiling n).closedVertices U).Finite := by
  filter_upwards [N.eventually_interior_cells_subset_domain h hU hUD] with n hn
  apply (G.tiling n).closedVertices_finite hU
  · simpa only [G.common_domain n] using hUD.closure_subset
  · intro v hv
    simpa only [G.common_domain n] using (hn v hv).trans interior_subset

/-- All neighbor sums at interior vertices are eventually finite. -/
theorem eventually_interior_neighbors_finite (h : N.ApproximationCondition)
    {U : Set (Euc d)} (hU : Bornology.IsBounded U) (hUD : HasAmbientCollar U G.domain) :
    ∀ᶠ n in Filter.atTop, ∀ v ∈ (G.tiling n).interiorVertices U,
      ((G.tiling n).neighbors v).Finite := by
  filter_upwards [N.eventually_interior_cells_subset_domain h hU hUD] with n hn v hv
  apply (G.tiling n).neighbors_finite v
  simpa only [G.common_domain n] using (hn v hv).trans interior_subset

/-- Every external graph vertex eventually lies in any fixed open neighborhood
of the closed continuum domain. This justifies Theorem B(a)'s boundary data. -/
theorem eventually_closedVertices_in_neighborhood (h : N.ApproximationCondition)
    {U O : Set (Euc d)} (hU : Bornology.IsBounded U) (hO : IsOpen O)
    (hUO : closure U ⊆ O) :
    ∀ᶠ n in Filter.atTop, ∀ v ∈ (G.tiling n).closedVertices U, (G.tiling n).pos v ∈ O := by
  obtain ⟨δ, hδ, hδO⟩ := hU.isCompact_closure.exists_cthickening_subset_open hO hUO
  filter_upwards [N.eventually_mesh_finite_le h (half_pos hδ)] with n hn v hv
  apply hδO
  have hp := (G.tiling n).closedVertices_pos_mem_cthickening hv hn.1
  exact Metric.cthickening_mono (by linarith : 2 * (G.tiling n).mesh.toReal ≤ δ)
    (closure U) hp

/-- Local geometry itself guarantees nearest vertices on U for all sufficiently
fine tilings. No minimizer outside D is required. -/
theorem eventually_exists_nearest_vertex (h : N.ApproximationCondition)
    {U : Set (Euc d)} (hU : Bornology.IsBounded U) (hUD : HasAmbientCollar U G.domain) :
    ∀ᶠ n in Filter.atTop, ∀ z ∈ U, ∃ v : (G.tiling n).V,
      ∀ w : (G.tiling n).V, dist z ((G.tiling n).pos v) ≤ dist z ((G.tiling n).pos w) := by
  obtain ⟨δ, hδ, hδD⟩ := hUD.exists_cthickening_subset hU.isCompact_closure
  filter_upwards [N.eventually_mesh_finite_le h hδ] with n hn z hz
  apply (G.tiling n).toTilingData.exists_nearest_vertex hδ _ hn.1 hn.2
  intro x hx
  rw [G.common_domain n]
  apply hδD
  exact Metric.mem_cthickening_of_dist_le x z δ (closure U) (subset_closure hz)
    (Metric.mem_closedBall.mp hx)

end BouRabeeGwynne.NearestVertexData
