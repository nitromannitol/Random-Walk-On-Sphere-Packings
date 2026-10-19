import SpherePackings.Support.Voronoi.CellPolytope

/-!
# Voronoi tilings

The cells of the Voronoi tessellation of a point set `S` that meet a bounded set `D` form an
orthogonal tiling of `D` (`rw-spheres.tex:338-358`), provided every such cell lies between two
balls around its point and `S` is finite near `D`.  Every codimension-one contact of two cells lies
in the bisecting hyperplane of their points, which gives orthogonality.
-/

open Metric

namespace SpherePackings.Voronoi

open BouRabeeGwynne
open Filter Topology

variable {d : ℕ}

/-- The points of `S` whose Voronoi cells meet `D`. -/
def activePoints (S D : Set (Euc d)) : Set (Euc d) :=
  {s | s ∈ S ∧ (cell S s ∩ D).Nonempty}

/-- Conditions under which the Voronoi cells of `S` meeting `D` tile `D`. -/
structure GoodVoronoi (S D : Set (Euc d)) (r R : ℝ) : Prop where
  r_pos : 0 < r
  R_pos : 0 < R
  bounded : Bornology.IsBounded D
  inner : ∀ s ∈ activePoints S D, closedBall s r ⊆ cell S s
  outer : ∀ s ∈ activePoints S D, cell S s ⊆ closedBall s R
  finite : (S ∩ cthickening (6 * R) D).Finite
  cover : ∀ y ∈ D, ∃ s ∈ S, y ∈ cell S s

/-- Two points of `S` at equal distance from `x` determine the level of `inner (s' - s) x`. -/
private lemma inner_sub_eq_of_dist_eq {s s' x : Euc d} (hd : dist s x = dist s' x) :
    inner ℝ (s' - s) x = (‖s'‖ ^ 2 - ‖s‖ ^ 2) / 2 := by
  have h1 := (dist_le_dist_iff_inner_le s s' x).1 hd.le
  have h2 := (dist_le_dist_iff_inner_le s' s x).1 hd.ge
  rw [← neg_sub s' s, inner_neg_left] at h2
  exact le_antisymm h1 (by linarith)

/-- A point equidistant from `s` and `s'` is not an interior point of the cell of `s` when
`s ≠ s'`: a small step away from `s` lands strictly closer to `s'`. -/
private lemma not_mem_interior_cell {S : Set (Euc d)} {s s' y : Euc d} (hs' : s' ∈ S)
    (hne : s ≠ s') (hy : y ∈ interior (cell S s)) (heq : dist s y = dist s' y) : False := by
  have ht : Tendsto (fun t : ℝ => y + t • (y - s)) (𝓝 0) (𝓝 y) := by
    have hc : Continuous fun t : ℝ => y + t • (y - s) := by fun_prop
    simpa using hc.tendsto 0
  have hopen : ∀ᶠ z in 𝓝 y, z ∈ interior (cell S s) := isOpen_interior.mem_nhds hy
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), y + t • (y - s) ∈ cell S s :=
    eventually_nhdsWithin_of_eventually_nhds <|
      (ht.eventually hopen).mono fun t ht' => interior_subset ht'
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := eventually_nhdsWithin_of_forall fun t ht => ht
  obtain ⟨t, hzt, ht0⟩ := (hev.and hpos).exists
  have hz : dist s (y + t • (y - s)) ≤ dist s' (y + t • (y - s)) := hzt s' hs'
  have hu : s' - s ≠ 0 := sub_ne_zero.2 hne.symm
  have hu2 : 0 < ‖s' - s‖ ^ 2 := pow_pos (norm_pos_iff.2 hu) 2
  have e1 : ‖y - s‖ = ‖y - s'‖ := by
    rw [← dist_eq_norm, ← dist_eq_norm, dist_comm y s, dist_comm y s']
    exact heq
  -- the equal distances to `y` force `2 ⟪y - s, s' - s⟫ = ‖s' - s‖ ^ 2`
  have e2 : 2 * inner ℝ (y - s) (s' - s) = ‖s' - s‖ ^ 2 := by
    have h := norm_sub_sq_real (y - s) (s' - s)
    rw [sub_sub_sub_cancel_right, ← e1] at h
    linarith
  have e3 : (1 + t) * (2 * inner ℝ (y - s) (s' - s)) = (1 + t) * ‖s' - s‖ ^ 2 := by
    rw [e2]
  have h1t : (0 : ℝ) ≤ 1 + t := by linarith
  have hn : ‖(1 + t) • (y - s)‖ = (1 + t) * ‖y - s‖ := by
    rw [norm_smul, Real.norm_of_nonneg h1t]
  have hz' : ‖(1 + t) • (y - s)‖ ≤ ‖(1 + t) • (y - s) - (s' - s)‖ := by
    have hzs : y + t • (y - s) - s = (1 + t) • (y - s) := by module
    have hzs' : y + t • (y - s) - s' = (1 + t) • (y - s) - (s' - s) := by module
    rw [dist_comm s, dist_comm s', dist_eq_norm, dist_eq_norm, hzs, hzs'] at hz
    exact hz
  have hsq : ‖(1 + t) • (y - s)‖ ^ 2 ≤ ‖(1 + t) • (y - s) - (s' - s)‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hz'
  rw [norm_sub_sq_real, real_inner_smul_left, hn] at hsq
  nlinarith [mul_pos ht0 hu2]

/-- Interiors of distinct Voronoi cells are disjoint. -/
theorem disjoint_interior_cell (S : Set (Euc d)) {s s' : Euc d} (hs' : s' ∈ S) (hs : s ∈ S)
    (hne : s ≠ s') : Disjoint (interior (cell S s)) (interior (cell S s')) := by
  rw [Set.disjoint_left]
  intro y hy hy'
  have heq : dist s y = dist s' y :=
    le_antisymm (interior_subset hy s' hs') (interior_subset hy' s hs)
  exact not_mem_interior_cell hs' hne hy heq

/-- Two points of the common part of two cells differ by a vector orthogonal to `s' - s`. -/
theorem inner_sub_eq_zero_of_mem_cell_inter (S : Set (Euc d)) {s s' x y : Euc d}
    (hs : s ∈ S) (hs' : s' ∈ S) (hx : x ∈ cell S s ∩ cell S s') (hy : y ∈ cell S s ∩ cell S s') :
    inner ℝ (s' - s) (x - y) = 0 := by
  have hxd : dist s x = dist s' x := le_antisymm (hx.1 s' hs') (hx.2 s hs)
  have hyd : dist s y = dist s' y := le_antisymm (hy.1 s' hs') (hy.2 s hs)
  rw [inner_sub_right, inner_sub_eq_of_dist_eq hxd, inner_sub_eq_of_dist_eq hyd, sub_self]

/-- An active point lies within `R` of a point of `D`. -/
private lemma exists_mem_dist_le {S D : Set (Euc d)} {r R : ℝ} (h : GoodVoronoi S D r R)
    {s : Euc d} (hs : s ∈ activePoints S D) : ∃ y ∈ D, dist s y ≤ R := by
  obtain ⟨y, hy, hyD⟩ := hs.2
  exact ⟨y, hyD, by rw [dist_comm]; exact mem_closedBall.1 (h.outer s hs hy)⟩

/-- Active points lie in the finite set `S ∩ cthickening (6 R) D`. -/
private lemma active_mem_thickening {S D : Set (Euc d)} {r R : ℝ} (h : GoodVoronoi S D r R)
    {s : Euc d} (hs : s ∈ activePoints S D) : s ∈ S ∩ cthickening (6 * R) D := by
  obtain ⟨y, hyD, hy⟩ := exists_mem_dist_le h hs
  exact ⟨hs.1, mem_cthickening_of_dist_le s y (6 * R) D hyD (by linarith [h.R_pos])⟩

/-- The points of `S` within `4 R` of an active point form a finite set. -/
private lemma finite_truncate {S D : Set (Euc d)} {r R : ℝ} (h : GoodVoronoi S D r R)
    {s : Euc d} (hs : s ∈ activePoints S D) : (S ∩ closedBall s (4 * R)).Finite := by
  refine h.finite.subset fun x hx => ⟨hx.1, ?_⟩
  obtain ⟨y, hyD, hy⟩ := exists_mem_dist_le h hs
  have hx' : dist x s ≤ 4 * R := mem_closedBall.1 hx.2
  exact mem_cthickening_of_dist_le x y (6 * R) D hyD
    (by linarith [dist_triangle x s y, h.R_pos])

/-- Truncating `S` to the points within `4 R` does not change the cell of an active point. -/
private lemma cell_truncate_eq {S D : Set (Euc d)} {r R : ℝ} (h : GoodVoronoi S D r R)
    {s : Euc d} (hs : s ∈ activePoints S D) :
    cell (S ∩ closedBall s (4 * R)) s = cell S s :=
  (cell_eq_of_subset_closedBall S h.R_pos (h.outer s hs)).symm

private lemma truncate_inner {S D : Set (Euc d)} {r R : ℝ} (h : GoodVoronoi S D r R)
    {s : Euc d} (hs : s ∈ activePoints S D) :
    closedBall s r ⊆ cell (S ∩ closedBall s (4 * R)) s := by
  rw [cell_truncate_eq h hs]
  exact h.inner s hs

private lemma truncate_outer {S D : Set (Euc d)} {r R : ℝ} (h : GoodVoronoi S D r R)
    {s : Euc d} (hs : s ∈ activePoints S D) :
    cell (S ∩ closedBall s (4 * R)) s ⊆ closedBall s R := by
  rw [cell_truncate_eq h hs]
  exact h.outer s hs

/-- The Voronoi cell of an active point, as a convex polytope cut out by the points of `S`
within `4 R` of it. -/
private noncomputable def activeCell {S D : Set (Euc d)} {r R : ℝ} (h : GoodVoronoi S D r R)
    (v : ↥(activePoints S D)) : ConvexPolytope d :=
  cellPolytope (S ∩ closedBall v.1 (4 * R))
    (fun _ => (finite_truncate h v.2).subset Set.inter_subset_left) v.1 h.r_pos
    (truncate_inner h v.2) (truncate_outer h v.2)

private lemma activeCell_carrier {S D : Set (Euc d)} {r R : ℝ} (h : GoodVoronoi S D r R)
    (v : ↥(activePoints S D)) : (activeCell h v).carrier = cell S v.1 :=
  cell_truncate_eq h v.2

private lemma active_mem_interior {S D : Set (Euc d)} {r R : ℝ} (h : GoodVoronoi S D r R)
    (v : ↥(activePoints S D)) : v.1 ∈ interior (cell S v.1) :=
  interior_maximal (ball_subset_closedBall.trans (h.inner v.1 v.2)) isOpen_ball
    (mem_ball_self h.r_pos)

/-- The Voronoi tiling of `D` by the cells of `S`. -/
noncomputable def voronoiTiling (S D : Set (Euc d)) {r R : ℝ} (h : GoodVoronoi S D r R) :
    OrthogonalTiling d where
  V := ↥(activePoints S D)
  pos := Subtype.val
  pos_injective := Subtype.val_injective
  cell := activeCell h
  domain := D
  pos_mem_interior v := by
    show v.1 ∈ interior (activeCell h v).carrier
    rw [activeCell_carrier]
    exact active_mem_interior h v
  interiors_pairwise_disjoint := by
    intro v w hvw
    show Disjoint (interior (activeCell h v).carrier) (interior (activeCell h w).carrier)
    rw [activeCell_carrier, activeCell_carrier]
    exact disjoint_interior_cell S w.2.1 v.2.1 (fun e => hvw (Subtype.ext e))
  cells_cover_domain := by
    intro y hy
    obtain ⟨s, hs, hys⟩ := h.cover y hy
    have hact : s ∈ activePoints S D := ⟨hs, y, hys, hy⟩
    exact Set.mem_iUnion.2 ⟨⟨s, hact⟩, by rw [activeCell_carrier]; exact hys⟩
  locallyFinite := by
    intro K _ _
    exact (h.finite.preimage Subtype.val_injective.injOn).subset fun v _ =>
      active_mem_thickening h v.2
  orthogonal := by
    intro v w _ x y hx hy
    change x ∈ (activeCell h v).carrier ∩ (activeCell h w).carrier at hx
    change y ∈ (activeCell h v).carrier ∩ (activeCell h w).carrier at hy
    rw [activeCell_carrier, activeCell_carrier] at hx hy
    exact inner_sub_eq_zero_of_mem_cell_inter S v.2.1 w.2.1 hx hy

theorem voronoiTiling_pos (S D : Set (Euc d)) {r R : ℝ} (h : GoodVoronoi S D r R)
    (v : (voronoiTiling S D h).V) : (voronoiTiling S D h).pos v ∈ activePoints S D :=
  v.2

theorem voronoiTiling_pos_surjective (S D : Set (Euc d)) {r R : ℝ} (h : GoodVoronoi S D r R)
    {s : Euc d} (hs : s ∈ activePoints S D) :
    ∃ v : (voronoiTiling S D h).V, (voronoiTiling S D h).pos v = s :=
  ⟨⟨s, hs⟩, rfl⟩

theorem voronoiTiling_cell (S D : Set (Euc d)) {r R : ℝ} (h : GoodVoronoi S D r R)
    (v : (voronoiTiling S D h).V) :
    ((voronoiTiling S D h).cell v).carrier = cell S ((voronoiTiling S D h).pos v) :=
  activeCell_carrier h v

theorem voronoiTiling_domain (S D : Set (Euc d)) {r R : ℝ} (h : GoodVoronoi S D r R) :
    (voronoiTiling S D h).domain = D :=
  rfl

end SpherePackings.Voronoi
