module

/- Nonvacuity examples written by the independent reviewer (Claude Haiku 5.5) of audit batch 22;
   see `AUDIT.md`. They show that the hypothesis bundles named below can hold together. -/
public import SpherePackings.Support.Guards.LatticeVoronoi
public import SpherePackings.Support.Voronoi.TilingProps
public import SpherePackings.Support.Complete.Basic
public import SpherePackings.Frozen.Lemma22AffineKernel
public import SpherePackings.Frozen.Lemma51Outer

@[expose] public section

/-! Nonvacuity examples for audit batch 22.

* `GT_complete`: every active cell of the Voronoi tiling of `(1/10) ℤ²` over the unit ball is
  complete (`CompleteCell`, via `CompleteCell.of_subset_interior`).
* the frozen Lemmas 2.2 and 2.5 apply to `GT` with that hypothesis.
* `lemma51b_fine_lattice_nonvacuous`: the hypothesis of Lemma 5.1(b) holds for the fine lattice
  `δ ℤ²` (with the witnesses `δ`, `R` of the frozen lemma), so the conclusion applies to it. -/

open MeasureTheory Metric Set BouRabeeGwynne BouRabeeGwynne.OrthogonalTiling
open SpherePackings SpherePackings.Voronoi

namespace AuditBatch22

/-- The Voronoi tiling of `(1/10) ℤ²` on the open ball of radius `2`. -/
noncomputable def GT : OrthogonalTiling 2 :=
  voronoiTiling (grid (1 / 10 : ℝ)) (ball (0 : Euc 2) 2)
    (goodVoronoi_grid (by norm_num) (by norm_num) isBounded_ball)

lemma GT_domain : GT.domain = ball (0 : Euc 2) 2 := voronoiTiling_domain _ _ _

lemma GT_mesh_le : GT.mesh ≤ ENNReal.ofReal (1 / 2) := by
  refine (voronoiTiling_mesh_le _).trans (ENNReal.ofReal_le_ofReal ?_)
  have hs : Real.sqrt ((2 : ℕ) : ℝ) ≤ 3 / 2 := by
    have := Real.sqrt_le_sqrt (show ((2 : ℕ) : ℝ) ≤ (3 / 2) ^ 2 by norm_num)
    rwa [Real.sqrt_sq (by norm_num)] at this
  linarith

lemma GT_diam_le (v : GT.V) : Metric.diam (GT.cell v).carrier ≤ 1 / 2 := by
  have hne : GT.mesh ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top GT_mesh_le
  have h1 : ENNReal.ofReal (Metric.diam (GT.cell v).carrier) ≤ GT.mesh :=
    le_iSup (fun w : GT.V => ENNReal.ofReal (Metric.diam (GT.cell w).carrier)) v
  exact ((ENNReal.ofReal_le_iff_le_toReal hne).mp h1).trans
    (ENNReal.toReal_le_of_le_ofReal (by norm_num) GT_mesh_le)

lemma GT_cell_sub (v : GT.V) (hv : GT.pos v ∈ ball (0 : Euc 2) 1) :
    (GT.cell v).carrier ⊆ ball (0 : Euc 2) 2 := by
  intro x hx
  have h1 : dist x (GT.pos v) ≤ 1 / 2 :=
    (Metric.dist_le_diam_of_mem (GT.cell v).compact.isBounded hx
      (interior_subset (GT.pos_mem_interior v))).trans (GT_diam_le v)
  have h2 := dist_triangle x (GT.pos v) 0
  rw [dist_zero_right, dist_zero_right] at h2
  rw [mem_ball_zero_iff] at hv ⊢
  linarith

lemma GT_cell_interior (v : GT.V) (hv : GT.pos v ∈ ball (0 : Euc 2) 1) :
    (GT.cell v).carrier ⊆ interior GT.domain := by
  rw [GT_domain, isOpen_ball.interior_eq]
  exact GT_cell_sub v hv

/-- Nonvacuity of the completeness hypothesis of Lemmas 2.2, 2.5, 3.1, Propositions 2.6, 3.2 and
Theorem 3.7: every active cell of `GT` over the unit ball is complete. -/
theorem GT_complete : ∀ v ∈ GT.interiorVertices (ball (0 : Euc 2) 1), CompleteCell GT v :=
  fun v hv => CompleteCell.of_subset_interior (by norm_num) (GT_cell_interior v hv)

/-- Lemma 2.2 (frozen) applied to `GT`: affine functions are harmonic at each complete vertex. -/
example (v : GT.V) (hv : v ∈ GT.interiorVertices (ball (0 : Euc 2) 1)) (p : Euc 2) (c : ℝ) :
    GT.discreteLaplacian (fun w => inner ℝ p (GT.pos w) + c) v (GT_complete v hv).1 = 0 :=
  SpherePackings.Frozen.lemma22_affine_kernel (by norm_num) GT v (GT_complete v hv) p c

/-- Lemma 2.5 (the statement of `Frozen/Lemma25DualCoverage.lean` is proved by this theorem) applied
to `GT`, with the completeness hypothesis discharged. -/
example := SpherePackings.dual_coverage_complete (by norm_num) GT (ball (0 : Euc 2) 1) GT_complete

/-- The hypothesis of Lemma 5.1(b) for the fine lattice `δ ℤ²` and `k = 1`, `U` the unit ball:
every grid point `y ∈ ℤ ∩ R-thickening` has a point of `δ ℤ²` in its cube of half-side `δ`. -/
lemma lattice_hyp {δ R : ℝ} (hδ : 0 < δ) :
    ∀ y ∈ grid (1 : ℝ) ∩ cthickening (R * 1) (ball (0 : Euc 2) 1),
      (grid (δ * 1) ∩ cube y (δ * 1) : Set (Euc 2)).Nonempty := by
  intro y _
  obtain ⟨g, hg, hgy⟩ := exists_grid_near (mul_pos hδ one_pos) y
  refine ⟨g, ⟨hg, fun j => ?_⟩⟩
  have := hgy j
  linarith

/-- Nonvacuity of Lemma 5.1(b): the witnesses `δ`, `R` of the frozen lemma admit the fine lattice
`S = δ ℤ²` as a hypothesis-satisfying set, and the conclusion applies to it. -/
theorem lemma51b_fine_lattice_nonvacuous :
    ∃ δ R : ℝ, 0 < δ ∧ δ < 1 ∧ 2 ≤ R ∧
      ∃ S : Set (Euc 2),
        (∀ y ∈ grid (1 : ℝ) ∩ cthickening (R * 1) (ball (0 : Euc 2) 1),
          (S ∩ cube y (δ * 1)).Nonempty) ∧
        ∀ s ∈ S ∩ ball (0 : Euc 2) 1, cell S s ⊆ ball s (4 * 1 * Real.sqrt ((2 : ℕ) : ℝ)) := by
  obtain ⟨δ, R, hδ0, hδ1, hR, hmain⟩ := SpherePackings.Frozen.lemma51b_outer (d := 2) (by norm_num)
  exact ⟨δ, R, hδ0, hδ1, hR, grid (δ * 1), lattice_hyp hδ0,
    hmain (ball (0 : Euc 2) 1) (grid (δ * 1)) 1 one_pos (lattice_hyp hδ0)⟩

end AuditBatch22
