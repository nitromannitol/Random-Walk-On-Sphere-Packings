module

/- Nonvacuity examples written by the independent reviewer (Claude Haiku 5.5) of audit batch 20;
   see `AUDIT.md`. They show that the hypothesis bundles named below can hold together. -/
public import SpherePackings.Support.Guards.LatticeTilings
public import SpherePackings.Support.Section3.PlanarQuadratic

@[expose] public section

-- The reviewer's examples, kept as written.
set_option linter.unusedVariables false
set_option linter.deprecated false

-- Nonvacuity examples of audit batch 20 (appended after the module source).


open MeasureTheory Metric Set BouRabeeGwynne BouRabeeGwynne.OrthogonalTiling SpherePackings.Voronoi
open SpherePackings

namespace Audit20Nonvacuity

/-- The Voronoi tiling of `(1/10) ℤ²` on the ball of radius `2` (as in `Batch19.lean`). -/
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

lemma GT_closure_sub : closure (ball (0 : Euc 2) 1) ⊆ ball (0 : Euc 2) 2 :=
  closure_ball_subset_closedBall.trans (closedBall_subset_ball (by norm_num))

lemma GT_closed_finite : (GT.closedVertices (ball (0 : Euc 2) 1)).Finite :=
  GT.closedVertices_finite isBounded_ball (by rw [GT_domain]; exact GT_closure_sub)
    (fun v hv => by rw [GT_domain]; exact GT_cell_sub v hv)

noncomputable instance GT_fintype : Fintype (GT.closedVertices (ball (0 : Euc 2) 1)) :=
  @Fintype.ofFinite _ GT_closed_finite.to_subtype

lemma hess_zero (x : Euc 2) : ‖fderiv ℝ (fderiv ℝ (fun _ : Euc 2 => (0 : ℝ))) x‖ ≤ 0 := by
  have h0 : fderiv ℝ (fderiv ℝ (fun _ : Euc 2 => (0 : ℝ))) x = 0 := by simp
  rw [h0, ContinuousLinearMap.opNorm_zero]

lemma GT_boundary_access :
    (GT.finiteNetwork (GT.closedVertices (ball (0 : Euc 2) 1))).BoundaryAccessible
      (GT.finiteInterior (ball (0 : Euc 2) 1)) :=
  GT.finiteNetwork_boundaryAccessible_of_cell_interior (R := GT.closedVertices (ball (0 : Euc 2) 1))
    (A := GT.finiteInterior (ball (0 : Euc 2) 1)) (by norm_num)
    (coordinateAxis (0 : Fin 2)) (coordinateAxis_ne_zero 0)
    (fun w hw x hwx => GT.neighbor_mem_closedVertices hw hwx)
    (fun w hw => by
      rw [GT_domain, isOpen_ball.interior_eq]
      exact GT_cell_sub w.1 hw)

lemma hcellD_ball : ∀ v ∈ GT.interiorVertices (ball (0 : Euc 2) 1),
    (GT.cell v).carrier ⊆ interior GT.domain := fun v hv => by
  rw [GT_domain, isOpen_ball.interior_eq]
  exact GT_cell_sub v hv

lemma harmonic_zero : IsHarmonicOn (fun _ : Euc 2 => (0 : ℝ)) univ :=
  ⟨contDiff_const.contDiffOn, fun x _ => by simp⟩

/-- The hypothesis bundle of `planar_dirichlet_bound_quadratic` holds on the lattice tiling with
`h_C = 0`, `M = 0`, `ε = 1/2`, and the Dirichlet solution `f` is provided by the tiling. -/
theorem nonvacuous_quadratic :
    ∃ f : GT.V → ℝ,
      GT.SolvesDirichlet (ball (0 : Euc 2) 1) (fun v => (fun _ : Euc 2 => (0 : ℝ)) (GT.pos v)) f ∧
      ∀ k : ℝ, 0 < k → ∀ v ∈ GT.interiorVertices (ball (0 : Euc 2) 1),
        |f v - (fun _ : Euc 2 => (0 : ℝ)) (GT.pos v)| ≤
          6 * k * 0 * (1 / 2) *
              (MeasureTheory.volume (⋃ w ∈ GT.closedVertices (ball (0 : Euc 2) 1),
                (GT.cell w).carrier)).toReal +
            0 * (1 / 2 + Real.sqrt 2 / k) ^ 2 := by
  obtain ⟨f, hf⟩ := GT.exists_dirichlet (ball (0 : Euc 2) 1) GT_boundary_access
    (fun _ : GT.V => (0 : ℝ))
  refine ⟨f, hf, ?_⟩
  exact planar_dirichlet_bound_quadratic GT (ball (0 : Euc 2) 1) hcellD_ball isOpen_univ
    harmonic_zero (fun _ _ => subset_univ _) isOpen_univ contDiff_const.contDiffOn
    (fun _ _ _ _ _ _ => subset_univ _) (M := 0) (ε := 1 / 2) le_rfl (by norm_num)
    (fun v _ => GT_diam_le v) (fun _ _ x _ => hess_zero x)
    (fun _ _ _ _ _ _ x _ => hess_zero x) f hf

/-- The hypothesis bundle of `planar_dirichlet_rate_half` holds on the lattice tiling with
`h_C = 0`, `M = 0`, `ε = 1/2`, `R₀ = 1` (a bound on `‖x‖` over `U = ball 0 1`). -/
theorem nonvacuous_rate_half :
    ∃ f : GT.V → ℝ,
      GT.SolvesDirichlet (ball (0 : Euc 2) 1) (fun v => (fun _ : Euc 2 => (0 : ℝ)) (GT.pos v)) f ∧
      ∀ v ∈ GT.interiorVertices (ball (0 : Euc 2) 1),
        |f v - (fun _ : Euc 2 => (0 : ℝ)) (GT.pos v)| ≤
          (6 * 0 * (MeasureTheory.volume (Metric.closedBall (0 : Euc 2) (1 + 1))).toReal +
            (1 + Real.sqrt 2) ^ 2 * 0) * Real.sqrt (1 / 2) := by
  obtain ⟨f, hf⟩ := GT.exists_dirichlet (ball (0 : Euc 2) 1) GT_boundary_access
    (fun _ : GT.V => (0 : ℝ))
  refine ⟨f, hf, ?_⟩
  exact planar_dirichlet_rate_half GT (ball (0 : Euc 2) 1) hcellD_ball (R₀ := 1)
    (fun x hx => (mem_ball_zero_iff.mp hx).le) isOpen_univ harmonic_zero
    (fun _ _ => subset_univ _) isOpen_univ contDiff_const.contDiffOn
    (fun _ _ _ _ _ _ => subset_univ _) (M := 0) (ε := 1 / 2) le_rfl (by norm_num) le_rfl
    (fun v _ => GT_diam_le v) (fun _ _ x _ => hess_zero x)
    (fun _ _ _ _ _ _ x _ => hess_zero x) f hf

#print axioms nonvacuous_quadratic
#print axioms nonvacuous_rate_half

end Audit20Nonvacuity
