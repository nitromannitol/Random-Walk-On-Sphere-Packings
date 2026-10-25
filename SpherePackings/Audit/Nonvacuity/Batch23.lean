module

/- Nonvacuity examples written by the independent reviewer (Claude Haiku 5.5) of audit batch 23;
   see `AUDIT.md`. They show that the hypothesis bundles named below can hold together.
   They reuse the lattice tiling `GT` of `Audit20Nonvacuity` (Voronoi tiling of `(1/10) ℤ²` on the
   ball of radius `2`), its boundary accessibility and its interior-cell containment. -/
public import SpherePackings.Audit.Nonvacuity.Batch20
public import SpherePackings.Support.Section3.PlanarInternal
public import SpherePackings.Support.Section3.GeneralInternal

@[expose] public section


open MeasureTheory Metric Set BouRabeeGwynne BouRabeeGwynne.OrthogonalTiling SpherePackings
open SpherePackings.Voronoi
open scoped Laplacian
open Audit20Nonvacuity

namespace AuditBatch23

-- The reviewer's example, kept as written (it uses a deprecated induction principle).
set_option linter.deprecated false in
lemma lift_zero_apply (t : TensorProduct ℝ (Euc 2) (Euc 2)) :
    (TensorProduct.lift (0 : Euc 2 →ₗ[ℝ] Euc 2 →ₗ[ℝ] ℝ)) t = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => exact map_zero _
  | tmul m n => simp [TensorProduct.lift.tmul]
  | add x y hx hy => rw [map_add, hx, hy, add_zero]

/-- A Laplacian vanishes where the second derivative vanishes. -/
lemma lap_eq_zero_of_fderiv_fderiv (f : Euc 2 → ℝ) (x : Euc 2)
    (h : fderiv ℝ (fderiv ℝ f) x = 0) : Δ f x = 0 := by
  show tensorIteratedFDerivTwo ℝ f x (InnerProductSpace.canonicalCovariantTensor (Euc 2)) = 0
  simp [tensorIteratedFDerivTwo, bilinearIteratedFDerivTwo, h]
  exact lift_zero_apply _

/-- The linear function `x ↦ ⟪a, x⟫`: harmonic, with zero Hessian and zero Taylor remainder. -/
noncomputable def lin (a : Euc 2) : Euc 2 → ℝ := fun x => inner ℝ a x

lemma lin_fderiv (a : Euc 2) (x : Euc 2) : fderiv ℝ (lin a) x = innerSL ℝ a :=
  (innerSL ℝ a).hasFDerivAt.fderiv

lemma lin_fderiv_fderiv (a : Euc 2) (x : Euc 2) : fderiv ℝ (fderiv ℝ (lin a)) x = 0 := by
  have hfun : fderiv ℝ (lin a) = fun _ => innerSL ℝ a := funext (lin_fderiv a)
  rw [hfun]
  exact fderiv_const_apply _

lemma lin_hess (a : Euc 2) (x : Euc 2) : ‖fderiv ℝ (fderiv ℝ (lin a)) x‖ ≤ 0 := by
  rw [lin_fderiv_fderiv, ContinuousLinearMap.opNorm_zero]

lemma lin_harm (a : Euc 2) (x : Euc 2) : Δ (lin a) x = 0 :=
  lap_eq_zero_of_fderiv_fderiv _ x (lin_fderiv_fderiv a x)

lemma lin_contDiff (a : Euc 2) : ContDiffOn ℝ 2 (lin a) univ :=
  (innerSL ℝ a).contDiff.contDiffOn

lemma lin_taylor (a : Euc 2) (v w : Euc 2) :
    |lin a w - lin a v - (fderiv ℝ (lin a) v) (w - v)| ≤ 0 / 2 * ‖w - v‖ ^ 2 := by
  rw [lin_fderiv, innerSL_apply_apply]
  simp [lin, inner_sub_right]

lemma GT_complete (v : GT.V) (hv : v ∈ GT.interiorVertices (ball (0 : Euc 2) 1)) :
    CompleteCell GT v :=
  CompleteCell.of_subset_interior (by norm_num) (hcellD_ball v hv)

/-- The bundle of `planar_dirichlet_bound_internal` holds for `h_C = ⟪a, ·⟫` on `GT`, with
`M₀ = M = 0` and `ε = 1/2`; the discrete solution is the one supplied by the tiling. -/
theorem nonvacuous_planar_internal (a : Euc 2) :
    ∃ f : GT.V → ℝ,
      GT.SolvesDirichlet (ball (0 : Euc 2) 1) (fun v => lin a (GT.pos v)) f ∧
      ∀ k : ℝ, 0 < k → ∀ v ∈ GT.interiorVertices (ball (0 : Euc 2) 1),
        |f v - lin a (GT.pos v)| ≤
          3 * 0 * (1 / 2 : ℝ) ^ 2 +
            (6 * k * 0 * (1 / 2 : ℝ) *
                (MeasureTheory.volume (⋃ w ∈ GT.closedVertices (ball (0 : Euc 2) 1),
                  (GT.cell w).carrier)).toReal +
              0 / 2 * (Real.sqrt 2 / k + 1 / 2) ^ 2) := by
  obtain ⟨f, hf⟩ := GT.exists_dirichlet (ball (0 : Euc 2) 1) GT_boundary_access
    (fun v => lin a (GT.pos v))
  refine ⟨f, hf, ?_⟩
  exact planar_dirichlet_bound_internal GT (ball (0 : Euc 2) 1) GT_complete isOpen_univ
    (lin_contDiff a) (fun _ _ => subset_univ _) (fun _ _ x _ => lin_harm a x)
    (M₀ := 0) (M := 0) (ε := 1 / 2) le_rfl le_rfl (by norm_num) (fun v _ => GT_diam_le v)
    (fun _ _ x _ => lin_hess a x) (fun v _ w _ _ => lin_taylor a (GT.pos v) (GT.pos w)) f hf

/-- The bundle of `planar_rate_internal` holds for the same data, with `R₀ = 1`. -/
theorem nonvacuous_planar_rate_internal (a : Euc 2) :
    ∃ f : GT.V → ℝ,
      GT.SolvesDirichlet (ball (0 : Euc 2) 1) (fun v => lin a (GT.pos v)) f ∧
      ∀ v ∈ GT.interiorVertices (ball (0 : Euc 2) 1),
        |f v - lin a (GT.pos v)| ≤
          0 * (3 + 6 * (MeasureTheory.volume (Metric.closedBall (0 : Euc 2) (1 + 1))).toReal +
            (Real.sqrt 2 + 1) ^ 2 / 2) * (1 / 2 : ℝ) ^ ((2 : ℝ) / 3) := by
  obtain ⟨f, hf⟩ := GT.exists_dirichlet (ball (0 : Euc 2) 1) GT_boundary_access
    (fun v => lin a (GT.pos v))
  refine ⟨f, hf, ?_⟩
  exact planar_rate_internal GT (ball (0 : Euc 2) 1) GT_complete (R₀ := 1)
    (fun x hx => (mem_ball_zero_iff.mp hx).le) isOpen_univ (lin_contDiff a)
    (fun _ _ => subset_univ _) (fun _ _ x _ => lin_harm a x)
    (M₀ := 0) (M := 0) (ε := 1 / 2) le_rfl le_rfl (by norm_num) (by norm_num)
    (fun v _ => GT_diam_le v) (fun _ _ x _ => lin_hess a x)
    (fun v _ w _ _ => lin_taylor a (GT.pos v) (GT.pos w)) f hf

/-! Theorem 3.6: the smallness `12 M ε ≤ 1` with `M ≥ 1` needs cells of diameter at most `1/12`,
so the mesh is `1/40` here (`GT` has diameter `√2/10`). -/

noncomputable def GF : OrthogonalTiling 2 :=
  voronoiTiling (grid (1 / 40 : ℝ)) (ball (0 : Euc 2) 2)
    (goodVoronoi_grid (by norm_num) (by norm_num) isBounded_ball)

lemma GF_domain : GF.domain = ball (0 : Euc 2) 2 := voronoiTiling_domain _ _ _

lemma GF_mesh_le : GF.mesh ≤ ENNReal.ofReal (1 / 12) := by
  refine (voronoiTiling_mesh_le _).trans (ENNReal.ofReal_le_ofReal ?_)
  have hs : Real.sqrt ((2 : ℕ) : ℝ) ≤ 3 / 2 := by
    have := Real.sqrt_le_sqrt (show ((2 : ℕ) : ℝ) ≤ (3 / 2) ^ 2 by norm_num)
    rwa [Real.sqrt_sq (by norm_num)] at this
  linarith

lemma GF_diam_le (v : GF.V) : Metric.diam (GF.cell v).carrier ≤ 1 / 12 := by
  have hne : GF.mesh ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top GF_mesh_le
  have h1 : ENNReal.ofReal (Metric.diam (GF.cell v).carrier) ≤ GF.mesh :=
    le_iSup (fun w : GF.V => ENNReal.ofReal (Metric.diam (GF.cell w).carrier)) v
  exact ((ENNReal.ofReal_le_iff_le_toReal hne).mp h1).trans
    (ENNReal.toReal_le_of_le_ofReal (by norm_num) GF_mesh_le)

lemma GF_cell_sub (v : GF.V) (hv : GF.pos v ∈ ball (0 : Euc 2) 1) :
    (GF.cell v).carrier ⊆ ball (0 : Euc 2) 2 := by
  intro x hx
  have h1 : dist x (GF.pos v) ≤ 1 / 12 :=
    (Metric.dist_le_diam_of_mem (GF.cell v).compact.isBounded hx
      (interior_subset (GF.pos_mem_interior v))).trans (GF_diam_le v)
  have h2 := dist_triangle x (GF.pos v) 0
  rw [dist_zero_right, dist_zero_right] at h2
  rw [mem_ball_zero_iff] at hv ⊢
  linarith

lemma GF_closed_finite : (GF.closedVertices (ball (0 : Euc 2) 1)).Finite :=
  GF.closedVertices_finite isBounded_ball (by rw [GF_domain]; exact GT_closure_sub)
    (fun v hv => by rw [GF_domain]; exact GF_cell_sub v hv)

noncomputable instance GF_fintype : Fintype (GF.closedVertices (ball (0 : Euc 2) 1)) :=
  @Fintype.ofFinite _ GF_closed_finite.to_subtype

lemma GF_boundary_access :
    (GF.finiteNetwork (GF.closedVertices (ball (0 : Euc 2) 1))).BoundaryAccessible
      (GF.finiteInterior (ball (0 : Euc 2) 1)) :=
  GF.finiteNetwork_boundaryAccessible_of_cell_interior (R := GF.closedVertices (ball (0 : Euc 2) 1))
    (A := GF.finiteInterior (ball (0 : Euc 2) 1)) (by norm_num)
    (coordinateAxis (0 : Fin 2)) (coordinateAxis_ne_zero 0)
    (fun w hw x hwx => GF.neighbor_mem_closedVertices hw hwx)
    (fun w hw => by
      rw [GF_domain, isOpen_ball.interior_eq]
      exact GF_cell_sub w.1 hw)

lemma GF_cellD_ball : ∀ v ∈ GF.interiorVertices (ball (0 : Euc 2) 1),
    (GF.cell v).carrier ⊆ interior GF.domain := fun v hv => by
  rw [GF_domain, isOpen_ball.interior_eq]
  exact GF_cell_sub v hv

lemma GF_complete (v : GF.V) (hv : v ∈ GF.interiorVertices (ball (0 : Euc 2) 1)) :
    CompleteCell GF v :=
  CompleteCell.of_subset_interior (by norm_num) (GF_cellD_ball v hv)

/-- The bundle of `generaldim_full_internal` holds for `h_C = ⟪a, ·⟫` on `GF`, with `M = 1`,
`K = 1`, `ε = 1/12`, `L = ‖a‖`, `R₀ = 1` and `D` the total diameter of all cells, which is finite. -/
theorem nonvacuous_generaldim_internal (a : Euc 2) :
    ∃ f : GF.V → ℝ,
      GF.SolvesDirichlet (ball (0 : Euc 2) 1) (fun v => lin a (GF.pos v)) f ∧
      ∃ C : ℝ, ∀ v ∈ GF.interiorVertices (ball (0 : Euc 2) 1),
        |f v - lin a (GF.pos v)| ≤ C := by
  obtain ⟨f, hf⟩ := GF.exists_dirichlet (ball (0 : Euc 2) 1) GF_boundary_access
    (fun v => lin a (GF.pos v))
  refine ⟨f, hf, _, generaldim_full_internal (by norm_num) GF (ball (0 : Euc 2) 1) GF_complete
    (R₀ := 1) (by norm_num) (fun x hx => (mem_ball_zero_iff.mp hx).le) isOpen_univ
    (lin_contDiff a) (fun _ _ => subset_univ _) (fun _ _ x _ => lin_harm a x)
    (M := 1) (L := ‖a‖) (ε := 1 / 12) (K := 1) (Dc := ∑ u ∈ GF_closed_finite.toFinset,
      Metric.diam (GF.cell u).carrier) le_rfl le_rfl (fun v _ => GF_diam_le v)
    (fun _ _ x _ => (lin_hess a x).trans zero_le_one)
    (fun v _ w _ _ => (lin_taylor a (GF.pos v) (GF.pos w)).trans (by
      rw [zero_div, zero_mul]
      positivity))
    (fun _ _ x _ => le_of_eq (by rw [lin_fderiv, innerSL_apply_norm]))
    (fun Q hQ _ => Finset.sum_le_sum_of_subset_of_nonneg
      (fun u hu => GF_closed_finite.mem_toFinset.mpr (hQ u hu).1)
      (fun _ _ _ => Metric.diam_nonneg))
    (by norm_num) (by norm_num) f hf⟩


end AuditBatch23
