module

-- Built on Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne (commit cf73d6e).
public import BouRabeeGwynne.PolytopeGaussGreen
public import SpherePackings.Support.Complete.GaussGreen
public import SpherePackings.Support.HarmonicPolynomials

@[expose] public section

/-!
# Lemma 2.2: affine functions lie in the kernel of the discrete Laplacian

`rw-spheres.tex:657-678` (label `lemma:linear-lie-in-kernel`).  Corrected: the printed lemma claims
`Δ_a ℓ_p(v) = 0` at every vertex, which fails at a cell with a facet not shared with a neighbour (two
squares: `ℓ(x) = x₁` has discrete Laplacian `1` at the left square).  The identity holds at every
vertex whose cell lies in the interior of the ambient set, where all facets are shared, and more
generally at every vertex whose cell is complete (`rw-spheres-corrected.tex`, Correction 4).
-/

namespace SpherePackings

open BouRabeeGwynne

/-- The gradient of `x ↦ ⟪p, x⟫ + c` is the constant functional `⟪p, ·⟫`. -/
private lemma fderiv_affine {d : ℕ} (p : Euc d) (c : ℝ) (y : Euc d) :
    fderiv ℝ (fun x : Euc d => inner ℝ p x + c) y = innerSL ℝ p :=
  ((innerSL ℝ p).hasFDerivAt.add_const c).fderiv

/-- The affine function `x ↦ ⟪p, x⟫ + c` is harmonic on any set. -/
private lemma isHarmonicOn_affine {d : ℕ} (p : Euc d) (c : ℝ) (U : Set (Euc d)) :
    IsHarmonicOn (fun x : Euc d => inner ℝ p x + c) U := by
  have hc : ContDiff ℝ 2 (fun x : Euc d => inner ℝ p x + c) :=
    (innerSL ℝ p).contDiff.add contDiff_const
  have hfd : fderiv ℝ (fun x : Euc d => inner ℝ p x + c) = fun _ => innerSL ℝ p :=
    funext fun y => fderiv_affine p c y
  refine ⟨hc.contDiffOn, fun x _ => ?_⟩
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin d) ℝ)]
  simp only [iteratedFDeriv_two_apply]
  rw [hfd]
  simp

/-- The actual contact flux of `x ↦ ⟪p, x⟫ + c` is the conductance times the increment. -/
private lemma surfaceFlux_affine {d : ℕ} (T : OrthogonalTiling d) (p : Euc d) (c : ℝ)
    {v w : T.V} (hvw : T.adj v w) :
    T.surfaceFlux (fun x => inner ℝ p x + c) v w =
      T.conductanceReal v w * (inner ℝ p (T.pos w) + c - (inner ℝ p (T.pos v) + c)) := by
  unfold OrthogonalTiling.surfaceFlux
  simp only [fderiv_affine, innerSL_apply_apply]
  rw [MeasureTheory.setIntegral_const, smul_eq_mul]
  change (T.facetVolume v w).toReal * inner ℝ p (T.unitEdgeDirection v w) = _
  rw [T.conductanceReal_of_adj hvw]
  simp only [OrthogonalTiling.unitEdgeDirection, real_inner_smul_right, inner_sub_right]
  ring

/-- **Lemma 2.2** (`lemma:linear-lie-in-kernel`), corrected: `Δ_a ℓ_p(v) = 0` for
`ℓ_p(x) = p ⬝ x + c` at every vertex `v` whose cell lies in the interior of the ambient set. -/
theorem discreteLaplacian_affine_eq_zero {d : ℕ} (hd : 1 ≤ d) (T : OrthogonalTiling d) (v : T.V)
    (hvD : (T.cell v).carrier ⊆ interior T.domain) (p : Euc d) (c : ℝ) :
    T.discreteLaplacian (fun w => inner ℝ p (T.pos w) + c) v
      (T.neighbors_finite v (hvD.trans interior_subset)) = 0 := by
  have hv := T.neighbors_finite v (hvD.trans interior_subset)
  have hsum := T.sum_surfaceFlux_eq_zero_of_harmonic hd v hvD hv isOpen_univ
    (Set.subset_univ _) (isHarmonicOn_affine p c Set.univ)
  refine Eq.trans ?_ hsum
  unfold OrthogonalTiling.discreteLaplacian
  refine Finset.sum_congr rfl fun w hw => ?_
  dsimp only
  rw [surfaceFlux_affine T p c ((T.mem_neighborFinset hv).mp hw)]

/-- **Lemma 2.2** (`lemma:linear-lie-in-kernel`), as in the corrected paper
(`rw-spheres-corrected.tex`, Correction 4): `Δ_a ℓ_p(v) = 0` for `ℓ_p(x) = p ⬝ x + c` at every vertex
`v` whose cell is complete. -/
theorem discreteLaplacian_affine_eq_zero_of_complete {d : ℕ} (hd : 1 ≤ d) (T : OrthogonalTiling d)
    (v : T.V) (hv : CompleteCell T v) (p : Euc d) (c : ℝ) :
    T.discreteLaplacian (fun w => inner ℝ p (T.pos w) + c) v hv.1 = 0 := by
  have hharm := isHarmonicOn_affine p c Set.univ
  have hsum := sum_surfaceFlux_eq_zero_of_complete hd T hv isOpen_univ (Set.subset_univ _)
    hharm.contDiffOn (fun x _ => hharm.laplacian_eq_zero (Set.mem_univ x))
  refine Eq.trans ?_ hsum
  unfold OrthogonalTiling.discreteLaplacian
  refine Finset.sum_congr rfl fun w hw => ?_
  dsimp only
  rw [surfaceFlux_affine T p c ((T.mem_neighborFinset hv.1).mp hw)]

end SpherePackings
