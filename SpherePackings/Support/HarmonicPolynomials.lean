module

public import BouRabeeGwynne.Harmonic

@[expose] public section

/-!
# Two harmonic polynomials

Coordinate functions and differences of squares of coordinates are harmonic on `ℝ^d`.  They test
the exit law of Brownian motion in the proof of Theorem 6.1.
-/

namespace SpherePackings

open BouRabeeGwynne

variable {d : ℕ}

/-- The `i`-th coordinate as a continuous linear functional on `ℝ^d`. -/
private noncomputable abbrev coordCLM (i : Fin d) : Euc d →L[ℝ] ℝ := EuclideanSpace.proj i

private lemma coordCLM_apply (i : Fin d) (v : Euc d) : coordCLM i v = v i := rfl

/-- The coordinate function `z ↦ z i` has derivative `coordCLM i` everywhere. -/
private lemma hasFDerivAt_coord (i : Fin d) (y : Euc d) :
    HasFDerivAt (fun z : Euc d => z i) (coordCLM i) y :=
  (coordCLM i).hasFDerivAt

/-- Product rule for `z ↦ z i * z i`, with the bilinear multiplication on `ℝ`. -/
private lemma hasFDerivAt_mul_coord (i : Fin d) (y : Euc d) :
    HasFDerivAt (fun z : Euc d => z i * z i)
      ((ContinuousLinearMap.mul ℝ ℝ (y i)).comp (coordCLM i) +
        ((ContinuousLinearMap.mul ℝ ℝ).comp (coordCLM i)).flip (y i)) y :=
  ((ContinuousLinearMap.mul ℝ ℝ).hasFDerivAt.comp y (hasFDerivAt_coord i y)).clm_apply
    (hasFDerivAt_coord i y)

private lemma contDiff_sq_sub_sq (i j : Fin d) :
    ContDiff ℝ 2 (fun z : Euc d => z i * z i - z j * z j) :=
  ((coordCLM i).contDiff.mul (coordCLM i).contDiff).sub
    ((coordCLM j).contDiff.mul (coordCLM j).contDiff)

/-- The first derivative of `z ↦ z i * z i - z j * z j`, applied to a vector. -/
private lemma fderiv_sq_sub_sq_apply (i j : Fin d) (y w : Euc d) :
    fderiv ℝ (fun z : Euc d => z i * z i - z j * z j) y w =
      2 * (y i * w i) - 2 * (y j * w j) := by
  have hd : HasFDerivAt (fun z : Euc d => z i * z i - z j * z j)
      (((ContinuousLinearMap.mul ℝ ℝ (y i)).comp (coordCLM i) +
        ((ContinuousLinearMap.mul ℝ ℝ).comp (coordCLM i)).flip (y i)) -
      ((ContinuousLinearMap.mul ℝ ℝ (y j)).comp (coordCLM j) +
        ((ContinuousLinearMap.mul ℝ ℝ).comp (coordCLM j)).flip (y j))) y :=
    (hasFDerivAt_mul_coord i y).sub (hasFDerivAt_mul_coord j y)
  rw [hd.fderiv]
  simp only [sub_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.mul_apply', coordCLM_apply]
  ring

/-- The second derivative of `z ↦ z i * z i - z j * z j`, evaluated on two vectors. -/
private lemma fderiv_fderiv_sq_sub_sq_apply (i j : Fin d) (x v w : Euc d) :
    fderiv ℝ (fderiv ℝ (fun z : Euc d => z i * z i - z j * z j)) x v w =
      2 * w i * v i - 2 * w j * v j := by
  have hDiff : Differentiable ℝ (fderiv ℝ (fun z : Euc d => z i * z i - z j * z j)) :=
    ((contDiff_sq_sub_sq i j).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hcl : fderiv ℝ (fun y : Euc d =>
        fderiv ℝ (fun z : Euc d => z i * z i - z j * z j) y w) x =
      (fderiv ℝ (fderiv ℝ (fun z : Euc d => z i * z i - z j * z j)) x).flip w := by
    rw [fderiv_clm_apply (hDiff x) (differentiableAt_const w), fderiv_const_apply,
      ContinuousLinearMap.comp_zero, zero_add]
  have hfun : (fun y : Euc d => fderiv ℝ (fun z : Euc d => z i * z i - z j * z j) y w) =
      ⇑((2 * w i) • coordCLM i - (2 * w j) • coordCLM j) := by
    funext y
    rw [fderiv_sq_sub_sq_apply]
    simp only [sub_apply, smul_apply, smul_eq_mul,
      coordCLM_apply]
    ring
  have hA : fderiv ℝ (fun y : Euc d =>
        fderiv ℝ (fun z : Euc d => z i * z i - z j * z j) y w) x =
      (2 * w i) • coordCLM i - (2 * w j) • coordCLM j := by
    rw [hfun, ContinuousLinearMap.fderiv]
  have hv := congrArg (fun L : Euc d →L[ℝ] ℝ => L v) (hcl.symm.trans hA)
  simp only [ContinuousLinearMap.flip_apply, sub_apply,
    smul_apply, smul_eq_mul, coordCLM_apply] at hv
  linarith

theorem isHarmonicOn_coord (i : Fin d) (U : Set (Euc d)) :
    IsHarmonicOn (fun x : Euc d => x i) U := by
  have hc : ContDiff ℝ 2 (fun x : Euc d => x i) := (coordCLM i).contDiff
  refine ⟨hc.contDiffOn, fun x _ => ?_⟩
  have hfd : fderiv ℝ (fun y : Euc d => y i) = fun _ => coordCLM i :=
    funext fun y => (hasFDerivAt_coord i y).fderiv
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin d) ℝ)]
  simp only [iteratedFDeriv_two_apply]
  rw [hfd]
  simp

theorem isHarmonicOn_sq_sub_sq (i j : Fin d) (U : Set (Euc d)) :
    IsHarmonicOn (fun x : Euc d => x i ^ 2 - x j ^ 2) U := by
  have hfun : (fun x : Euc d => x i ^ 2 - x j ^ 2) = fun x => x i * x i - x j * x j := by
    funext x
    ring
  rw [hfun]
  refine ⟨(contDiff_sq_sub_sq i j).contDiffOn, fun x _ => ?_⟩
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin d) ℝ)]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    fderiv_fderiv_sq_sub_sq_apply]
  simp [EuclideanSpace.basisFun_apply, Finset.sum_sub_distrib]

end SpherePackings
