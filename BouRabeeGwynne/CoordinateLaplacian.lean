-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/CoordinateLaplacian.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.Harmonic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# The actual continuum Laplacian as a coordinate divergence

This identifies the coordinate derivative integrals used by polytope slicing
with mathlib's Laplacian, including its precise second-derivative convention.
-/

open scoped BigOperators InnerProductSpace
open InnerProductSpace Laplacian

namespace BouRabeeGwynne

variable {d : ℕ}

/-- A fixed directional derivative of a `C²` function is `C¹` on its open domain. -/
theorem contDiffOn_directional_fderiv {W : Set (Euc d)} (hW : IsOpen W)
    {h : Euc d → ℝ} (hh : ContDiffOn ℝ 2 h W) (e : Euc d) :
    ContDiffOn ℝ 1 (fun x => (fderiv ℝ h x) e) W :=
  (hh.fderiv_of_isOpen (m := 1) hW (by norm_num)).clm_apply contDiffOn_const

/-- Differentiating a fixed directional derivative evaluates the actual Hessian. -/
theorem fderiv_directional_fderiv {W : Set (Euc d)} (hW : IsOpen W)
    {h : Euc d → ℝ} (hh : ContDiffOn ℝ 2 h W) {x : Euc d} (hx : x ∈ W)
    (e v : Euc d) :
    (fderiv ℝ (fun y => (fderiv ℝ h y) e) x) v =
      (fderiv ℝ (fderiv ℝ h) x v) e := by
  have hC : ContDiffOn ℝ 1 (fderiv ℝ h) W := hh.fderiv_of_isOpen hW (by norm_num)
  have hD := (hC.differentiableOn (by norm_num)).differentiableAt (hW.mem_nhds hx)
  rw [fderiv_clm_apply hD (differentiableAt_const e)]
  simp

/-- The coordinate divergence of the gradient is the continuum Laplacian used
in the theorem statements. -/
theorem laplacian_eq_sum_coordinate_second {W : Set (Euc d)} (hW : IsOpen W)
    {h : Euc d → ℝ} (hh : ContDiffOn ℝ 2 h W) {x : Euc d} (hx : x ∈ W) :
    Δ h x = ∑ i : Fin d,
      (fderiv ℝ (fun y => (fderiv ℝ h y) (EuclideanSpace.basisFun (Fin d) ℝ i)) x)
        (EuclideanSpace.basisFun (Fin d) ℝ i) := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis h (EuclideanSpace.basisFun (Fin d) ℝ)]
  apply Finset.sum_congr rfl
  intro i _
  rw [fderiv_directional_fderiv hW hh hx]
  simp [iteratedFDeriv_two_apply]

/-- Applying a covector to a vector is the sum of its coordinate contributions. -/
theorem continuousLinearMap_apply_eq_sum_coordinates
    (L : Euc d →L[ℝ] ℝ) (v : Euc d) :
    L v = ∑ i : Fin d, v i * L (EuclideanSpace.basisFun (Fin d) ℝ i) := by
  have hv := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr' v
  have h := congrArg L hv
  simpa only [map_sum, map_smul, smul_eq_mul, EuclideanSpace.basisFun_inner] using h.symm

end BouRabeeGwynne
