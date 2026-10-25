module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/PolynomialAnalyticLaplacian.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.PolynomialLaplacian
public import BouRabeeGwynne.Harmonic
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section

/-!
# Formal polynomial derivatives are the actual Euclidean derivatives

Polynomial harmonic extension is useful for Section 4 only after its formal
Laplacian is identified with the analytic Laplacian in `IsHarmonicOn`.
The identification here follows the polynomial induction principle and the
actual Fréchet product rule.
-/

open MvPolynomial InnerProductSpace Laplacian
namespace BouRabeeGwynne

noncomputable def polynomialEval {d : ℕ} (p : MvPolynomial (Fin d) ℝ)
    (x : Euc d) : ℝ := MvPolynomial.eval (fun i ↦ x i) p

lemma contDiff_polynomialEval {d : ℕ} (p : MvPolynomial (Fin d) ℝ)
    {n : WithTop ℕ∞} : ContDiff ℝ n (polynomialEval p) := by
  have ha : AnalyticOnNhd ℝ (polynomialEval p) Set.univ :=
    AnalyticOnNhd.eval_continuousLinearMap' (𝕜 := ℝ) (E := Euc d) (B := ℝ)
      (fun i : Fin d ↦ PiLp.proj 2 (fun _ : Fin d ↦ ℝ) i) p
  exact ha.contDiff (n := n)

lemma differentiable_polynomialEval {d : ℕ} (p : MvPolynomial (Fin d) ℝ) :
    Differentiable ℝ (polynomialEval p) :=
  (contDiff_polynomialEval p (n := 1)).differentiable (by norm_num)

/-- Formal differentiation in one coordinate gives the directional derivative
along the corresponding vector of the Euclidean orthonormal basis. -/
theorem fderiv_polynomialEval_basis {d : ℕ} (p : MvPolynomial (Fin d) ℝ)
    (x : Euc d) (i : Fin d) :
    fderiv ℝ (polynomialEval p) x (EuclideanSpace.basisFun (Fin d) ℝ i) =
      polynomialEval (pderiv i p) x := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c =>
    have hconst : polynomialEval (C c : MvPolynomial (Fin d) ℝ) =
        fun _ : Euc d ↦ c := by
      funext y
      simp [polynomialEval]
    rw [hconst, fderiv_const_apply]
    simp [polynomialEval]
  | add p q hp hq =>
    have hadd : polynomialEval (p + q) = fun y ↦ polynomialEval p y + polynomialEval q y := by
      funext y
      simp [polynomialEval]
    rw [hadd, fderiv_fun_add (differentiable_polynomialEval p x)
      (differentiable_polynomialEval q x), ContinuousLinearMap.add_apply, hp, hq]
    simp [polynomialEval, map_add]
  | mul_X p j hp =>
    have hmul : polynomialEval (p * X j) = fun y ↦ polynomialEval p y * y j := by
      funext y
      simp [polynomialEval]
    have hcoord : fderiv ℝ (fun y : Euc d ↦ y j) x =
        PiLp.proj 2 (fun _ : Fin d ↦ ℝ) j :=
      (PiLp.proj 2 (fun _ : Fin d ↦ ℝ) j).fderiv
    have hdcoord : DifferentiableAt ℝ (fun y : Euc d ↦ y j) x :=
      (PiLp.proj 2 (fun _ : Fin d ↦ ℝ) j).differentiableAt
    rw [hmul, fderiv_fun_mul (differentiable_polynomialEval p x) hdcoord]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, hcoord, hp]
    by_cases hij : i = j
    · subst j
      simp [polynomialEval, pderiv_mul, EuclideanSpace.basisFun_apply,
        EuclideanSpace.single_apply, PiLp.proj_apply, mul_comm]
    · simp [polynomialEval, pderiv_mul, EuclideanSpace.basisFun_apply,
        EuclideanSpace.single_apply, PiLp.proj_apply, hij, Ne.symm hij, mul_comm]

/-- Repeating the genuine directional derivative yields evaluation of the
second formal partial derivative. -/
theorem fderiv_twice_polynomialEval_basis {d : ℕ} (p : MvPolynomial (Fin d) ℝ)
    (x : Euc d) (i j : Fin d) :
    fderiv ℝ (fderiv ℝ (polynomialEval p)) x
      (EuclideanSpace.basisFun (Fin d) ℝ i) (EuclideanSpace.basisFun (Fin d) ℝ j) =
        polynomialEval (pderiv i (pderiv j p)) x := by
  have heq : (fun y ↦ fderiv ℝ (polynomialEval p) y
      (EuclideanSpace.basisFun (Fin d) ℝ j)) = polynomialEval (pderiv j p) :=
    funext (fun y ↦ fderiv_polynomialEval_basis p y j)
  have hDf : Differentiable ℝ (fderiv ℝ (polynomialEval p)) :=
    ((contDiff_polynomialEval p (n := 2)).fderiv_right (by norm_num) :
      ContDiff ℝ 1 (fderiv ℝ (polynomialEval p))).differentiable (by norm_num)
  have h := fderiv_polynomialEval_basis (pderiv j p) x i
  rw [← heq, fderiv_clm_apply (hDf x) (differentiableAt_const _)] at h
  simpa only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply] using h

/-- The algebraic and analytic Laplacians agree exactly in every finite
Euclidean dimension. -/
theorem laplacian_polynomialEval {d : ℕ} (p : MvPolynomial (Fin d) ℝ) :
    Δ (polynomialEval p) = polynomialEval (polynomialLaplacian p) := by
  funext x
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis (polynomialEval p)
    (EuclideanSpace.basisFun (Fin d) ℝ)]
  change (∑ i, iteratedFDeriv ℝ 2 (polynomialEval p) x
    ![EuclideanSpace.basisFun (Fin d) ℝ i, EuclideanSpace.basisFun (Fin d) ℝ i]) = _
  simp only [polynomialEval, polynomialLaplacian, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
  exact fderiv_twice_polynomialEval_basis p x i i

lemma isHarmonicOn_polynomialEval_of_laplacian_eq_zero {d : ℕ}
    (p : MvPolynomial (Fin d) ℝ) (hp : polynomialLaplacian p = 0) (U : Set (Euc d)) :
    IsHarmonicOn (polynomialEval p) U := by
  refine ⟨(contDiff_polynomialEval p).contDiffOn, fun x hx ↦ ?_⟩
  rw [laplacian_polynomialEval, hp]
  simp [polynomialEval]

end BouRabeeGwynne
