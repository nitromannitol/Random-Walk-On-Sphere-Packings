-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/PolynomialLaplacian.lean` at commit cf73d6e); unchanged apart from this header.
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.Ring

/-!
# The finite-degree polynomial Dirichlet operator

The formal Laplacian and the squared-radius product identity supply the
algebraic part of harmonic polynomial extension on a sphere. The actual
Brownian exit representation will prove injectivity of the resulting finite
dimensional Dirichlet operator.
-/

open MvPolynomial
namespace BouRabeeGwynne

noncomputable def polynomialLaplacian {d : ℕ} (p : MvPolynomial (Fin d) ℝ) :
    MvPolynomial (Fin d) ℝ := ∑ i, pderiv i (pderiv i p)

noncomputable def polynomialSquaredNorm (d : ℕ) : MvPolynomial (Fin d) ℝ :=
  ∑ i, X i ^ 2

lemma polynomialLaplacian_add {d : ℕ} (p q : MvPolynomial (Fin d) ℝ) :
    polynomialLaplacian (p + q) = polynomialLaplacian p + polynomialLaplacian q := by
  simp [polynomialLaplacian, map_add, Finset.sum_add_distrib]

lemma polynomialLaplacian_smul {d : ℕ} (c : ℝ) (p : MvPolynomial (Fin d) ℝ) :
    polynomialLaplacian (c • p) = c • polynomialLaplacian p := by
  simp [polynomialLaplacian, map_smul, Finset.smul_sum]

lemma pderiv_polynomialSquaredNorm {d : ℕ} (i : Fin d) :
    pderiv i (polynomialSquaredNorm d) = 2 * X i := by
  classical
  rw [polynomialSquaredNorm, map_sum]
  rw [Finset.sum_eq_single i]
  · simp [pderiv_pow]
  · intro j hj hji
    simp [pderiv_pow, pderiv_X_of_ne hji]
  · simp

lemma pderiv_twice_polynomialSquaredNorm_mul {d : ℕ}
    (p : MvPolynomial (Fin d) ℝ) (i : Fin d) :
    pderiv i (pderiv i (polynomialSquaredNorm d * p)) =
      2 * p + 4 * (X i * pderiv i p) +
        polynomialSquaredNorm d * pderiv i (pderiv i p) := by
  rw [pderiv_mul, map_add, pderiv_mul, pderiv_mul,
    pderiv_polynomialSquaredNorm]
  have htwo : pderiv i (2 : MvPolynomial (Fin d) ℝ) = 0 := by
    simpa only [Nat.cast_ofNat] using (pderiv i).map_natCast 2
  rw [pderiv_mul, htwo, pderiv_X_self]
  ring

/-- Multiplication by squared radius raises polynomial degree by two, so its
Laplacian preserves the original finite degree bound. This exact identity also
displays the Euler term used in the homogeneous formulation. -/
theorem polynomialLaplacian_squaredNorm_mul {d : ℕ}
    (p : MvPolynomial (Fin d) ℝ) :
    polynomialLaplacian (polynomialSquaredNorm d * p) =
      (2 * (d : ℝ)) • p + 4 * (∑ i, X i * pderiv i p) +
        polynomialSquaredNorm d * polynomialLaplacian p := by
  simp only [polynomialLaplacian, pderiv_twice_polynomialSquaredNorm_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [smul_eq_C_mul, map_mul, map_ofNat]
  norm_num
  ring

end BouRabeeGwynne
