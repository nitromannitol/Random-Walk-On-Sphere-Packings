-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/PolynomialDirichlet.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.PolynomialDegree
import BouRabeeGwynne.PolynomialBallIdentity
import BouRabeeGwynne.PolynomialAnalyticLaplacian
import BouRabeeGwynne.HarmonicNearClosureBrownianExit
import BouRabeeGwynne.EuclideanWienerLaw
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Every polynomial boundary datum on a Euclidean sphere has a globally
harmonic polynomial extension. Injectivity of the finite-degree Dirichlet
operator follows from the actual Brownian exit representation. -/

open MvPolynomial MeasureTheory Set
open scoped BigOperators ENNReal

namespace BouRabeeGwynne

noncomputable def polynomialBallFactor {d : ℕ} (c : Euc d) (r : ℝ) :
    MvPolynomial (Fin d) ℝ := C (r ^ 2) - ∑ i : Fin d, (X i - C (c i)) ^ 2

lemma polynomialBallFactor_degree_le {d : ℕ} (c : Euc d) (r : ℝ) :
    (polynomialBallFactor c r).totalDegree ≤ 2 := by
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · simp only [MvPolynomial.totalDegree_C, Nat.zero_le]
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro i _
    have hi : (X i - C (c i) : MvPolynomial (Fin d) ℝ).totalDegree ≤ 1 :=
      (MvPolynomial.totalDegree_sub_C_le _ _).trans_eq (MvPolynomial.totalDegree_X i)
    exact (MvPolynomial.totalDegree_pow _ 2).trans (by omega)

lemma polynomialEval_ballFactor {d : ℕ} (c x : Euc d) (r : ℝ) :
    polynomialEval (polynomialBallFactor c r) x = r ^ 2 - ‖x - c‖ ^ 2 := by
  simp [polynomialEval, polynomialBallFactor, EuclideanSpace.real_norm_sq_eq,
    PiLp.sub_apply]

noncomputable def ballDirichletOperator {d : ℕ} (c : Euc d) (r : ℝ) (m : ℕ) :
    MvPolynomial.restrictTotalDegree (Fin d) ℝ m →ₗ[ℝ]
      MvPolynomial.restrictTotalDegree (Fin d) ℝ m :=
  quadraticLaplacianOnDegree (polynomialBallFactor c r) (polynomialBallFactor_degree_le c r) m

theorem ballDirichletOperator_injective {d : ℕ} (hd : 1 ≤ d)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (c : Euc d) {r : ℝ} (hr : 0 < r) (m : ℕ) :
    Function.Injective (ballDirichletOperator c r m) := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro q hq
  have hformal : polynomialLaplacian (polynomialBallFactor c r * q.val) = 0 := by
    have hv := congrArg Subtype.val hq
    exact hv
  let f := polynomialEval (polynomialBallFactor c r * q.val)
  have hh : HarmonicNearClosure f (Metric.ball c r) :=
    ⟨Set.univ, isOpen_univ, subset_univ _,
      isHarmonicOn_polynomialEval_of_laplacian_eq_zero _ hformal Set.univ⟩
  have hmul (x : Euc d) : f x =
      polynomialEval (polynomialBallFactor c r) x * polynomialEval q.val x := by
    simp only [f, polynomialEval, map_mul]
  apply Subtype.ext
  change q.val = 0
  apply polynomial_eq_zero_of_eval_zero_on_ball q.val c hr
  intro z hz
  have heq : f z = 0 := by
    calc
      f z = ∫ x, f x ∂((stoppedBrownianLaw (Metric.ball c r) z μ).map CurveSpace.endPoint) :=
        (standardBrownianLaw_integral_stopped_endPoint_harmonicNearClosure hd hμ
          Metric.isOpen_ball Metric.isBounded_ball hh hz).symm
      _ = ∫ _x : Euc d, (0 : ℝ)
          ∂((stoppedBrownianLaw (Metric.ball c r) z μ).map CurveSpace.endPoint) := by
        apply integral_congr_ae
        filter_upwards [standardBrownianLaw_stopped_endPoint_ae_mem_frontier hd hμ
          Metric.isOpen_ball Metric.isBounded_ball hz] with x hx
        have hnorm : ‖x - c‖ = r := by
          simpa only [Metric.mem_sphere, dist_eq_norm] using
            (Metric.frontier_ball_subset_sphere hx)
        rw [hmul, polynomialEval_ballFactor, hnorm, sub_self, zero_mul]
      _ = 0 := by simp
  have hpos : 0 < polynomialEval (polynomialBallFactor c r) z := by
    rw [polynomialEval_ballFactor]
    have hnorm : ‖z - c‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
    nlinarith [norm_nonneg (z - c)]
  rw [hmul] at heq
  exact (mul_eq_zero.mp heq).resolve_left hpos.ne'

theorem exists_harmonic_polynomial_on_sphere_of_brownianLaw {d : ℕ} (hd : 1 ≤ d)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (c : Euc d) {r : ℝ} (hr : 0 < r) (p : MvPolynomial (Fin d) ℝ) :
    ∃ P : MvPolynomial (Fin d) ℝ, polynomialLaplacian P = 0 ∧
      EqOn (polynomialEval P) (polynomialEval p) (Metric.sphere c r) := by
  have hdeg : (polynomialLaplacian p).totalDegree ≤ p.totalDegree := by
    simpa only [polynomialLaplacian, one_mul] using
      (totalDegree_laplacian_mul_le (A := (1 : MvPolynomial (Fin d) ℝ))
        (p := p) (by simp) le_rfl)
  let target : MvPolynomial.restrictTotalDegree (Fin d) ℝ p.totalDegree :=
    ⟨polynomialLaplacian p, (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr hdeg⟩
  obtain ⟨q, hq⟩ := (LinearMap.surjective_of_injective
    (ballDirichletOperator_injective hd hμ c hr p.totalDegree)) target
  have hqformal : polynomialLaplacian (polynomialBallFactor c r * q.val) =
      polynomialLaplacian p := congrArg Subtype.val hq
  refine ⟨p - polynomialBallFactor c r * q.val, ?_, ?_⟩
  · simp only [polynomialLaplacian, map_sub, Finset.sum_sub_distrib]
    change polynomialLaplacian p - polynomialLaplacian (polynomialBallFactor c r * q.val) = 0
    rw [hqformal, sub_self]
  · intro x hx
    have hnorm : ‖x - c‖ = r := by simpa only [Metric.mem_sphere, dist_eq_norm] using hx
    have hfactor : polynomialEval (polynomialBallFactor c r) x = 0 := by
      rw [polynomialEval_ballFactor, hnorm, sub_self]
    change MvPolynomial.eval (fun i => x i) _ = _
    rw [map_sub, map_mul]
    change polynomialEval p x - polynomialEval (polynomialBallFactor c r) x *
      polynomialEval q.val x = polynomialEval p x
    rw [hfactor, zero_mul, sub_zero]

/-- The standard Brownian law used in the injectivity proof is the explicitly
constructed Euclidean Wiener law, so existence has no probabilistic premise. -/
theorem exists_harmonic_polynomial_on_sphere {d : ℕ} (hd : 1 ≤ d)
    (c : Euc d) {r : ℝ} (hr : 0 < r) (p : MvPolynomial (Fin d) ℝ) :
    ∃ P : MvPolynomial (Fin d) ℝ, polynomialLaplacian P = 0 ∧
      EqOn (polynomialEval P) (polynomialEval p) (Metric.sphere c r) :=
  exists_harmonic_polynomial_on_sphere_of_brownianLaw hd
    (isStandardBrownianLaw_euclideanWienerLaw d) c hr p

end BouRabeeGwynne
