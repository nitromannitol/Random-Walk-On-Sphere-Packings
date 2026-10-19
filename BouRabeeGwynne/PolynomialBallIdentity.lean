-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/PolynomialBallIdentity.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.PaperObjects
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Order.Interval.Set.Infinite

/-! A polynomial vanishing on a nonempty Euclidean ball is the zero polynomial.
This gives the injectivity step for the finite-dimensional ball Dirichlet operator. -/

open scoped BigOperators
open Set

namespace BouRabeeGwynne

lemma norm_le_sum_abs_coordinates {d : ℕ} (x : Euc d) :
    ‖x‖ ≤ ∑ i : Fin d, |x i| := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hx : x = ∑ i : Fin d, x i • b i := by
    simpa only [b, EuclideanSpace.basisFun_repr] using (b.sum_repr x).symm
  calc
    ‖x‖ = ‖∑ i : Fin d, x i • b i‖ := congrArg norm hx
    _ ≤ ∑ i : Fin d, ‖x i • b i‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_smul, b.norm_eq_one, mul_one, Real.norm_eq_abs]

theorem polynomial_eq_zero_of_eval_zero_on_ball {d : ℕ}
    (p : MvPolynomial (Fin d) ℝ) (c : Euc d) {r : ℝ} (hr : 0 < r)
    (hp : ∀ x ∈ Metric.ball c r, MvPolynomial.eval (fun i => x i) p = 0) : p = 0 := by
  classical
  let a : ℝ := r / ((d : ℝ) + 1)
  have ha : 0 < a := div_pos hr (by positivity)
  have hda : (d : ℝ) * a < r := by
    have heq : a * ((d : ℝ) + 1) = r := div_mul_cancel₀ _ (by positivity)
    nlinarith
  apply MvPolynomial.funext_set (fun i : Fin d => Set.Ioo (c i - a) (c i + a))
    (fun i => Set.Ioo_infinite (by linarith))
  intro x hx
  let y : Euc d := WithLp.toLp 2 x
  have hcoord (i : Fin d) : |(y - c) i| ≤ a := by
    have hi := hx i (Set.mem_univ i)
    change |x i - c i| ≤ a
    exact abs_le.mpr ⟨by linarith [hi.1], by linarith [hi.2]⟩
  have hy : y ∈ Metric.ball c r := by
    apply Metric.mem_ball.mpr
    calc
      dist y c = ‖y - c‖ := dist_eq_norm _ _
      _ ≤ ∑ i : Fin d, |(y - c) i| := norm_le_sum_abs_coordinates _
      _ ≤ ∑ _i : Fin d, a := Finset.sum_le_sum (fun i _ => hcoord i)
      _ = (d : ℝ) * a := by simp
      _ < r := hda
  have hyzero := hp y hy
  change MvPolynomial.eval x p = 0 at hyzero
  simpa only [map_zero] using hyzero

end BouRabeeGwynne
