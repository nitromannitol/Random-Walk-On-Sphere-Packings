-- Built on Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne (commit cf73d6e).
import SpherePackings.Support.Section2.AffineKernel
import BouRabeeGwynne.TilingNetwork
import Mathlib.Analysis.Normed.Affine.Convex

/-!
# Discrete Laplacians of quadratic and `C²` functions at interior vertices

By Lemma 2.2 the discrete Laplacian of `|· - z|²` at a vertex of `V[U]` whose cell lies in the
interior of the ambient set is `∑ a(u, w) |w - u|²`, and by Taylor's theorem on the edge segments the
discrete Laplacian of a `C²` function with Hessian at most `M` there is at most `M` times this sum.
-/

namespace SpherePackings

open BouRabeeGwynne BouRabeeGwynne.OrthogonalTiling

open scoped BigOperators Classical

variable {d : ℕ}

/-- The identity `‖w - z‖² - ‖u - z‖² = ‖w - u‖² + 2 ⟪u - z, w - u⟫`. -/
private lemma norm_sq_sub_sq_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u w z : E) : ‖w - z‖ ^ 2 - ‖u - z‖ ^ 2 = ‖w - u‖ ^ 2 + 2 * inner ℝ (u - z) (w - u) := by
  have h : w - z = (w - u) + (u - z) := by abel
  rw [h, norm_add_sq_real, real_inner_comm (u - z) (w - u)]
  ring

/-- By Lemma 2.2 on the closed network, `∑ a(u, w) ⟪p, w - u⟫ = 0` at an interior vertex `u`. -/
private lemma sum_inner_eq_zero (hd : 1 ≤ d) (T : OrthogonalTiling d) (U : Set (Euc d))
    [Fintype (T.closedVertices U)] (u : T.closedVertices U) (hu : u ∈ T.finiteInterior U)
    (hcellD : (T.cell u).carrier ⊆ interior T.domain) (p : Euc d) :
    ∑ w : T.closedVertices U,
      (T.finiteNetwork (T.closedVertices U)).a u w * inner ℝ p (T.pos w - T.pos u) = 0 := by
  have hv := T.neighbors_finite (u : T.V) (hcellD.trans interior_subset)
  have h1 : (T.finiteNetwork (T.closedVertices U)).laplacian
      (fun w => inner ℝ p (T.pos w) + 0) u = 0 := by
    rw [T.closedNetwork_laplacian U (fun x => inner ℝ p (T.pos x) + 0) u hu hv]
    exact discreteLaplacian_affine_eq_zero hd T (u : T.V) hcellD p 0
  simp only [FiniteConductanceNetwork.laplacian, add_zero] at h1
  simp only [inner_sub_right]
  exact h1

/-- By Lemma 2.2 for a continuous linear functional `L`, `∑ a(u, w) L(w - u) = 0` at an interior
vertex `u`. -/
private lemma sum_clm_eq_zero (hd : 1 ≤ d) (T : OrthogonalTiling d) (U : Set (Euc d))
    [Fintype (T.closedVertices U)] (u : T.closedVertices U) (hu : u ∈ T.finiteInterior U)
    (hcellD : (T.cell u).carrier ⊆ interior T.domain) (L : Euc d →L[ℝ] ℝ) :
    ∑ w : T.closedVertices U,
      (T.finiteNetwork (T.closedVertices U)).a u w * L (T.pos w - T.pos u) = 0 := by
  obtain ⟨p, hp⟩ : ∃ p : Euc d, ∀ x, L x = inner ℝ p x :=
    ⟨(InnerProductSpace.toDual ℝ (Euc d)).symm L, fun x => InnerProductSpace.toDual_symm_apply.symm⟩
  simp only [hp]
  exact sum_inner_eq_zero hd T U u hu hcellD p

/-- Taylor's theorem along a segment: if `h` is `C²` on an open set `W` containing `[a, b]` with
Hessian at most `M` there, then `|h b - h a - Dh(a)(b - a)| ≤ M |b - a|²`. -/
private lemma taylor_segment_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : E → ℝ) {W : Set E} (hW : IsOpen W) (hh : ContDiffOn ℝ 2 h W) {M : ℝ} (hM : 0 ≤ M)
    {a b : E} (hseg : segment ℝ a b ⊆ W)
    (hH : ∀ x ∈ segment ℝ a b, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M) :
    |h b - h a - fderiv ℝ h a (b - a)| ≤ M * ‖b - a‖ ^ 2 := by
  have hCF : ContDiffOn ℝ 1 (fderiv ℝ h) W := hh.fderiv_of_isOpen hW (by norm_num)
  have hdh : ∀ x ∈ segment ℝ a b, DifferentiableAt ℝ h x := fun x hx =>
    (hh.differentiableOn (by norm_num)).differentiableAt (hW.mem_nhds (hseg hx))
  have hdfh : ∀ x ∈ segment ℝ a b, DifferentiableAt ℝ (fderiv ℝ h) x := fun x hx =>
    (hCF.differentiableOn (by norm_num)).differentiableAt (hW.mem_nhds (hseg hx))
  have hgrad : ∀ x ∈ segment ℝ a b, ‖fderiv ℝ h x - fderiv ℝ h a‖ ≤ M * ‖x - a‖ := fun x hx =>
    Convex.norm_image_sub_le_of_norm_fderiv_le hdfh hH (convex_segment a b)
      (left_mem_segment ℝ a b) hx
  have hdist : ∀ x ∈ segment ℝ a b, ‖x - a‖ ≤ ‖b - a‖ := by
    intro x hx
    have h1 := dist_add_dist_of_mem_segment hx
    have h2 : dist a b = ‖b - a‖ := by rw [dist_comm, dist_eq_norm]
    have h3 : dist a x = ‖x - a‖ := by rw [dist_comm, dist_eq_norm]
    linarith [dist_nonneg (x := x) (y := b)]
  have hres := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun z => h z - fderiv ℝ h a z) (f' := fun x => fderiv ℝ h x - fderiv ℝ h a)
    (fun x hx => ((hdh x hx).hasFDerivAt.sub (fderiv ℝ h a).hasFDerivAt).hasFDerivWithinAt)
    (fun x hx => (hgrad x hx).trans (mul_le_mul_of_nonneg_left (hdist x hx) hM))
    (convex_segment a b) (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)
  have hid : h b - h a - fderiv ℝ h a (b - a) =
      (h b - fderiv ℝ h a b) - (h a - fderiv ℝ h a a) := by
    rw [map_sub]
    ring
  rw [← Real.norm_eq_abs, hid]
  calc ‖(h b - fderiv ℝ h a b) - (h a - fderiv ℝ h a a)‖ ≤ M * ‖b - a‖ * ‖b - a‖ := hres
    _ = M * ‖b - a‖ ^ 2 := by ring

/-- By Lemma 2.2, the discrete Laplacian of `|· - z|²` at a vertex of `V[U]` is
`∑ a(u, w) |w - u|²`. -/
theorem laplacian_sq_dist (hd : 1 ≤ d) (T : OrthogonalTiling d) (U : Set (Euc d))
    [Fintype (T.closedVertices U)] (u : T.closedVertices U) (hu : u ∈ T.finiteInterior U)
    (hcellD : (T.cell u).carrier ⊆ interior T.domain) (z : Euc d) :
    (T.finiteNetwork (T.closedVertices U)).laplacian (fun w => ‖T.pos w - z‖ ^ 2) u =
      ∑ w : T.closedVertices U,
        (T.finiteNetwork (T.closedVertices U)).a u w * ‖T.pos w - T.pos u‖ ^ 2 := by
  simp only [FiniteConductanceNetwork.laplacian]
  have hlin := sum_inner_eq_zero hd T U u hu hcellD (T.pos u - z)
  calc ∑ w : T.closedVertices U, (T.finiteNetwork (T.closedVertices U)).a u w *
        (‖T.pos w - z‖ ^ 2 - ‖T.pos u - z‖ ^ 2)
      = ∑ w : T.closedVertices U, ((T.finiteNetwork (T.closedVertices U)).a u w *
          ‖T.pos w - T.pos u‖ ^ 2 + 2 * ((T.finiteNetwork (T.closedVertices U)).a u w *
          inner ℝ (T.pos u - z) (T.pos w - T.pos u))) :=
        Finset.sum_congr rfl fun w _ => by rw [norm_sq_sub_sq_eq]; ring
    _ = ∑ w : T.closedVertices U, (T.finiteNetwork (T.closedVertices U)).a u w *
          ‖T.pos w - T.pos u‖ ^ 2 + 2 * ∑ w : T.closedVertices U,
          (T.finiteNetwork (T.closedVertices U)).a u w *
            inner ℝ (T.pos u - z) (T.pos w - T.pos u) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = ∑ w : T.closedVertices U, (T.finiteNetwork (T.closedVertices U)).a u w *
          ‖T.pos w - T.pos u‖ ^ 2 := by
        rw [hlin, mul_zero, add_zero]

/-- By Lemma 2.2 and Taylor's theorem on the edge segments, the discrete Laplacian of `h_C` at a
vertex of `V[U]` is at most `M ∑ a(u, w) |w - u|²` in absolute value. -/
theorem abs_laplacian_le (hd : 1 ≤ d) (T : OrthogonalTiling d) (U : Set (Euc d))
    [Fintype (T.closedVertices U)] (u : T.closedVertices U) (hu : u ∈ T.finiteInterior U)
    (hcellD : (T.cell u).carrier ⊆ interior T.domain)
    {W : Set (Euc d)} (hW : IsOpen W) {h : Euc d → ℝ} (hh : ContDiffOn ℝ 2 h W) {M : ℝ}
    (hM : 0 ≤ M)
    (hseg : ∀ w : T.closedVertices U, T.adj (u : T.V) w →
      segment ℝ (T.pos u) (T.pos w) ⊆ W)
    (hH : ∀ w : T.closedVertices U, T.adj (u : T.V) w →
      ∀ x ∈ segment ℝ (T.pos u) (T.pos w), ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M) :
    |(T.finiteNetwork (T.closedVertices U)).laplacian (fun w => h (T.pos w)) u| ≤
      M * ∑ w : T.closedVertices U,
        (T.finiteNetwork (T.closedVertices U)).a u w * ‖T.pos w - T.pos u‖ ^ 2 := by
  simp only [FiniteConductanceNetwork.laplacian]
  have hsplit : ∑ w : T.closedVertices U,
      (T.finiteNetwork (T.closedVertices U)).a u w * (h (T.pos w) - h (T.pos u)) =
      ∑ w : T.closedVertices U, (T.finiteNetwork (T.closedVertices U)).a u w *
        (h (T.pos w) - h (T.pos u) - fderiv ℝ h (T.pos u) (T.pos w - T.pos u)) := by
    have hlin := sum_clm_eq_zero hd T U u hu hcellD (fderiv ℝ h (T.pos u))
    calc ∑ w : T.closedVertices U, (T.finiteNetwork (T.closedVertices U)).a u w *
          (h (T.pos w) - h (T.pos u))
        = ∑ w : T.closedVertices U, ((T.finiteNetwork (T.closedVertices U)).a u w *
            (h (T.pos w) - h (T.pos u) - fderiv ℝ h (T.pos u) (T.pos w - T.pos u)) +
            (T.finiteNetwork (T.closedVertices U)).a u w *
              fderiv ℝ h (T.pos u) (T.pos w - T.pos u)) :=
          Finset.sum_congr rfl fun w _ => by ring
      _ = ∑ w : T.closedVertices U, (T.finiteNetwork (T.closedVertices U)).a u w *
            (h (T.pos w) - h (T.pos u) - fderiv ℝ h (T.pos u) (T.pos w - T.pos u)) +
          ∑ w : T.closedVertices U, (T.finiteNetwork (T.closedVertices U)).a u w *
            fderiv ℝ h (T.pos u) (T.pos w - T.pos u) := Finset.sum_add_distrib
      _ = ∑ w : T.closedVertices U, (T.finiteNetwork (T.closedVertices U)).a u w *
            (h (T.pos w) - h (T.pos u) - fderiv ℝ h (T.pos u) (T.pos w - T.pos u)) := by
          rw [hlin, add_zero]
  rw [hsplit]
  have hfd : ∀ w : T.closedVertices U, T.adj (u : T.V) w →
      |h (T.pos w) - h (T.pos u) - fderiv ℝ h (T.pos u) (T.pos w - T.pos u)| ≤
        M * ‖T.pos w - T.pos u‖ ^ 2 :=
    fun w hw => taylor_segment_bound h hW hh hM (hseg w hw) (hH w hw)
  calc |∑ w : T.closedVertices U, (T.finiteNetwork (T.closedVertices U)).a u w *
        (h (T.pos w) - h (T.pos u) - fderiv ℝ h (T.pos u) (T.pos w - T.pos u))|
      ≤ ∑ w : T.closedVertices U, |(T.finiteNetwork (T.closedVertices U)).a u w *
          (h (T.pos w) - h (T.pos u) - fderiv ℝ h (T.pos u) (T.pos w - T.pos u))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ w : T.closedVertices U, (T.finiteNetwork (T.closedVertices U)).a u w *
          (M * ‖T.pos w - T.pos u‖ ^ 2) := by
        refine Finset.sum_le_sum fun w _ => ?_
        have ha0 := (T.finiteNetwork (T.closedVertices U)).nonneg u w
        by_cases hadj : T.adj (u : T.V) w
        · rw [abs_mul, abs_of_nonneg ha0]
          exact mul_le_mul_of_nonneg_left (hfd w hadj) ha0
        · have hnpos : ¬ 0 < (T.finiteNetwork (T.closedVertices U)).a u w :=
            fun hp => hadj (T.conductanceReal_pos_iff.mp hp)
          have ha : (T.finiteNetwork (T.closedVertices U)).a u w = 0 :=
            le_antisymm (not_lt.mp hnpos) ha0
          rw [ha]
          simp
    _ = M * ∑ w : T.closedVertices U, (T.finiteNetwork (T.closedVertices U)).a u w *
          ‖T.pos w - T.pos u‖ ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun w _ => by ring

end SpherePackings
