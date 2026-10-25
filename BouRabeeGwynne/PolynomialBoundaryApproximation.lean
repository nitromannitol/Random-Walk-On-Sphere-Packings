module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/PolynomialBoundaryApproximation.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.PolynomialAnalyticLaplacian
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass

@[expose] public section

/-!
# Polynomial approximation of boundary data

Coordinate polynomials separate every pair of points in a Euclidean compact
set. The real Stone–Weierstrass theorem therefore supplies genuine multivariate
polynomials approximating arbitrary continuous boundary data uniformly.
-/

open MvPolynomial
namespace BouRabeeGwynne

noncomputable def polynomialRestrictionAlgHom {d : ℕ} (K : Set (Euc d)) :
    MvPolynomial (Fin d) ℝ →ₐ[ℝ] C(K, ℝ) where
  toFun p := ⟨fun x ↦ polynomialEval p x.1,
    (contDiff_polynomialEval p (n := 0)).continuous.comp continuous_subtype_val⟩
  map_zero' := by ext x; simp [polynomialEval]
  map_one' := by ext x; simp [polynomialEval]
  map_add' p q := by ext x; simp [polynomialEval]
  map_mul' p q := by ext x; simp [polynomialEval]
  commutes' c := by ext x; simp [polynomialEval]

@[simp] lemma polynomialRestrictionAlgHom_apply {d : ℕ} (K : Set (Euc d))
    (p : MvPolynomial (Fin d) ℝ) (x : K) :
    polynomialRestrictionAlgHom K p x = polynomialEval p x.1 := rfl

lemma polynomialRestriction_separatesPoints {d : ℕ} (K : Set (Euc d)) :
    (polynomialRestrictionAlgHom K).range.SeparatesPoints := by
  classical
  intro x y hxy
  have hcoord : ∃ i : Fin d, x.1 i ≠ y.1 i := by
    by_contra! h
    apply hxy
    apply Subtype.ext
    ext i
    exact h i
  obtain ⟨i, hi⟩ := hcoord
  refine ⟨polynomialRestrictionAlgHom K (X i),
    ⟨polynomialRestrictionAlgHom K (X i), ⟨X i, rfl⟩, rfl⟩, ?_⟩
  simpa [polynomialEval] using hi

/-- Uniform polynomial approximation on the actual compact boundary, with no
regularity requirement on the boundary beyond compactness. -/
theorem exists_polynomial_near_continuous_on_compact {d : ℕ}
    {K : Set (Euc d)} (hK : IsCompact K) (f : K → ℝ) (hf : Continuous f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : MvPolynomial (Fin d) ℝ, ∀ x : K, |polynomialEval p x.1 - f x| < ε := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨⟨g, hg⟩, hnear⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints
      (polynomialRestrictionAlgHom K).range (polynomialRestriction_separatesPoints K)
      f hf ε hε
  obtain ⟨p, hp⟩ := hg
  refine ⟨p, fun x ↦ ?_⟩
  have hx := hnear x
  change ‖g x - f x‖ < ε at hx
  rw [← hp] at hx
  change ‖polynomialEval p x.1 - f x‖ < ε at hx
  simpa only [Real.norm_eq_abs] using hx

end BouRabeeGwynne
