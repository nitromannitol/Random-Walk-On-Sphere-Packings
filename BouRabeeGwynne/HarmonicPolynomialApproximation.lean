module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/HarmonicPolynomialApproximation.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.PolynomialBoundaryApproximation
public import BouRabeeGwynne.PolynomialDirichlet
public import Mathlib.Topology.MetricSpace.Thickening

@[expose] public section

/-!
# Genuine harmonic approximants for the Section 4 harmonic-measure argument

Polynomial density on a sphere and the finite-dimensional polynomial Dirichlet
construction give globally harmonic polynomial approximants. Since they are
harmonic on every enlarged ball already, no parameter-dependent Poisson
extension theorem is needed. Continuity controls the small overshoot of the
discrete exit points off the sphere.
-/

open MvPolynomial Set Metric
namespace BouRabeeGwynne

/-- Any continuous data on a Euclidean sphere can be approximated uniformly by
an actual globally harmonic polynomial. -/
theorem exists_harmonic_polynomial_near_sphere_data {d : ℕ} (hd : 1 ≤ d)
    (c : Euc d) {r : ℝ} (hr : 0 < r)
    (f : Metric.sphere c r → ℝ) (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : MvPolynomial (Fin d) ℝ, polynomialLaplacian P = 0 ∧
      ∀ x : Metric.sphere c r, |polynomialEval P x.1 - f x| < ε := by
  obtain ⟨p, hp⟩ := exists_polynomial_near_continuous_on_compact
    (isCompact_sphere c r) f hf hε
  obtain ⟨P, hP, hboundary⟩ := exists_harmonic_polynomial_on_sphere hd c hr p
  refine ⟨P, hP, fun x ↦ ?_⟩
  rw [hboundary x.property]
  exact hp x

/-- The same harmonic polynomial approximates a globally continuous spatial
test on a whole collar of the sphere. This is the collar needed for discrete
exit locations whose distance from the sphere is controlled by the mesh. -/
theorem exists_harmonic_polynomial_near_sphere_collar {d : ℕ} (hd : 1 ≤ d)
    (c : Euc d) {r : ℝ} (hr : 0 < r)
    (f : Euc d → ℝ) (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : MvPolynomial (Fin d) ℝ, polynomialLaplacian P = 0 ∧
      ∃ δ > 0, ∀ x ∈ Metric.cthickening δ (Metric.sphere c r),
        |polynomialEval P x - f x| < ε := by
  obtain ⟨P, hP, hnear⟩ := exists_harmonic_polynomial_near_sphere_data hd c hr
    (fun x ↦ f x.1) (hf.comp continuous_subtype_val) hε
  let V : Set (Euc d) := {x | |polynomialEval P x - f x| < ε}
  have hV : IsOpen V := isOpen_lt
    (((contDiff_polynomialEval P (n := 0)).continuous.sub hf).abs) continuous_const
  have hsphere : Metric.sphere c r ⊆ V := fun x hx ↦ hnear ⟨x, hx⟩
  obtain ⟨δ, hδ, hcollar⟩ := (isCompact_sphere c r).exists_cthickening_subset_open hV hsphere
  exact ⟨P, hP, δ, hδ, fun x hx ↦ hcollar hx⟩

end BouRabeeGwynne
