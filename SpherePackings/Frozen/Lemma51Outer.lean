module

/-
Lemma 5.1(b) of rw-spheres.tex, frozen.

Paper statement, `rw-spheres.tex:1635-1641` (label `lemma:geometric-constraint`): there is
`δ = δ(d) ∈ (0, 1)` such that if every cube `y + [-δk, δk]^d`, `y ∈ k ℤ^d ∩ B_{2k}(U)`, contains a
point of `S`, then `𝒞_s ⊆ B_{4k√d}(s)` for every `s ∈ S ∩ U`.

Corrected statement (`rw-spheres-corrected.tex`, Lemma 5.1(b)): there are constants
`δ = δ(d) ∈ (0, 1)` and `R = R(d) ≥ 2` such that, with the grid points of `k ℤ^d ∩ B_{Rk}(U)`, the
same conclusion holds.  Stated here for arbitrary sets `U` and `S` (the paper's bounded domain `U`
and locally finite `S` are not needed).  The proof takes `δ = 1/10` and `R = max(2, 1.1√d)`.  The
published radius `2k` holds for `d ≤ 3` (then `R = 2`) and, with a smaller `δ`, for `4 ≤ d ≤ 12`
(a separate rounding argument, not formalized: there the registered statement is weaker than the
printed one).  It fails for every `d ≥ 13`: with `k = 1`, `s = (-1/100, 1/2, …, 1/2)`,
`U = B_{1/1000}(s)` and `S = {s} ∪ (ℤ^d ∩ B_2(U))`, every tested cube contains a point of `S` for
every `δ > 0`, while `s + 5√d e₁ ∈ 𝒞_s`.
-/
public import SpherePackings.Support.Voronoi.GeometricConstraint

@[expose] public section

open Metric SpherePackings.Voronoi

-- FROZEN-STATEMENT-BEGIN
theorem SpherePackings.Frozen.lemma51b_outer {d : ℕ} (hd : 1 ≤ d) :
    ∃ δ R : ℝ, 0 < δ ∧ δ < 1 ∧ 2 ≤ R ∧
      ∀ (U S : Set (EuclideanSpace ℝ (Fin d))) (k : ℝ), 0 < k →
        (∀ y ∈ grid k ∩ cthickening (R * k) U, (S ∩ cube y (δ * k)).Nonempty) →
        ∀ s ∈ S ∩ U, cell S s ⊆ ball s (4 * k * Real.sqrt d)
-- FROZEN-STATEMENT-END
:= SpherePackings.Voronoi.geometric_constraint_outer hd
