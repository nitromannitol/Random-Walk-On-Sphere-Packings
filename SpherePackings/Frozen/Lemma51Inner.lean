/-
Lemma 5.1(a) of rw-spheres.tex, frozen.

Paper statement, `rw-spheres.tex:1627-1634` (label `lemma:geometric-constraint`): if every cube
`x + [-2r, 2r]^d`, `x ∈ r ℤ^d ∩ U`, contains at most one point of `S`, then `B_r(s) ⊆ 𝒞_s` for every
`s ∈ S ∩ U`.

The statement of the corrected paper (`rw-spheres-corrected.tex`, Correction 15): the condition is
asked of every grid point `x ∈ r ℤ^d` with `(x + [-r, r]^d) ∩ U ≠ ∅`.  The published version is false:
in `ℝ`, `U = (0, 10)`, `r = 1` and `S = {0.1, -1.5}` satisfy its hypothesis, but
`B_1(0.1) ⊄ 𝒞_{0.1} = [-0.7, ∞)` (an informal counterexample).  The conclusion is for the closed ball.
-/
import SpherePackings.Support.Voronoi.GeometricConstraint

open Metric SpherePackings.Voronoi

-- FROZEN-STATEMENT-BEGIN
theorem SpherePackings.Frozen.lemma51a_inner {d : ℕ} (U S : Set (EuclideanSpace ℝ (Fin d))) {r : ℝ}
    (hr : 0 < r)
    (h : ∀ x ∈ grid r, (cube x r ∩ U).Nonempty → (S ∩ cube x (2 * r)).Subsingleton) :
    ∀ s ∈ S ∩ U, closedBall s r ⊆ cell S s
-- FROZEN-STATEMENT-END
:= SpherePackings.Voronoi.geometric_constraint_inner_collar U S hr h
