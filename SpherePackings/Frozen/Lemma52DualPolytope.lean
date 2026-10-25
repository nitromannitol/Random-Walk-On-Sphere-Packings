module

/-
Lemma 5.2 of rw-spheres.tex, frozen.

Paper statement, `rw-spheres.tex:1650-1653` (label `lemma:dual-polytope-bound`): there is
`δ'(d) ∈ (0, 1)` such that for all `x^{(i±)} ∈ [-δ', δ']^d ± e_i`, the polar
`P* = {y : x ⬝ y ≤ 1 ∀ x ∈ P}` of `P = conv(x^{(1+)}, x^{(1-)}, …, x^{(d+)}, x^{(d-)})` lies in
`B_{2√d}`.  As printed, for `d ≥ 1`.
-/
public import SpherePackings.Support.Voronoi.DualPolytopeBound

@[expose] public section

open Metric SpherePackings.Voronoi

-- FROZEN-STATEMENT-BEGIN
theorem SpherePackings.Frozen.lemma52_dual_polytope {d : ℕ} (hd : 1 ≤ d) :
    ∃ δ' : ℝ, 0 < δ' ∧ δ' < 1 ∧
      ∀ x : Fin d → Bool → EuclideanSpace ℝ (Fin d),
        (∀ i b, x i b - (if b then (1 : ℝ) else -1) • EuclideanSpace.single i (1 : ℝ) ∈
          cube 0 δ') →
        {y : EuclideanSpace ℝ (Fin d) |
            ∀ p ∈ convexHull ℝ (Set.range (Function.uncurry x)), inner ℝ p y ≤ 1} ⊆
          ball 0 (2 * Real.sqrt d)
-- FROZEN-STATEMENT-END
:= SpherePackings.Voronoi.dual_polytope_bound hd
