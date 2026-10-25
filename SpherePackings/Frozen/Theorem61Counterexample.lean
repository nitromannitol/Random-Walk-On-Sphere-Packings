module

/-
Theorem 6.1 of rw-spheres.tex, frozen.

Paper statement, `rw-spheres.tex:1791-1794` (label `theorem:counter-example`): for all `d ≥ 3` there
is a sphere packing of `ℝ^d` on which simple random walk with unit conductance does not converge to
Brownian motion modulo time parametrization in the scaling limit; the radii are `1` or `1/2` and
each sphere is tangent to a bounded number of others.

"Does not converge" is formalized for the walk started at the centre `0`, positions scaled by `1/n`,
stopped on leaving the unit ball: these laws exist and do not converge to the law of Brownian motion
from `0` stopped on leaving the unit ball, in the Lévy–Prokhorov distance for curves modulo time
parametrization.  In dimension three the packing is the printed one, and every sphere is covered
(`rw-spheres.tex:331-333`: the hyperplanes tangent to it at its contact points bound a bounded
polytope).  For `d ≥ 4` the packing differs
from the printed one (small spheres at even coordinates beyond the third), for which the printed
hitting computation fails; this packing does not cover `ℝ^d` (a small sphere other than the middle
ones touches others only in the first three coordinate directions).  The statement, like the
printed one, does not ask that the packing cover `ℝ^d`.
-/
public import SpherePackings.Support.Counterexample.Theorem

@[expose] public section

open MeasureTheory Metric Filter Set BouRabeeGwynne SpherePackings
open scoped ENNReal Topology

-- FROZEN-STATEMENT-BEGIN
theorem SpherePackings.Frozen.theorem61_counterexample (d : ℕ) (hd : 3 ≤ d) :
    ∃ P : SpherePacking d,
      (∀ i, P.radius i = 1 ∨ P.radius i = 1 / 2) ∧
      (∃ D : ℕ, ∀ i, {j | P.Tangent i j}.Finite ∧ {j | P.Tangent i j}.ncard ≤ D) ∧
      (d = 3 → ∀ i, P.Covered i) ∧
      ∃ i₀ : P.ι, P.center i₀ = 0 ∧
        (∃ walkLaw : ℕ → Measure (CurveSpace d), ∀ n : ℕ, 1 ≤ n →
          P.IsStoppedSRWLaw ((n : ℝ)⁻¹) (ball 0 1) i₀ (walkLaw n)) ∧
        ∀ μ : Measure (BrownianPath d), IsStandardBrownianLaw μ →
        ∀ walkLaw : ℕ → Measure (CurveSpace d),
          (∀ᶠ n : ℕ in atTop, P.IsStoppedSRWLaw ((n : ℝ)⁻¹) (ball 0 1) i₀ (walkLaw n)) →
          ¬ Tendsto (fun n => levyProkhorovEDist (walkLaw n) (stoppedBrownianLaw (ball 0 1) 0 μ))
            atTop (𝓝 0)
-- FROZEN-STATEMENT-END
:= SpherePackings.simpleRandomWalk_counterexample d hd
