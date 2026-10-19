/-
Proposition 4.2 of rw-spheres.tex, frozen.

Paper statement, `rw-spheres.tex:1511-1516` (label `prop:convergence-of-harmonic-measure`): under
Assumption D, `lim_{n → ∞} sup_{x ∈ B} d_P(hm_n(x), hm(x)) = 0` for the unit ball `B`, where
`hm_n(x)` is the discrete harmonic measure of `∂V_n[B]` seen from `x^n` and `hm(x)` the Brownian
harmonic measure of `∂B` seen from `x`.

Formalized for any sequence of nearest-neighbour walks on graphs in `ℝ^d` (`NearestNeighbourWalk`)
under Assumption D as printed (`AssumptionD`; the existence of the discrete Dirichlet solutions,
which the paper presupposes, is not assumed, and (4.2) is required of every solution), for every ball whose closure lies in
`B_δ(D)`, the set on which Assumption D speaks (the unit ball when its closure lies there).
Correction: the printed statement leaves implicit that the unit ball lies in `B_δ(D)` (its proof
applies (4.2) to the unit ball), and fails without it (a walk that is simple random walk near `D` and moves deterministically near the
unit ball satisfies Assumption D).  `x^n` is the vertex selection of Assumption D, any one
satisfying (4.1).  The uniformity is over the whole open ball.
-/
import SpherePackings.Support.Section4General.Prop42

open MeasureTheory Metric Filter Set BouRabeeGwynne SpherePackings

-- FROZEN-STATEMENT-BEGIN
theorem SpherePackings.Frozen.prop42_general {d : ℕ} (hd : 1 ≤ d) (W : ℕ → NearestNeighbourWalk d)
    (near : ∀ n, Euc d → (W n).V) {D : Set (Euc d)} {δ : ℝ} (hAD : AssumptionD W near D δ)
    {c : Euc d} {r : ℝ} (hr : 0 < r) (hB : closedBall c r ⊆ cthickening δ D)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) :
    ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ x ∈ ball c r,
      levyProkhorovEDist ((W n).harmonicMeasure (ball c r) (near n x))
        (brownianSpatialHarmonicMeasure (ball c r) isOpen_ball μ hμ x : Measure (Euc d)) ≤
        ENNReal.ofReal η
-- FROZEN-STATEMENT-END
:= SpherePackings.prop42_general hd W near hAD hr hB hμ
