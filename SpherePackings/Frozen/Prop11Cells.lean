module

/-
Proposition 1.1 of rw-spheres.tex, first part, frozen.

Paper statement, `rw-spheres.tex:371-381` (label `prop:min-max-edge-length`): with probability one,
for all large `m`, the Voronoi cells of the Poisson process `Λ_m` of intensity `m μ` that meet `U`
satisfy `B_{m^{-8/β⁻}}(s) ⊆ 𝒞_s ⊆ B_{m^{-1/(3β⁺)}}(s)`.

Corrected statement (`rw-spheres-corrected.tex`, Correction 3): the mass bounds (1.4) are assumed
on an open neighbourhood `W` of `closure U`, not only on `U`.  The published version is false: for
`U` the unit ball and `μ` the Lebesgue measure restricted to `U`, the cells of the extreme points
of the (finite) process are unbounded and meet `U`.  Only the points in `W` are assumed to form a
Poisson point process, of intensity `m μ|_W`: this follows from `Λ_m` being a Poisson point process
of intensity `m μ` (`IsPoissonPointProcess.restrict_inter`), and allows `μ` to have atoms outside
`W`.  The Poisson processes need not be independent, and `U` need not be connected.  A Poisson point
process has finitely many points in every bounded set (`IsPoissonPointProcess`), so the intensity
may have infinite total mass, as Lebesgue measure on `ℝ^d` does.
-/
public import SpherePackings.Support.Voronoi.PoissonLocal

@[expose] public section

open MeasureTheory Metric Filter Set SpherePackings SpherePackings.Voronoi
open scoped ENNReal NNReal Topology

-- FROZEN-STATEMENT-BEGIN
theorem SpherePackings.Frozen.prop11_cells {d : ℕ} (hd : 1 ≤ d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hUb : Bornology.IsBounded U) {μ : Measure (EuclideanSpace ℝ (Fin d))} {βp βm : ℝ}
    (hβp : 0 < βp) (hβm : 0 < βm) {W : Set (EuclideanSpace ℝ (Fin d))}
    (hW : IsOpen W) (hUW : closure U ⊆ W) (hμ : HolderMassBounds μ W βp βm)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Λ : ℕ → Ω → Set (EuclideanSpace ℝ (Fin d)))
    (hΛ : ∀ m : ℕ, IsPoissonPointProcess P (fun ω => Λ m ω ∩ W) ((m : ℝ≥0∞) • μ.restrict W)) :
    ∀ᵐ ω ∂P, ∀ᶠ m in atTop, ∀ s ∈ Λ m ω, (cell (Λ m ω) s ∩ U).Nonempty →
      ball s ((m : ℝ) ^ (-8 / βm)) ⊆ cell (Λ m ω) s ∧
        cell (Λ m ω) s ⊆ ball s ((m : ℝ) ^ (-1 / (3 * βp)))
-- FROZEN-STATEMENT-END
:= SpherePackings.voronoi_cells_between_balls_local hd hUb hβp hβm hW hUW hμ P Λ hΛ
