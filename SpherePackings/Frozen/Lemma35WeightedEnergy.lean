module

/-
Lemma 3.5 of rw-spheres.tex, frozen.

Paper statement, `rw-spheres.tex:1128-1135` (label `lemma:gradient-energy-estimate`):
`∑_{e ∈ E[Ā]} d vol_d(Q_e) 1{|∇f(e)| > δ} ≤ D(f, A)` for every `δ ≥ sup_{e ∈ E[Ā]} ‖e‖`.

leobon12's theorem, for any finite family of edges with lengths at most `δ`, in the form
`d vol_d(Q_e) = ‖e‖ vol_{d-1}(H_e)` (Lemma 2.4).
-/
public import BouRabeeGwynne.Section3WeightedEnergy

@[expose] public section

open scoped BigOperators Classical
open BouRabeeGwynne BouRabeeGwynne.OrthogonalTiling

-- FROZEN-STATEMENT-BEGIN
theorem SpherePackings.Frozen.lemma35_weighted_energy {d : ℕ} (T : BouRabeeGwynne.OrthogonalTiling d) (E : Finset (T.V × T.V))
    (hE : ∀ e ∈ E, T.adj e.1 e.2) (f : T.V → ℝ) (δ : ℝ)
    (hlength : ∀ e ∈ E, ‖T.pos e.2 - T.pos e.1‖ ≤ δ) :
    (∑ e ∈ E, if δ < |f e.2 - f e.1| then
      (T.facetVolume e.1 e.2).toReal * ‖T.pos e.2 - T.pos e.1‖ else 0) ≤
      ∑ e ∈ E, T.conductanceReal e.1 e.2 * (f e.2 - f e.1) ^ 2
-- FROZEN-STATEMENT-END
:= BouRabeeGwynne.OrthogonalTiling.weighted_gradient_energy_estimate_on_edges T E hE f δ hlength
