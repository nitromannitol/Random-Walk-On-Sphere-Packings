/-
Theorem 4.1 of rw-spheres.tex, frozen.

Paper statement, `rw-spheres.tex:1481-1488` (label `theorem:general-clt`): if Assumption D holds and
`U ⊆ D` is a bounded Lipschitz domain, the supremum over `z ∈ U` of the Prokhorov distance between
the laws of the walk from `z^n`, interpolated and stopped at its first exit from `V_n[U]`, and of
Brownian motion from `z` stopped at its exit from `U`, in the metric (1.2), tends to `0`.

Formalized for any sequence of nearest-neighbour walks on graphs with vertices in `ℝ^d`
(`NearestNeighbourWalk`: a Markov kernel on the vertex set whose steps follow the edges of an
undirected graph) under Assumption D as printed (`AssumptionD`; the existence of the discrete Dirichlet solutions,
which the paper presupposes, is not assumed, and (4.2) is required of every solution).  `z^n` is any nearest
vertex of `z` (the paper breaks ties lexicographically).  The laws are on curves modulo time
parametrization with the metric (1.2), the distance is Lévy–Prokhorov, and the walk is also shown
to leave `V_n[U]` almost surely for large `n`.  The proof adapts leobon12's coupling from his
proof of Theorem A to an arbitrary kernel.
-/
import SpherePackings.Support.Section4General.Theorem41

open MeasureTheory Metric Filter Set BouRabeeGwynne SpherePackings
open scoped ENNReal Topology

-- FROZEN-STATEMENT-BEGIN
theorem SpherePackings.Frozen.theorem41 {d : ℕ} (hd : 1 ≤ d) (W : ℕ → NearestNeighbourWalk d)
    (near : ∀ n, Euc d → (W n).V) (hnear : ∀ n, (W n).IsNearestVertex (near n))
    {D : Set (Euc d)} {δ : ℝ} (hAD : AssumptionD W near D δ)
    {U : Set (Euc d)} (hU : IsLipschitzDomain U) (hUb : Bornology.IsBounded U) (hUD : U ⊆ D)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) :
    (∀ᶠ n in atTop, ∀ a : (W n).V, ∀ᵐ ω ∂MarkovChain.law (W n).kernel a,
      FiniteConductanceNetwork.exitTime ((W n).inner U) ω ≠ ⊤) ∧
    ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ z ∈ U,
      levyProkhorovEDist ((W n).stoppedWalkLaw U (near n z)) (stoppedBrownianLaw U z μ) ≤
        ENNReal.ofReal η
-- FROZEN-STATEMENT-END
:= SpherePackings.theorem41 hd W near hnear hAD hU hUb hUD hμ
