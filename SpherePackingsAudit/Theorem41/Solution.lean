import SpherePackings.MainTheorems

/-!
# Solution: Theorem 4.1 (`theorem:general-clt`)

Proves the challenge statement from the repository's main theorem.  The vocabulary constants are
the repository's own declarations, of which the challenge's vocabulary modules are verbatim copies.
-/

namespace SpherePackingsAudit

open MeasureTheory Metric Filter Set BouRabeeGwynne SpherePackings
open scoped ENNReal NNReal Topology

/-- Theorem 4.1 (`theorem:general-clt`). -/
theorem theorem_4_1 {d : ℕ} (hd : 1 ≤ d) (W : ℕ → NearestNeighbourWalk d)
    (near : ∀ n, Euc d → (W n).V) (hnear : ∀ n, (W n).IsNearestVertex (near n))
    {D : Set (Euc d)} {δ : ℝ} (hAD : AssumptionD W near D δ)
    {U : Set (Euc d)} (hU : IsLipschitzDomain U) (hUb : Bornology.IsBounded U) (hUD : U ⊆ D)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) :
    (∀ᶠ n in atTop, ∀ a : (W n).V, ∀ᵐ ω ∂MarkovChain.law (W n).kernel a,
      FiniteConductanceNetwork.exitTime ((W n).inner U) ω ≠ ⊤) ∧
    ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ z ∈ U,
      levyProkhorovEDist ((W n).stoppedWalkLaw U (near n z)) (stoppedBrownianLaw U z μ) ≤
        ENNReal.ofReal η :=
  SpherePackings.theorem_4_1 hd W near hnear hAD hU hUb hUD hμ

end SpherePackingsAudit
