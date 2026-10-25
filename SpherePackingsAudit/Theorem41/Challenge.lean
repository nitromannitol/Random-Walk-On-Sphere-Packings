module

public import SpherePackingsAudit.Vocabulary.SpherePackings.Support.Section4General.StoppedWalkLaw
public import SpherePackingsAudit.Vocabulary.SpherePackings.Support.Section4General.AssumptionD
public import SpherePackingsAudit.Vocabulary.BouRabeeGwynne.LipschitzDomain

@[expose] public section

/-!
# Comparator challenge: Theorem 4.1 (`theorem:general-clt`)

This file imports only Mathlib and the vocabulary modules of `SpherePackingsAudit/Vocabulary/`,
which copy verbatim, under their repository names, the repository declarations needed to read the
statement (`python3 tools/check_vocabulary.py`).  It ends with one `sorry`, the proof being checked.
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
        ENNReal.ofReal η := by
  sorry

end SpherePackingsAudit
