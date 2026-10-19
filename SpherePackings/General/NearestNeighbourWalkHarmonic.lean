-- Built on Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne (commit cf73d6e).
import SpherePackings.General.NearestNeighbourWalk
import SpherePackings.General.Walk.FreeAbsorbed

/-!
# The harmonic measure of a nearest-neighbour walk as an absorbed-chain exit law

When the walk leaves `V[S]` almost surely, its harmonic measure of `S` is the law of the exit
position of the chain absorbed outside `V[S]`.
-/

open MeasureTheory Set

namespace SpherePackings

variable {d : ℕ}

namespace NearestNeighbourWalk

open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork

variable (W : NearestNeighbourWalk d)

theorem discreteHarmonicMeasure_map_val (S : Set (Euc d)) (a : W.V)
    (hexit : ∀ᵐ ω ∂MarkovChain.law W.kernel a, exitTime (W.inner S) ω ≠ ⊤) :
    (MarkovChain.discreteHarmonicMeasure W.kernel (W.inner S) (W.measurableSet_inner S) a).map
      Subtype.val = W.harmonicMeasure S a := by
  rw [MarkovChain.discreteHarmonicMeasure_eq_law_map, Measure.map_map measurable_subtype_coe
    (MarkovChain.measurable_exitVertex _ (W.measurableSet_inner S)), harmonicMeasure,
    Measure.restrict_eq_self_of_ae_mem (s := {ω | exitTime (W.inner S) ω ≠ ⊤}) hexit]
  rfl

/-- The same, for a set of vertices equal to `V[S]`. -/
theorem discreteHarmonicMeasure_map_val_of_eq (S : Set (Euc d)) {B : Set W.V}
    (hB : MeasurableSet B) (hBS : B = W.inner S) (a : W.V)
    (hexit : ∀ᵐ ω ∂MarkovChain.law W.kernel a, exitTime (W.inner S) ω ≠ ⊤) :
    (MarkovChain.discreteHarmonicMeasure W.kernel B hB a).map Subtype.val =
      W.harmonicMeasure S a := by
  subst hBS
  exact W.discreteHarmonicMeasure_map_val S a hexit

end NearestNeighbourWalk

end SpherePackings
