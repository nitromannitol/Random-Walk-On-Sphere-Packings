import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Poisson point processes

The random point sets `Λ_m` of Proposition 1.1 (`rw-spheres.tex:360-381`).  A random set of points
`Λ : Ω → Set (ℝ^d)` is a Poisson point process with intensity `ν` when every bounded set contains
finitely many points of `Λ`, and, for every measurable set `B` of finite `ν`-measure, `Λ ∩ B` is
almost surely finite, the number of points of `Λ` in `B` has the Poisson law with mean `ν B`, and the
numbers of points in finitely many pairwise disjoint such sets are independent.  (On the null event
where `Λ ∩ B` is infinite, `Set.ncard` counts `0`.)  The points form a set, so the intensity has no
atoms: the count in a singleton is at most one.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace SpherePackings

variable {d : ℕ}

/-- `Λ` is a Poisson point process on `ℝ^d` with intensity `ν` under `P`. -/
structure IsPoissonPointProcess {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Λ : Ω → Set (EuclideanSpace ℝ (Fin d))) (ν : Measure (EuclideanSpace ℝ (Fin d))) :
    Prop where
  /-- Finitely many points in every bounded set. -/
  finite : ∀ B, Bornology.IsBounded B → ∀ ω, (Λ ω ∩ B).Finite
  /-- Almost surely finitely many points in every measurable set of finite intensity. -/
  ae_finite : ∀ B, MeasurableSet B → ν B ≠ ∞ → ∀ᵐ ω ∂P, (Λ ω ∩ B).Finite
  /-- The number of points in such a set is Poisson with mean `ν B`. -/
  hasLaw : ∀ B, MeasurableSet B → ν B ≠ ∞ →
    HasLaw (fun ω => (Λ ω ∩ B).ncard) (poissonMeasure (ν B).toNNReal) P
  /-- Counts in finitely many pairwise disjoint such sets are independent. -/
  indep : ∀ (n : ℕ) (B : Fin n → Set (EuclideanSpace ℝ (Fin d))),
    (∀ i, MeasurableSet (B i)) → (∀ i, ν (B i) ≠ ∞) → Pairwise (Function.onFun Disjoint B) →
      iIndepFun (fun i ω => (Λ ω ∩ B i).ncard) P

end SpherePackings
