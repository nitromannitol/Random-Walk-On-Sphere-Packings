/- Nonvacuity examples written by the independent reviewer (Claude Haiku 5.5) of audit batch 21;
   see `AUDIT.md`. They show that the hypothesis bundles named below can hold together. -/
import SpherePackings.Support.Counterexample.Covering
import SpherePackings.Support.Poisson.Basic
import SpherePackings.Frozen.Lemma51Outer
import BouRabeeGwynne.EuclideanWienerLaw

-- The reviewer's examples, kept as written.
set_option linter.unusedVariables false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal NNReal

namespace AuditBatch21

open SpherePackings SpherePackings.Voronoi BouRabeeGwynne

/-- One sphere of radius `1` at the origin: nothing touches it. -/
def lonelyPacking (d : ℕ) : SpherePacking d where
  ι := Unit
  center := fun _ => 0
  radius := fun _ => 1
  radius_pos := fun _ => one_pos
  disjoint := fun i j h => absurd (Subsingleton.elim i j) h

/-- A sphere with no tangent neighbour is not covered, in every dimension `d ≥ 1`. -/
example (d : ℕ) (hd : 1 ≤ d) : ¬ (lonelyPacking d).Covered () := by
  have : NeZero d := ⟨by omega⟩
  intro h
  unfold SpherePacking.Covered at h
  have hempty : ∀ j, ¬ (lonelyPacking d).Tangent () j := fun j hj => hj.1 (Subsingleton.elim (α := Unit) _ _)
  have huniv : (⋂ j ∈ {j | (lonelyPacking d).Tangent () j},
      (lonelyPacking d).tangentHalfspace () j) = univ := by
    ext x
    simp [hempty]
  rw [huniv] at h
  exact NormedSpace.unbounded_univ ℝ (Euc d) h

/-- The packing of Theorem 6.1 in dimension three covers every sphere (`Covering.lean`). -/
example : ∀ i, (SpherePackings.Counterexample.packing 0).Covered i :=
  SpherePackings.Counterexample.packing_covered

/-- An intensity with an atom of mass `1` admits no Poisson point process in the set model: the
count in `{x}` is at most one, while the Poisson law with mean `1` charges `2`. -/
example {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω) (Λ : Ω → Set (Euc d)) (x : Euc d)
    (h : IsPoissonPointProcess P Λ (Measure.dirac x)) : False := by
  have hν : (Measure.dirac x) {x} = 1 := Measure.dirac_apply_of_mem rfl
  have hL := h.hasLaw {x} (measurableSet_singleton x) (by rw [hν]; simp)
  have hr : (Measure.dirac x {x}).toNNReal = 1 := by rw [hν]; simp
  rw [hr] at hL
  have hle : ∀ ω, (Λ ω ∩ {x}).ncard ≤ 1 := fun ω =>
    (Set.ncard_le_ncard Set.inter_subset_right (Set.finite_singleton x)).trans
      (Set.ncard_singleton x).le
  have h2 : P.map (fun ω => (Λ ω ∩ {x}).ncard) {2} = 0 := by
    rw [Measure.map_apply_of_aemeasurable hL.aemeasurable (measurableSet_singleton 2)]
    have hpre : (fun ω => (Λ ω ∩ {x}).ncard) ⁻¹' {2} = ∅ := by
      ext ω
      have := hle ω
      simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      omega
    rw [hpre, measure_empty]
  rw [hL.map_eq] at h2
  have hpos : (poissonMeasure 1) {2} ≠ 0 := by
    rw [poissonMeasure_singleton]
    exact (ENNReal.ofReal_pos.mpr (by simp; positivity)).ne'
  exact hpos h2

/-- Lemma 5.1(b), the frozen statement, applied to `S = grid k`: the cube hypothesis holds with the
point `y` itself, so the statement is not vacuous. -/
example {d : ℕ} (hd : 1 ≤ d) (U : Set (Euc d)) {k : ℝ} (hk : 0 < k) :
    ∀ s ∈ grid k ∩ U, cell (grid k) s ⊆ ball s (4 * k * Real.sqrt d) := by
  obtain ⟨δ, R, hδ, -, -, h⟩ := SpherePackings.Frozen.lemma51b_outer hd
  exact h U (grid k) k hk fun y hy =>
    ⟨y, hy.1, show ∀ j, |y j - y j| ≤ δ * k from fun j => by simp; positivity⟩

/-- The `∀ μ` clause of Theorem 6.1 is not vacuous: a standard Brownian law exists (Wiener measure). -/
example (d : ℕ) : ∃ μ : Measure (BrownianPath d), IsStandardBrownianLaw μ :=
  ⟨_, isStandardBrownianLaw_euclideanWienerLaw d⟩

end AuditBatch21
