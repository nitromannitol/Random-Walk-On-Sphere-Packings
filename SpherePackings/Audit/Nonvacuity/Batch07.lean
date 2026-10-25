module

/- Nonvacuity examples written by the independent reviewer (Claude Haiku 5.5) of audit batch 07;
   see `AUDIT.md`. They show that the hypothesis bundles named below can hold together. -/
public import SpherePackings.Support.Guards.LatticeTilings
public import SpherePackings.Support.Guards.LipschitzBall
public import BouRabeeGwynne.TheoremAStatement
public import BouRabeeGwynne.Harmonic

@[expose] public section

-- The reviewer's examples, kept as written.
set_option linter.unusedVariables false
set_option linter.deprecated false

open MeasureTheory Metric
open scoped Topology

namespace SpherePackings.Audit.Nonvacuity07
open BouRabeeGwynne

/-- The hypotheses shared by Theorems A and B (domain, bounded, ambient collar, (1.3) for every
choice of nearest vertices, and the regularity disjunction) are jointly satisfiable in every
dimension `d ≥ 1`, by the lattice Voronoi tilings on the unit ball. -/
theorem lattice_premises_satisfiable {d : ℕ} (hd : 1 ≤ d) :
    ∃ (G : TilingSequence d) (N : NearestVertexData G) (U : Set (Euc d)),
      IsLipschitzDomain U ∧ Bornology.IsBounded U ∧ HasAmbientCollar U G.domain ∧
      N.ApproximationCondition ∧ PaperRegularity G := by
  obtain ⟨G, hcollar, ⟨N⟩, hall, hII⟩ := SpherePackings.exists_lattice_tilingSequence hd
  exact ⟨G, N, ball (0 : Euc d) 1, SpherePackings.isLipschitzDomain_ball hd, isBounded_ball,
    hcollar, hall N, Or.inr (Or.inl hII)⟩

/-- The zero function is harmonic on a neighbourhood of the closure of the unit ball, so the
`HarmonicNearClosure` hypothesis of the Section 3 collar lemmas is satisfiable. -/
theorem zero_harmonicNearClosure {d : ℕ} : HarmonicNearClosure (fun _ : Euc d => (0 : ℝ)) (ball (0 : Euc d) 1) :=
  ⟨ball (0 : Euc d) 2, isOpen_ball,
    closure_ball_subset_closedBall.trans (closedBall_subset_ball (by norm_num)),
    ⟨contDiffOn_const, fun x _ => by simp⟩⟩

end SpherePackings.Audit.Nonvacuity07
