/- Nonvacuity examples written by the independent reviewer (Claude Haiku 5.5) of audit batch 08;
   see `AUDIT.md`. They show that the hypothesis bundles named below can hold together. -/
import BouRabeeGwynne.TheoremAStatement
import BouRabeeGwynne.TheoremBStatement
import BouRabeeGwynne.Harmonic
import SpherePackings.Support.Guards.LatticeTilings
import SpherePackings.Support.Guards.LipschitzBall

-- The reviewer's examples, kept as written.
set_option linter.unusedVariables false
set_option linter.deprecated false

namespace SpherePackings.Audit.Nonvacuity08
open BouRabeeGwynne

open BouRabeeGwynne Metric
open scoped Topology

/-- Shared premises of `TheoremAStatement` and `TheoremBStatement`, in every dimension `d ≥ 1`:
lattice tilings with the unit ball as domain, the nearest-vertex data, the approximation
condition, and `PaperRegularity` through alternative (II). -/
theorem nonvac_shared_premises (d : ℕ) (hd : 1 ≤ d) :
    ∃ (G : TilingSequence d) (N : NearestVertexData G) (U : Set (Euc d)),
      IsLipschitzDomain U ∧ Bornology.IsBounded U ∧ HasAmbientCollar U G.domain ∧
      N.ApproximationCondition ∧ PaperRegularity G := by
  obtain ⟨G, hcollar, ⟨N⟩, happrox, hreg⟩ := SpherePackings.exists_lattice_tilingSequence hd
  exact ⟨G, N, ball (0 : Euc d) 1, SpherePackings.isLipschitzDomain_ball hd, isBounded_ball,
    hcollar, happrox N, Or.inr (Or.inl hreg)⟩

/-- Premises of `TheoremBPartBStatement` for the boundary data `hC = 0`, including
`Nonempty (NearestClosureBoundaryChoices G U)`, so the universal quantifier over the sampling
choices `S` in branch (b) is not vacuous. -/
theorem nonvac_theoremB_part_b_premises (d : ℕ) (hd : 1 ≤ d) :
    ∃ (G : TilingSequence d) (N : NearestVertexData G) (U : Set (Euc d)) (hC : Euc d → ℝ),
      IsLipschitzDomain U ∧ Bornology.IsBounded U ∧ HasAmbientCollar U G.domain ∧
      N.ApproximationCondition ∧ PaperRegularity G ∧ IsHarmonicOn hC U ∧
      ContinuousOnClosure hC U ∧ Nonempty (NearestClosureBoundaryChoices G U) := by
  obtain ⟨G, hcollar, ⟨N⟩, happrox, hreg⟩ := SpherePackings.exists_lattice_tilingSequence hd
  refine ⟨G, N, ball (0 : Euc d) 1, fun _ => 0, SpherePackings.isLipschitzDomain_ball hd,
    isBounded_ball, hcollar, happrox N, Or.inr (Or.inl hreg), ⟨contDiffOn_const, fun x _ => by simp⟩,
    continuousOn_const,
    ⟨NearestClosureBoundaryChoices.ofNonempty G (ball (0 : Euc d) 1) ⟨0, mem_ball_self one_pos⟩⟩⟩

/-- Premises of `TheoremBPartAStatement`: `HarmonicNearClosure` holds for the zero function
with the open neighbourhood `univ` of `closure U`. -/
theorem nonvac_theoremB_part_a_premises (d : ℕ) (hd : 1 ≤ d) :
    ∃ (G : TilingSequence d) (N : NearestVertexData G) (U : Set (Euc d)) (hC : Euc d → ℝ),
      IsDomain U ∧ Bornology.IsBounded U ∧ HasAmbientCollar U G.domain ∧
      N.ApproximationCondition ∧ PaperRegularity G ∧ HarmonicNearClosure hC U := by
  obtain ⟨G, hcollar, ⟨N⟩, happrox, hreg⟩ := SpherePackings.exists_lattice_tilingSequence hd
  exact ⟨G, N, ball (0 : Euc d) 1, fun _ => 0,
    (SpherePackings.isLipschitzDomain_ball hd).isDomain, isBounded_ball, hcollar, happrox N,
    Or.inr (Or.inl hreg), Set.univ, isOpen_univ, Set.subset_univ _,
    ⟨contDiffOn_const, fun x _ => by simp⟩⟩


end SpherePackings.Audit.Nonvacuity08
