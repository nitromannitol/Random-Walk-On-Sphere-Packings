module

public import SpherePackings.Support.Counterexample.Construction
public import BouRabeeGwynne.StoppedCurveLaws

@[expose] public section

/-!
# Simple random walk on a sphere packing, stopped on leaving a domain

The process of Theorem 6.1 (`rw-spheres.tex:1791-1794`): simple random walk on the tangency graph of
a sphere packing, with unit conductance on every edge, its positions scaled by a factor `c`, stopped
on leaving a domain `U`.  The law is defined exactly as `BouRabeeGwynne.IsStoppedTilingWalkLaw`,
with the tiling conductances replaced by unit conductances: the walk runs on the finite set of
spheres whose scaled centres lie in `U`, together with their neighbours and the starting sphere,
and the curve is the polygonal interpolation of the scaled centres, normalized to `[0,1]` and stopped
at the first vertex outside `U`.
-/

open MeasureTheory
open scoped ENNReal

namespace SpherePackings

open BouRabeeGwynne

namespace SpherePacking

variable {d : ℕ} (P : SpherePacking d)

lemma tangent_irrefl (i : P.ι) : ¬ P.Tangent i i := fun h => h.1 rfl

lemma tangent_symm {i j : P.ι} (h : P.Tangent i j) : P.Tangent j i :=
  ⟨Ne.symm h.1, by rw [dist_comm, h.2, add_comm]⟩

/-- Spheres whose centres, scaled by `c`, lie in `U`. -/
def interiorSpheres (c : ℝ) (U : Set (Euc d)) : Set P.ι :=
  {i | c • P.center i ∈ U}

/-- The closed region: the interior spheres and the spheres touching one of them. -/
def closedRegion (c : ℝ) (U : Set (Euc d)) : Set P.ι :=
  P.interiorSpheres c U ∪ {j | j ∉ P.interiorSpheres c U ∧ ∃ i ∈ P.interiorSpheres c U, P.Tangent i j}

/-- Unit conductances on the tangency graph, restricted to a finite set of spheres. -/
noncomputable def unitNetwork (R : Set P.ι) [Fintype R] : FiniteConductanceNetwork R := by
  classical
  exact {
    a := fun v w => if P.Tangent v w then 1 else 0
    symm := fun v w => by
      by_cases h : P.Tangent v w
      · simp [h, P.tangent_symm h]
      · have h' : ¬ P.Tangent w v := fun h' => h (P.tangent_symm h')
        simp [h, h']
    nonneg := fun v w => by split_ifs <;> norm_num
    loop_zero := fun v => by simp [P.tangent_irrefl] }

/-- `μ` is the law of simple random walk on the tangency graph, with centres scaled by `c`, started
at the sphere `i₀` and stopped on leaving `U`. -/
def IsStoppedSRWLaw (c : ℝ) (U : Set (Euc d)) (i₀ : P.ι) (μ : Measure (CurveSpace d)) : Prop := by
  classical
  exact ∃ (R : Finset P.ι) (_hR : (R : Set P.ι) = P.closedRegion c U ∪ {i₀}),
    letI : MeasurableSpace R := ⊤
    let A : Set R := {v | c • P.center v.val ∈ U}
    let N := P.unitNetwork (R : Set P.ι)
    ∃ (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (start : R), start.val = i₀ ∧
      let law := N.trajectoryLaw A hpos start
      let curve := stoppedPolygonalCurve (fun v : R => c • P.center v.val) A
      AEMeasurable curve law ∧
      (∀ᵐ ω ∂law, FiniteConductanceNetwork.exitTime A ω ≠ ⊤) ∧
      IsProbabilityMeasure μ ∧ μ = law.map curve

end SpherePacking

end SpherePackings
