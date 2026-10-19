-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/Section3MassDecay.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.Section3InternalMass
import BouRabeeGwynne.Section3HarmonicIteration

/-! Geometric incident-mass decay of the actual harmonic-replacement sequence. -/

open scoped Classical BigOperators

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

noncomputable def finiteAmbientFunction (R : Set T.V) (f : R → ℝ) : T.V → ℝ :=
  Function.extend Subtype.val f (fun _ => 0)

@[simp] lemma finiteAmbientFunction_apply (R : Set T.V) (f : R → ℝ) (v : R) :
    T.finiteAmbientFunction R f v = f v :=
  Subtype.val_injective.extend_apply f (fun _ => 0) v

/-- Proposition 2.6 is used for every actual intermediate Dirichlet solution.
The geometric contraction is derived from the tiling, not supplied as a premise. -/
theorem harmonicIteration_mass_le_geometric (hd : 1 ≤ d)
    (R : Set T.V) [Fintype R] (A : Set R)
    (haccess : (T.finiteNetwork R).BoundaryAccessible A)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    (hcellD : ∀ v ∈ A, (T.cell v).carrier ⊆ interior T.domain)
    (g : R → ℝ) (e : Euc d) (he : e ≠ 0) (a b : ℝ) (hab : a ≤ b)
    (hheight : ∀ v ∈ A, ∀ x ∈ (T.cell v).carrier,
      inner ℝ e x / inner ℝ e e ∈ Set.Icc a b)
    {C τ L ℓ : ℝ} (hC : 0 ≤ C) (hτ : 0 < τ) (hℓ : 0 < ℓ)
    (hlength : ∀ v w : R, T.adj v w → ‖T.pos w - T.pos v‖ ≤ L)
    (henergy : ∀ S ⊆ A, ∀ h : R → ℝ,
      (T.finiteNetwork R).SolvesDirichlet S g h →
      (T.finiteNetwork R).energy (h - g) ≤ C ^ 2 * T.incidentMass R S)
    (hfactor : (d : ℝ) * ‖e‖ * (b - a) * C / τ + (L ^ 2 / ℓ ^ 2) * C ^ 2 ≤ 1 / 2) :
    ∀ j, T.incidentMass R
      ((T.finiteNetwork R).harmonicIteration A haccess g (fun _ => τ) (fun _ => ℓ) j).region ≤
      T.incidentMass R A * (1 / 2 : ℝ) ^ j := by
  let N := T.finiteNetwork R
  let s := N.harmonicIteration A haccess g (fun _ => τ) (fun _ => ℓ)
  have hsub (j : ℕ) : (s j).region ⊆ A :=
    N.harmonicIteration_region_antitone A haccess g (fun _ => τ) (fun _ => ℓ)
      (Nat.zero_le j)
  have hstep (j : ℕ) : T.incidentMass R (s (j + 1)).region ≤
      (1 / 2 : ℝ) * T.incidentMass R (s j).region := by
    let f := T.finiteAmbientFunction R ((s j).value - g)
    have hzero : ∀ v : R, v ∉ (s j).region → f v = 0 := by
      intro v hv
      simp only [f, T.finiteAmbientFunction_apply, Pi.sub_apply,
        (s j).solves.2 v hv, sub_self]
    have hE : T.incidentEnergy R (s j).region f ≤
        C ^ 2 * T.incidentMass R (s j).region := by
      rw [T.incidentEnergy_eq_networkEnergy R (s j).region f hzero]
      have heq : (fun v : R => f v) = (s j).value - g := by
        funext v
        exact T.finiteAmbientFunction_apply R _ v
      rw [heq]
      exact henergy _ (hsub j) _ (s j).solves
    have htrim := T.incidentMass_trimmed_le_contraction_factor hd R (s j).region
      (fun v hv => hneighbors v (hsub j hv))
      (fun v hv => hcellD v (hsub j hv)) f hzero e he a b hab
      (fun v hv => hheight v (hsub j hv)) hC hτ hℓ hlength hE
    have heq : (s (j + 1)).region = N.trimmedErrorSet (s j).region
        (fun v : R => f v) τ ℓ := by
      simp only [f, T.finiteAmbientFunction_apply]
      rfl
    rw [heq]
    exact htrim.trans (mul_le_mul_of_nonneg_right hfactor (T.incidentMass_nonneg _ _))
  intro j
  induction j with
  | zero =>
    simp [s, N, FiniteConductanceNetwork.harmonicIteration,
      FiniteConductanceNetwork.HarmonicIterationState.initial]
  | succ j ih =>
    calc
      _ ≤ (1 / 2 : ℝ) * T.incidentMass R (s j).region := hstep j
      _ ≤ (1 / 2 : ℝ) * (T.incidentMass R A * (1 / 2 : ℝ) ^ j) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; ring

end BouRabeeGwynne.OrthogonalTiling
