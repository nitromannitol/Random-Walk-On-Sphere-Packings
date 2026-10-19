-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/WalkAdaptiveStopping.lean` at commit cf73d6e): its declarations that assume a
-- finite state space or a finite conductance network, for the chain of an arbitrary Markov
-- kernel on a measurable space.
import BouRabeeGwynne.WalkAdaptiveStopping
import SpherePackings.General.MarkovChain.Absorbed

/-! General-state-space version of `BouRabeeGwynne.WalkAdaptiveStopping`: the declarations of that file
that assume a finite state space or a finite conductance network. -/

open MeasureTheory ProbabilityTheory Set Preorder
set_option backward.isDefEq.respectTransparency false
namespace SpherePackings.MarkovChain

open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork BouRabeeGwynne.TrajectoryCoupling
variable {V J : Type*} [MeasurableSpace V] [MeasurableEq V]

omit [MeasurableEq V] in
/-- Dependence only on the observed prefix proves the canonical stopping-time condition,
provided the sublevel events `{τ ≤ n}` are measurable; in a finite state space that
measurability is automatic. -/
lemma isStoppingTime_of_prefix_invariant {τ : (ℕ → V) → WithTop ℕ}
    (h : ∀ n ω ω', frestrictLe n ω = frestrictLe n ω' →
      (τ ω ≤ n ↔ τ ω' ≤ n))
    (hmeas : ∀ n : ℕ, MeasurableSet {ω | τ ω ≤ n}) :
    IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => V)) τ := by
  intro n
  rw [Filtration.piLE_eq_comap_frestrictLe]
  let s : Set (Finset.Iic n → V) := {p | τ (paddedHistory n p).2 ≤ n}
  refine ⟨s, (hmeas n).preimage (measurable_snd.comp (measurable_paddedHistory n)), ?_⟩
  ext ω
  change τ (paddedHistory n (frestrictLe n ω)).2 ≤ n ↔ τ ω ≤ n
  apply h
  funext i
  simp only [paddedHistory, frestrictLe_apply,
    Nat.min_eq_left (Finset.mem_Iic.mp i.property)]

/-- Adaptive ball selection from the past gives an actual discrete stopping
time, without requiring finite exits on every sample path. The measurability of
the adaptive exit events, which finiteness of the state space used to provide, is
a hypothesis. -/
theorem isStoppingTime_nextSelectedExitTime {τ : (ℕ → V) → WithTop ℕ}
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => V)) τ)
    (B : J → Set V) (select : (ℕ × (ℕ → V)) → Option J)
    (hmeas : ∀ n : ℕ, MeasurableSet {ω | nextSelectedExitTime τ B select ω ≤ n}) :
    IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => V))
      (nextSelectedExitTime τ B select) := by
  refine isStoppingTime_of_prefix_invariant ?_ hmeas
  have transfer (n : ℕ) (ω ω' : ℕ → V)
      (hp : frestrictLe n ω = frestrictLe n ω')
      (ht : nextSelectedExitTime τ B select ω ≤ n) :
      nextSelectedExitTime τ B select ω' ≤ n := by
    have hle : τ ω ≤ n := (le_nextSelectedExitTime τ B select ω).trans ht
    have hfin : τ ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hle
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hfin
    have hkn : k ≤ n := by
      rw [← hk] at hle
      exact WithTop.coe_le_coe.mp hle
    have hk' : τ ω' = k := stopping_eq_of_prefix_eq hτ hp hkn hk.symm
    have hobs : observedHistory τ ω = observedHistory τ ω' :=
      observedHistory_eq_of_prefix_eq hτ hp hkn hk.symm
    unfold nextSelectedExitTime at ht ⊢
    rw [hk', ← hobs]
    rw [← hk] at ht
    cases hs : select (observedHistory τ ω) with
    | none =>
      simp only [add_zero]
      exact (WithTop.coe_le_coe (α := ℕ)).mpr hkn
    | some j =>
      simp only [hs] at ht ⊢
      rw [futureAt_of_eq hk']
      rw [futureAt_of_eq hk.symm] at ht
      obtain ⟨l, hl, hbad⟩ := (add_exitTime_shift_le_iff (B j) ω k n).mp ht
      apply (add_exitTime_shift_le_iff (B j) ω' k n).mpr
      exact ⟨l, hl, (eval_eq_of_prefix_eq hp hl) ▸ hbad⟩
  intro n ω ω' hp
  exact ⟨transfer n ω ω' hp, transfer n ω' ω hp.symm⟩

end SpherePackings.MarkovChain
