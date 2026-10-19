-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (files `BouRabeeGwynne/StoppedWalk.lean` and `WalkStrongMarkov.lean` at commit cf73d6e): the
-- absorbed walk of a finite conductance network is replaced by the chain of an arbitrary Markov
-- kernel absorbed outside a measurable set.
import SpherePackings.General.MarkovChain.Dirichlet

/-!
# Absorbed chains and the strong Markov property

`absorbedKernel κ hA` moves like `κ` inside the measurable set `A` and stays put outside it.  Its
chain is absorbed at its first exit from `A`.  The strong Markov property of the chain of any
Markov kernel at an almost surely finite stopping time: the observed history and the whole future
path have the joint law of the history and a fresh chain started at its last state.  Nothing here
depends on the paper.
-/

open MeasureTheory ProbabilityTheory Set Preorder
open BouRabeeGwynne BouRabeeGwynne.TrajectoryCoupling BouRabeeGwynne.FiniteConductanceNetwork

namespace SpherePackings.MarkovChain

variable {V : Type*} [MeasurableSpace V] (κ : Kernel V V) [IsMarkovKernel κ]

/-- The joint distribution of a history and its next state. -/
lemma law_history_next (a : V) (n : ℕ) :
    (law κ a).map (frestrictLe n) ⊗ₘ historyKernel κ n =
      (law κ a).map (fun ω ↦ (frestrictLe n ω, ω (n + 1))) :=
  Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure

/-! ### Absorption -/

/-- The kernel moving like `κ` in `A` and staying put outside `A`. -/
noncomputable def absorbedKernel {A : Set V} (hA : MeasurableSet A) : Kernel V V :=
  open Classical in Kernel.piecewise hA κ (Kernel.deterministic id measurable_id)

instance absorbedKernel_isMarkovKernel {A : Set V} (hA : MeasurableSet A) :
    IsMarkovKernel (absorbedKernel κ hA) := by
  unfold absorbedKernel
  infer_instance

omit [IsMarkovKernel κ] in
lemma absorbedKernel_of_mem {A : Set V} (hA : MeasurableSet A) {a : V} (ha : a ∈ A) :
    absorbedKernel κ hA a = κ a := by
  classical
  simp [absorbedKernel, Kernel.piecewise_apply, ha]

omit [IsMarkovKernel κ] in
lemma absorbedKernel_of_not_mem {A : Set V} (hA : MeasurableSet A) {a : V} (ha : a ∉ A) :
    absorbedKernel κ hA a = Measure.dirac a := by
  classical
  simp [absorbedKernel, Kernel.piecewise_apply, ha, Kernel.deterministic_apply]

/-! ### The strong Markov property -/

/-- A fresh chain started at the last state of an observed history. -/
noncomputable def observedRestartKernel : Kernel (ℕ × (ℕ → V)) (ℕ → V) :=
  (pathKernel κ).comap (fun h => h.2 h.1)
    (measurable_from_prod_countable_right fun n => measurable_pi_apply n)

instance observedRestartKernel_isMarkovKernel : IsMarkovKernel (observedRestartKernel κ) := by
  unfold observedRestartKernel
  infer_instance

lemma law_prefix_future_restrict (a : V) (n : ℕ) {s : Set (Finset.Iic n → V)}
    (hs : MeasurableSet s) :
    ((law κ a).restrict (frestrictLe n ⁻¹' s)).map (frestrictLe n) ⊗ₘ restartKernel κ n =
      ((law κ a).restrict (frestrictLe n ⁻¹' s)).map
        (fun ω => (frestrictLe n ω, walkShift n ω)) := by
  rw [← Measure.restrict_map (measurable_frestrictLe n) hs,
    TrajectoryCoupling.compProd_restrict_first _ _ hs, law_prefix_future κ a n,
    Measure.restrict_map ((measurable_frestrictLe n).prodMk (measurable_walkShift n))
      (hs.preimage measurable_fst)]
  rfl

lemma law_observed_future_slice (a : V) {τ : (ℕ → V) → WithTop ℕ}
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => V)) τ) (n : ℕ) :
    ((law κ a).restrict {ω | τ ω = n}).map (observedHistory τ) ⊗ₘ observedRestartKernel κ =
      ((law κ a).restrict {ω | τ ω = n}).map
        (fun ω => (observedHistory τ ω, futureAt τ ω)) := by
  obtain ⟨s, hs, hseq⟩ := stopping_event_prefix hτ n
  let μn := (law κ a).restrict {ω | τ ω = n}
  have hm : MeasurableSet {ω | τ ω = n} :=
    measurableSet_eq_fun hτ.measurable' measurable_const
  have hae : ∀ᵐ ω ∂μn, τ ω = n := ae_restrict_mem hm
  have hobs : μn.map (observedHistory τ) =
      μn.map (paddedHistory n ∘ frestrictLe n) := by
    apply Measure.map_congr
    filter_upwards [hae] with ω hω
    exact observedHistory_of_eq hω
  have hjoint : μn.map (fun ω => (observedHistory τ ω, futureAt τ ω)) =
      μn.map (fun ω => (paddedHistory n (frestrictLe n ω), walkShift n ω)) := by
    apply Measure.map_congr
    filter_upwards [hae] with ω hω
    rw [observedHistory_of_eq hω, futureAt_of_eq hω]
  have hrestart (h : Finset.Iic n → V) :
      (restartKernel κ n h).map id = observedRestartKernel κ (paddedHistory n h) := by
    rw [Measure.map_id]
    simp only [restartKernel, observedRestartKernel, Kernel.comap_apply, paddedHistory,
      min_self]
  have hprefix := law_prefix_future_restrict κ a n hs
  rw [hseq] at hprefix
  change μn.map (frestrictLe n) ⊗ₘ restartKernel κ n = _ at hprefix
  change μn.map (observedHistory τ) ⊗ₘ observedRestartKernel κ = _
  rw [hobs, hjoint,
    ← Measure.map_map (measurable_paddedHistory n) (measurable_frestrictLe n),
    ← compProd_map_prod_of_kernel_map _ _ _ _ _ (measurable_paddedHistory n)
      measurable_id hrestart,
    hprefix,
    Measure.map_map ((measurable_paddedHistory n).prodMap measurable_id)
      ((measurable_frestrictLe n).prodMk (measurable_walkShift n))]
  rfl

/-- **Strong Markov property**: at an almost surely finite stopping time, the observed history
and the whole future path have the law of the history and a fresh chain started at its last
state. -/
theorem law_observed_future (a : V) {τ : (ℕ → V) → WithTop ℕ}
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => V)) τ)
    (hfin : ∀ᵐ ω ∂law κ a, τ ω ≠ ⊤) :
    (law κ a).map (observedHistory τ) ⊗ₘ observedRestartKernel κ =
      (law κ a).map (fun ω => (observedHistory τ ω, futureAt τ ω)) := by
  have hμ := measure_eq_sum_stopping_slices (law κ a) hτ.measurable' hfin
  have hobs := measurable_observedHistory hτ.measurable'
  have hjoint := hobs.prodMk (measurable_futureAt hτ.measurable')
  calc
    _ = (Measure.sum (fun n : ℕ => (law κ a).restrict {ω | τ ω = n})).map
          (observedHistory τ) ⊗ₘ observedRestartKernel κ := by rw [← hμ]
    _ = Measure.sum (fun n : ℕ =>
        ((law κ a).restrict {ω | τ ω = n}).map (observedHistory τ)
          ⊗ₘ observedRestartKernel κ) := by
      rw [Measure.map_sum hobs.aemeasurable, Measure.compProd_sum_left]
    _ = Measure.sum (fun n : ℕ =>
        ((law κ a).restrict {ω | τ ω = n}).map
          (fun ω => (observedHistory τ ω, futureAt τ ω))) := by
      congr 1
      funext n
      exact law_observed_future_slice κ a hτ n
    _ = _ := by rw [← Measure.map_sum hjoint.aemeasurable, ← hμ]

variable [MeasurableEq V]

omit [MeasurableEq V] in
/-- The chain starts at its starting state, almost surely. -/
lemma law_ae_start [MeasurableSingletonClass V] (a : V) : ∀ᵐ ω ∂law κ a, ω 0 = a := by
  have h : ∀ᵐ x ∂(law κ a).map (fun ω => ω 0), x = a := by
    rw [law_map_eval_zero]
    exact (ae_dirac_iff (measurableSet_singleton a)).mpr rfl
  exact ae_of_ae_map (measurable_pi_apply 0).aemeasurable h

/-- At any fixed time, a chain already outside `A` remains at its current state. -/
lemma law_absorbed_ae_absorbing_step {A : Set V} (hA : MeasurableSet A) (a : V) (n : ℕ) :
    ∀ᵐ ω ∂law (absorbedKernel κ hA) a, ω n ∉ A → ω (n + 1) = ω n := by
  have hmeas : MeasurableSet {q : (Finset.Iic n → V) × V |
      q.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩ ∉ A → q.2 = q.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩} := by
    have h1 : MeasurableSet {q : (Finset.Iic n → V) × V | q.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩ ∈ A} :=
      ((measurable_pi_apply _).comp measurable_fst) hA
    have h2 : MeasurableSet {q : (Finset.Iic n → V) × V |
        q.2 = q.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩} :=
      measurableSet_eq_fun measurable_snd ((measurable_pi_apply _).comp measurable_fst)
    have : {q : (Finset.Iic n → V) × V |
        q.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩ ∉ A → q.2 = q.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩} =
        {q | q.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩ ∈ A} ∪
          {q | q.2 = q.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩} := by
      ext q
      simp only [mem_ofPred_eq, mem_union]
      tauto
    rw [this]
    exact h1.union h2
  have hpair : ∀ᵐ q ∂(law (absorbedKernel κ hA) a).map
      (fun ω ↦ (frestrictLe n ω, ω (n + 1))),
      q.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩ ∉ A →
        q.2 = q.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩ := by
    rw [← law_history_next]
    apply Measure.ae_compProd_of_ae_ae hmeas
    apply Filter.Eventually.of_forall
    intro h
    by_cases hh : h ⟨n, Finset.mem_Iic.mpr le_rfl⟩ ∈ A
    · exact Filter.Eventually.of_forall fun w hw ↦ (hw hh).elim
    · change ∀ᵐ w ∂(absorbedKernel κ hA (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)),
        h ⟨n, Finset.mem_Iic.mpr le_rfl⟩ ∉ A → w = h ⟨n, Finset.mem_Iic.mpr le_rfl⟩
      rw [absorbedKernel_of_not_mem κ hA hh]
      have hset : {w : V | h ⟨n, Finset.mem_Iic.mpr le_rfl⟩ ∉ A →
          w = h ⟨n, Finset.mem_Iic.mpr le_rfl⟩} = {h ⟨n, Finset.mem_Iic.mpr le_rfl⟩} := by
        ext w
        simp [hh]
      rw [ae_dirac_iff (by rw [hset]; exact measurableSet_singleton _)]
      exact fun _ => rfl
  exact ae_of_ae_map (by fun_prop) hpair

/-- Absorption holds simultaneously at all times, almost surely. -/
lemma law_absorbed_ae_absorbed {A : Set V} (hA : MeasurableSet A) (a : V) :
    ∀ᵐ ω ∂law (absorbedKernel κ hA) a, IsAbsorbedPath A ω :=
  ae_all_iff.mpr (law_absorbed_ae_absorbing_step κ hA a)

end SpherePackings.MarkovChain
