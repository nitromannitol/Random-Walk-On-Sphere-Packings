module

-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/WalkSelectedRestart.lean` at commit cf73d6e): its declarations that assume a
-- finite state space or a finite conductance network, for the chain of an arbitrary Markov
-- kernel on a measurable space.
public import BouRabeeGwynne.WalkSelectedRestart
public import SpherePackings.General.MarkovChain.Absorbed
public import SpherePackings.General.Walk.SkeletonKernels
public import SpherePackings.General.Walk.WalkAbsorption

@[expose] public section

/-! General-state-space version of `BouRabeeGwynne.WalkSelectedRestart`: the declarations of that file
that assume a finite state space or a finite conductance network. -/

open MeasureTheory ProbabilityTheory Set
namespace SpherePackings.MarkovChain

open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork BouRabeeGwynne.TrajectoryCoupling
variable {d : ℕ} {V J : Type*} [MeasurableSpace V] [MeasurableEq V]
  [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

omit [MeasurableEq V] in
lemma measurable_selectedClockedExcursion (pos : V → Euc d) (B : J → Set V)
    (hpos : Measurable pos) (hB : ∀ j, MeasurableSet (B j)) :
    Measurable (fun p : (Option J × V) × (ℕ → V) =>
      selectedClockedExcursion pos B p.1 p.2) := by
  have hcurry : Measurable (fun q : Option J × (V × (ℕ → V)) =>
      selectedClockedExcursion pos B (q.1, q.2.1) q.2.2) := by
    apply measurable_from_prod_countable_right
    rintro (_ | j)
    · change Measurable (fun q : V × (ℕ → V) => (true, ClockedWalkExcursion.constant (pos q.1)))
      exact measurable_const.prodMk
        (ClockedWalkExcursion.measurable_constant.comp (hpos.comp measurable_fst))
    · change Measurable (fun q : V × (ℕ → V) => (false, ClockedWalkExcursion.ofWalk pos (B j) q.2))
      exact measurable_const.prodMk ((measurable_ofWalk hpos (hB j)).comp measurable_snd)
  exact hcurry.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))

variable (κ : Kernel V V) [IsMarkovKernel κ]
/-- This is the same selected kernel used by the coupled skeleton, pulled
back along the actual observed terminal vertex and the past-dependent choice. -/
noncomputable def selectedClockedRestartKernel (pos : V → Euc d) (hpos : Measurable pos)
    (B : J → Set V) (hB : ∀ j, MeasurableSet (B j))
    (select : (ℕ × (ℕ → V)) → Option J) (hs : Measurable select) :
    Kernel (ℕ × (ℕ → V)) (Bool × ClockedWalkExcursion d) :=
  (selectedExcursionKernel (fun j => clockedWalkExcursionKernel κ pos (hB j))
    (ClockedWalkExcursion.constant ∘ pos)
    (ClockedWalkExcursion.measurable_constant.comp hpos)).comap
      (fun h => (select h, h.2 h.1)) (hs.prodMk measurable_historyLast)

instance selectedClockedRestartKernel_isMarkov (pos : V → Euc d) (hpos : Measurable pos)
    (B : J → Set V) (hB : ∀ j, MeasurableSet (B j))
    (select : (ℕ × (ℕ → V)) → Option J) (hs : Measurable select) :
    IsMarkovKernel (selectedClockedRestartKernel κ pos hpos B hB select hs) := by
  unfold selectedClockedRestartKernel
  have : ∀ j, IsMarkovKernel (clockedWalkExcursionKernel κ pos (hB j)) :=
    fun j => clockedWalkExcursionKernel_isMarkov κ hpos (hB j)
  infer_instance

lemma observedRestartKernel_map_selectedClockedExcursion (pos : V → Euc d)
    (hpos : Measurable pos) {A : Set V} (B : J → Set V) (hBA : ∀ j, B j ⊆ A)
    (hA : MeasurableSet A)
    (hB : ∀ j, MeasurableSet (B j))
    (select : (ℕ × (ℕ → V)) → Option J) (hs : Measurable select)
    (h : ℕ × (ℕ → V)) :
    (observedRestartKernel (absorbedKernel κ hA) h).map
        (selectedClockedExcursion pos B (select h, h.2 h.1)) =
      selectedClockedRestartKernel κ pos hpos B hB select hs h := by
  have hlaw : observedRestartKernel (absorbedKernel κ hA) h =
      law (absorbedKernel κ hA) (h.2 h.1) := by
    rw [observedRestartKernel, Kernel.comap_apply, pathKernel_apply]
  rw [hlaw]
  change (law (absorbedKernel κ hA) (h.2 h.1)).map
      (selectedClockedExcursion pos B (select h, h.2 h.1)) =
    selectedExcursionKernel (fun j => clockedWalkExcursionKernel κ pos (hB j))
      (ClockedWalkExcursion.constant ∘ pos)
      (ClockedWalkExcursion.measurable_constant.comp hpos)
      (select h, h.2 h.1)
  cases hj : select h with
  | none =>
    change (law (absorbedKernel κ hA) (h.2 h.1)).map
      (fun _ : ℕ → V => (true, ClockedWalkExcursion.constant (pos (h.2 h.1)))) =
      Measure.dirac (true, ClockedWalkExcursion.constant (pos (h.2 h.1)))
    rw [Measure.map_const, measure_univ, one_smul]
  | some j =>
    rw [selectedExcursionKernel_some]
    change (law (absorbedKernel κ hA) (h.2 h.1)).map
        ((fun e => (false, e)) ∘ ClockedWalkExcursion.ofWalk pos (B j)) = _
    have hmark : Measurable (fun e : ClockedWalkExcursion d => (false, e)) :=
      measurable_const.prodMk measurable_id
    rw [← Measure.map_map hmark (measurable_ofWalk hpos (hB j)),
      trajectoryLaw_map_clockedExcursion κ pos hpos (hBA j) hA (hB j)]

/-- The entire observed past and the next selected whole excursion have the
joint law given by the genuine selected kernel. The first component has not
been replaced by the endpoint marginal. -/
theorem trajectoryLaw_observed_selectedExcursion (pos : V → Euc d) (hpos : Measurable pos)
    {A : Set V} (B : J → Set V) (hBA : ∀ j, B j ⊆ A)
    (hA : MeasurableSet A)
    (hB : ∀ j, MeasurableSet (B j))
    (select : (ℕ × (ℕ → V)) → Option J) (hs : Measurable select) (v : V)
    {τ : (ℕ → V) → WithTop ℕ}
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => V)) τ)
    (hfin : ∀ᵐ ω ∂law (absorbedKernel κ hA) v, τ ω ≠ ⊤) :
    (law (absorbedKernel κ hA) v).map (fun ω =>
      (observedHistory τ ω, selectedClockedExcursion pos B
        (select (observedHistory τ ω), (observedHistory τ ω).2 (observedHistory τ ω).1)
        (futureAt τ ω))) =
      (law (absorbedKernel κ hA) v).map (observedHistory τ)
        ⊗ₘ selectedClockedRestartKernel κ pos hpos B hB select hs := by
  let g : (ℕ × (ℕ → V)) → (ℕ → V) → Bool × ClockedWalkExcursion d :=
    fun h ω => selectedClockedExcursion pos B (select h, h.2 h.1) ω
  have hg : Measurable (fun p : (ℕ × (ℕ → V)) × (ℕ → V) => g p.1 p.2) :=
    (measurable_selectedClockedExcursion pos B hpos hB).comp
      (((hs.prodMk measurable_historyLast).comp measurable_fst).prodMk measurable_snd)
  have hobs := measurable_observedHistory hτ.measurable'
  have hfuture := measurable_futureAt hτ.measurable'
  have hpair : Measurable (fun p : (ℕ × (ℕ → V)) × (ℕ → V) =>
      (id p.1, g p.1 p.2)) := measurable_fst.prodMk hg
  have hjoint : Measurable (fun ω : ℕ → V => (observedHistory τ ω, futureAt τ ω)) :=
    hobs.prodMk hfuture
  have hfactor := compProd_map_dependent_of_kernel_map
    ((law (absorbedKernel κ hA) v).map (observedHistory τ))
    (observedRestartKernel (absorbedKernel κ hA))
    (selectedClockedRestartKernel κ pos hpos B hB select hs)
    id g measurable_id hg
    (observedRestartKernel_map_selectedClockedExcursion κ pos hpos B hBA hA hB select hs)
  rw [Measure.map_id, law_observed_future (absorbedKernel κ hA) v hτ hfin,
    Measure.map_map hpair hjoint] at hfactor
  exact hfactor

end SpherePackings.MarkovChain
