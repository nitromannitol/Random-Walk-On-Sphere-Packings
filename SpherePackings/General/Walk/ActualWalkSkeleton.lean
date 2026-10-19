-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/ActualWalkSkeleton.lean` at commit cf73d6e): its declarations that assume a
-- finite state space or a finite conductance network, for the chain of an arbitrary Markov
-- kernel on a measurable space.
import BouRabeeGwynne.ActualWalkSkeleton
import SpherePackings.General.MarkovChain.Absorbed
import SpherePackings.General.Walk.SkeletonKernels
import SpherePackings.General.Walk.WalkAdaptiveStopping
import SpherePackings.General.Walk.WalkSelectedRestart

/-! General-state-space version of `BouRabeeGwynne.ActualWalkSkeleton`: the declarations of that file
that assume a finite state space or a finite conductance network. -/

open MeasureTheory ProbabilityTheory Set
set_option backward.isDefEq.respectTransparency false
namespace SpherePackings.MarkovChain

open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork BouRabeeGwynne.TrajectoryCoupling
variable {d : ℕ} {V J : Type*} [MeasurableSpace V] [MeasurableEq V] [Countable J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

omit [MeasurableEq V] in
/-- The adaptive exit time is measurable once the stopping time, the selector and the exit
sets are measurable. For a finite state space this measurability was automatic. -/
lemma measurable_nextSelectedExitTime {τ : (ℕ → V) → WithTop ℕ} (hτ : Measurable τ)
    (B : J → Set V) (hB : ∀ j, MeasurableSet (B j)) (select : ℕ × (ℕ → V) → Option J)
    (hs : Measurable select) :
    Measurable (nextSelectedExitTime τ B select) := by
  have hH : Measurable (fun p : Option J × (ℕ → V) =>
      match p.1 with
      | none => (0 : WithTop ℕ)
      | some j => exitTime (B j) p.2) := by
    refine measurable_from_prod_countable_right fun o => ?_
    cases o with
    | none => exact measurable_const
    | some j => exact measurable_exitTime (hB j)
  have hG : Measurable (fun ω : ℕ → V => (select (observedHistory τ ω), futureAt τ ω)) :=
    (hs.comp (measurable_observedHistory hτ)).prodMk (measurable_futureAt hτ)
  have hsum : Measurable (fun p : WithTop ℕ × WithTop ℕ => p.1 + p.2) := Measurable.of_discrete
  unfold nextSelectedExitTime
  exact hsum.comp (hτ.prodMk (hH.comp hG))

omit [MeasurableEq V] in
lemma measurableSet_nextSelectedExitTime_le {τ : (ℕ → V) → WithTop ℕ} (hτ : Measurable τ)
    (B : J → Set V) (hB : ∀ j, MeasurableSet (B j)) (select : ℕ × (ℕ → V) → Option J)
    (hs : Measurable select) (n : ℕ) :
    MeasurableSet {ω | nextSelectedExitTime τ B select ω ≤ n} := by
  have hI : MeasurableSet (Set.Iic (n : WithTop ℕ)) := (Set.to_countable _).measurableSet
  exact measurable_nextSelectedExitTime hτ B hB select hs hI

omit [Countable J] [MeasurableSingletonClass (Option J)] in
lemma measurable_walkStageSelector
    {previous : (ℕ → V) → WithTop ℕ × (Bool × ClockedWalkExcursion d)}
    (hp : Measurable previous) (select : V → Option J) (hselect : Measurable select) :
    Measurable (walkStageSelector previous select) := by
  unfold walkStageSelector
  exact Measurable.ite
    (measurableSet_eq_fun (hp.snd.fst.comp measurable_snd) measurable_const)
    measurable_const (hselect.comp measurable_historyLast)

/-- Every stage is measurable and its clock is a stopping time, proved together by induction
on the stage. -/
lemma actualWalkStage_measurable_and_isStoppingTime (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → V → Option J) (hpos : Measurable pos)
    (hB : ∀ j, MeasurableSet (B j)) (hselect : ∀ n, Measurable (select n)) (n : ℕ) :
    Measurable (actualWalkStage pos B initial select n) ∧
      IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => V))
        (fun ω => (actualWalkStage pos B initial select n ω).1) := by
  induction n with
  | zero =>
    exact ⟨(exitTime_isStoppingTime' (hB initial)).measurable'.prodMk
      (measurable_const.prodMk (measurable_ofWalk hpos (hB initial))),
      exitTime_isStoppingTime' (hB initial)⟩
  | succ n ih =>
    obtain ⟨hstage, hτ⟩ := ih
    let τ := fun ω => (actualWalkStage pos B initial select n ω).1
    have hτm : Measurable τ := hτ.measurable'
    have hchoice := measurable_walkStageSelector hstage (select n) (hselect n)
    have hclock : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => V))
        (fun ω => (actualWalkStage pos B initial select (n + 1) ω).1) :=
      isStoppingTime_nextSelectedExitTime hτ B
        (walkStageSelector (actualWalkStage pos B initial select n) (select n))
        (fun m => measurableSet_nextSelectedExitTime_le hτm B hB _ hchoice m)
    have hobs := measurable_observedHistory hτm
    have hparameters : Measurable (fun ω =>
        (walkStageSelector (actualWalkStage pos B initial select n) (select n)
          (observedHistory τ ω), (observedHistory τ ω).2 (observedHistory τ ω).1)) :=
      (hchoice.comp hobs).prodMk (measurable_historyLast.comp hobs)
    exact ⟨hclock.measurable'.prodMk
      ((measurable_selectedClockedExcursion pos B hpos hB).comp
        (hparameters.prodMk (measurable_futureAt hτm))), hclock⟩

theorem actualWalkStage_clock_isStoppingTime (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → V → Option J) (hpos : Measurable pos)
    (hB : ∀ j, MeasurableSet (B j)) (hselect : ∀ n, Measurable (select n)) (n : ℕ) :
    IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => V))
      (fun ω => (actualWalkStage pos B initial select n ω).1) :=
  (actualWalkStage_measurable_and_isStoppingTime pos B initial select hpos hB hselect n).2

theorem measurable_actualWalkStage (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → V → Option J) (hpos : Measurable pos)
    (hB : ∀ j, MeasurableSet (B j)) (hselect : ∀ n, Measurable (select n)) (n : ℕ) :
    Measurable (actualWalkStage pos B initial select n) :=
  (actualWalkStage_measurable_and_isStoppingTime pos B initial select hpos hB hselect n).1

lemma actualWalkStage_flag_eq_of_prefix (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → V → Option J) (hpos : Measurable pos)
    (hB : ∀ j, MeasurableSet (B j)) (hselect : ∀ n, Measurable (select n)) (i n : ℕ) {ω ω' : ℕ → V}
    (hp : Preorder.frestrictLe n ω = Preorder.frestrictLe n ω')
    (ht : (actualWalkStage pos B initial select i ω).1 ≤ n) :
    (actualWalkStage pos B initial select i ω).2.1 =
      (actualWalkStage pos B initial select i ω').2.1 := by
  cases i with
  | zero => rfl
  | succ i =>
    let τ := fun ξ => (actualWalkStage pos B initial select i ξ).1
    let choice := walkStageSelector (actualWalkStage pos B initial select i) (select i)
    have hτn : τ ω ≤ n :=
      ((actualWalkStage_clock_mono pos B initial select ω) (Nat.le_succ i)).trans ht
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp
      (ne_top_of_le_ne_top WithTop.coe_ne_top hτn)
    have hkn : k ≤ n := (WithTop.coe_le_coe (α := ℕ)).mp (hk.trans_le hτn)
    have hobs := observedHistory_eq_of_prefix_eq
      (actualWalkStage_clock_isStoppingTime pos B initial select hpos hB hselect i) hp hkn hk.symm
    change (selectedClockedExcursion pos B
      (choice (observedHistory τ ω), (observedHistory τ ω).2 (observedHistory τ ω).1)
      (futureAt τ ω)).1 =
      (selectedClockedExcursion pos B
      (choice (observedHistory τ ω'), (observedHistory τ ω').2 (observedHistory τ ω').1)
      (futureAt τ ω')).1
    rw [← hobs]
    cases choice (observedHistory τ ω) <;> rfl

/-- The full clock, flag, duration and all padded vertices of an observed
excursion depend only on the original path up to its elapsed clock. -/
lemma actualWalkStage_eq_of_prefix (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → V → Option J) (hpos : Measurable pos)
    (hB : ∀ j, MeasurableSet (B j)) (hselect : ∀ n, Measurable (select n)) (i n : ℕ) {ω ω' : ℕ → V}
    (hp : Preorder.frestrictLe n ω = Preorder.frestrictLe n ω')
    (ht : (actualWalkStage pos B initial select i ω).1 ≤ n) :
    actualWalkStage pos B initial select i ω = actualWalkStage pos B initial select i ω' := by
  obtain ⟨l, hl⟩ := WithTop.ne_top_iff_exists.mp
    (ne_top_of_le_ne_top WithTop.coe_ne_top ht)
  have hln : l ≤ n := (WithTop.coe_le_coe (α := ℕ)).mp (hl.trans_le ht)
  have hl' := stopping_eq_of_prefix_eq
    (actualWalkStage_clock_isStoppingTime pos B initial select hpos hB hselect i) hp hln hl.symm
  apply Prod.ext
  · exact hl.symm.trans hl'.symm
  apply Prod.ext
  · exact actualWalkStage_flag_eq_of_prefix pos B initial select hpos hB hselect i n hp ht
  cases i with
  | zero =>
    rw [actualWalkStage_zero_segment pos B initial select ω l hl.symm,
      actualWalkStage_zero_segment pos B initial select ω' l hl']
    exact clockedWalkSegment_eq_of_prefix pos (Nat.zero_le l) hln hp
  | succ i =>
    have hprev : (actualWalkStage pos B initial select i ω).1 ≤ (l : WithTop ℕ) :=
      ((actualWalkStage_clock_mono pos B initial select ω) (Nat.le_succ i)).trans_eq hl.symm
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp
      (ne_top_of_le_ne_top WithTop.coe_ne_top hprev)
    have hkl : k ≤ l := (WithTop.coe_le_coe (α := ℕ)).mp (hk.trans_le hprev)
    have hk' := stopping_eq_of_prefix_eq
      (actualWalkStage_clock_isStoppingTime pos B initial select hpos hB hselect i) hp
      (hkl.trans hln) hk.symm
    rw [actualWalkStage_succ_segment pos B initial select i ω k l hk.symm hl.symm,
      actualWalkStage_succ_segment pos B initial select i ω' k l hk' hl']
    exact clockedWalkSegment_eq_of_prefix pos hkl hln hp

lemma actualWalkStage_observedPast (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → V → Option J) (hpos : Measurable pos)
    (hB : ∀ j, MeasurableSet (B j)) (hselect : ∀ n, Measurable (select n)) (i : ℕ) (ω : ℕ → V)
    (hfin : (actualWalkStage pos B initial select i ω).1 ≠ ⊤) :
    actualWalkStage pos B initial select i
      (observedHistory (fun ξ => (actualWalkStage pos B initial select i ξ).1) ω).2 =
      actualWalkStage pos B initial select i ω := by
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hfin
  have hp : Preorder.frestrictLe k ω = Preorder.frestrictLe k
      (observedHistory (fun ξ => (actualWalkStage pos B initial select i ξ).1) ω).2 := by
    rw [observedHistory_of_eq hk.symm]
    funext j
    simp only [paddedHistory, Preorder.frestrictLe_apply,
      Nat.min_eq_left (Finset.mem_Iic.mp j.property)]
  exact (actualWalkStage_eq_of_prefix pos B initial select hpos hB hselect i k hp hk.symm.le).symm

lemma actualWalkStage_stopped_permanent (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → V → Option J) (hpos : Measurable pos)
    (hB : ∀ j, MeasurableSet (B j)) (hselect : ∀ n, Measurable (select n)) (i : ℕ) (ω : ℕ → V)
    (hfin : (actualWalkStage pos B initial select i ω).1 ≠ ⊤)
    (hstop : (actualWalkStage pos B initial select i ω).2.1 = true) :
    (actualWalkStage pos B initial select (i + 1) ω).2.1 = true := by
  let τ := fun ξ => (actualWalkStage pos B initial select i ξ).1
  let h := observedHistory τ ω
  have hflag : (actualWalkStage pos B initial select i h.2).2.1 = true := by
    rw [actualWalkStage_observedPast pos B initial select hpos hB hselect i ω hfin]
    exact hstop
  have hchoice : walkStageSelector (actualWalkStage pos B initial select i) (select i) h = none := by
    simp only [walkStageSelector, hflag, ↓reduceIte]
  change (selectedClockedExcursion pos B
    (walkStageSelector (actualWalkStage pos B initial select i) (select i) h, h.2 h.1)
    (futureAt τ ω)).1 = true
  rw [hchoice]
  rfl

/-- All actual recursive clocks are finite on one common probability-one
event, derived from almost-sure finiteness of the ambient exit time rather than postulated per stage. -/
theorem actualWalkStage_ae_all_clocks_finite (κ : Kernel V V) [IsMarkovKernel κ]
    (pos : V → Euc d) {A : Set V} (B : J → Set V) (hBA : ∀ j, B j ⊆ A)
    (hA : MeasurableSet A) (hexit : ∀ v, ∀ᵐ ω ∂law (absorbedKernel κ hA) v, exitTime A ω ≠ ⊤)
    (initial : J) (select : ℕ → V → Option J) (v : V) :
    ∀ᵐ ω ∂law (absorbedKernel κ hA) v, ∀ n,
      (actualWalkStage pos B initial select n ω).1 ≠ ⊤ := by
  filter_upwards [hexit v] with ω hω
  intro n
  exact ne_top_of_le_ne_top hω
    (actualWalkStage_clock_le_ambientExit pos B hBA initial select ω n)

end SpherePackings.MarkovChain
