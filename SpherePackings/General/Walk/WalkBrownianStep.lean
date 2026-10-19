-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/WalkBrownianStep.lean` at commit cf73d6e): its declarations that assume a
-- finite state space or a finite conductance network, for the chain of an arbitrary Markov
-- kernel on a measurable space.
import BouRabeeGwynne.WalkBrownianStep
import SpherePackings.General.MarkovChain.Absorbed
import SpherePackings.General.Walk.DiscreteHarmonicMeasure
import SpherePackings.General.Walk.SkeletonKernels
import SpherePackings.General.Walk.WalkBrownianCellMeasures
import SpherePackings.General.Walk.WalkBrownianCoupling
import SpherePackings.General.Walk.WalkSkeletonKernel

/-! General-state-space version of `BouRabeeGwynne.WalkBrownianStep`: the declarations of that file
that assume a finite state space or a finite conductance network. -/

set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Preorder
open scoped unitInterval ENNReal
namespace SpherePackings.MarkovChain

open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork BouRabeeGwynne.TrajectoryCoupling
variable {d : ℕ} {V J : Type*} [MeasurableSpace V] [MeasurableEq V]
  [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
variable (κ : Kernel V V) [IsMarkovKernel κ]
  (pos : V → Euc d) (hpos : MeasurableEmbedding pos) (B : J → Set V)
  (hB : ∀ j, MeasurableSet (B j))
  (select : ℕ → Euc d → Option J) (hs : ∀ n, Measurable (select n))

omit [MeasurableEq V] in
lemma walkSkeletonHistoryKernel_active_row (n : ℕ)
    (h : Finset.Iic n → Bool × ClockedWalkExcursion d)
    (hflag : (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).1 = false)
    (v : V) (hv : ClockedWalkExcursion.endPoint (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2 = pos v)
    (j : J) (hj : select n (pos v) = some j) :
    walkSkeletonHistoryKernel κ pos hpos B hB select hs n h =
      (clockedWalkExcursionKernel κ pos (hB j) v).map (fun e => (false, e)) := by
  let e := (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2
  have hp : h ⟨n, Finset.mem_Iic.mpr le_rfl⟩ = (false, e) := Prod.ext hflag rfl
  change absorbingExcursionKernel (fun j => spatialClockedExcursionKernel κ pos hpos (B j) (hB j))
    ClockedWalkExcursion.endPoint ClockedWalkExcursion.measurable_endPoint
    ClockedWalkExcursion.constant ClockedWalkExcursion.measurable_constant
    (select n) (hs n) (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) = _
  rw [hp, absorbingExcursionKernel_false_some _ _ _ _ _ _ _ e j (by rw [hv]; exact hj)]
  rw [hv, spatialClockedExcursionKernel_vertex κ]

omit [MeasurableEq V] in
lemma walkSkeletonHistoryKernel_constant_row (n : ℕ)
    (h : Finset.Iic n → Bool × ClockedWalkExcursion d)
    (hstop : (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).1 = true ∨
      select n (ClockedWalkExcursion.endPoint (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2) = none) :
    walkSkeletonHistoryKernel κ pos hpos B hB select hs n h =
      Measure.dirac (true, ClockedWalkExcursion.constant
        (ClockedWalkExcursion.endPoint (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2)) := by
  change absorbingExcursionKernel (fun j => spatialClockedExcursionKernel κ pos hpos (B j) (hB j))
    ClockedWalkExcursion.endPoint ClockedWalkExcursion.measurable_endPoint
    ClockedWalkExcursion.constant ClockedWalkExcursion.measurable_constant
    (select n) (hs n) (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) = _
  generalize hp : h ⟨n, Finset.mem_Iic.mpr le_rfl⟩ = p at hstop ⊢
  rcases p with ⟨flag, e⟩
  cases flag with
  | true => rfl
  | false =>
    have hn : select n (ClockedWalkExcursion.endPoint e) = none := hstop.resolve_left Bool.false_ne_true
    exact absorbingExcursionKernel_false_none _ _ _ _ _ _ _ e hn

variable (U : J → Set (Euc d)) (hU : ∀ j, IsOpen (U j))
  (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ]
variable (m : ℕ → ℕ) (E : ∀ n, Fin (m n) → Set (Euc d))
  (hE : ∀ n i, MeasurableSet (E n i))
  (hdE : ∀ n, Pairwise (fun i j => Disjoint (E n i) (E n j)))
omit [MeasurableEq V] in
lemma walkBrownianCouplingKernel_apply (n : ℕ) (h) :
    walkBrownianCouplingKernel κ pos hpos B hB U hU μ select hs m E hE hdE n h =
      finitePartitionCoupling
        (walkSkeletonHistoryKernel κ pos hpos B hB select hs n
          (TrajectoryCoupling.prefixMap Prod.fst n h))
        (brownianSkeletonKernel U hU μ (brownianSelectorForWalk select)
          (fun n => hs (n - 1)) n (TrajectoryCoupling.prefixMap Prod.snd n h))
        (fun i => walkEndpointCell pos (E (n + 1) i))
        (fun i => activeEndpointCell (fun c : C(unitInterval, Euc d) => c 1) (E (n + 1) i)) :=
  finitePartitionCouplingKernel_apply _ _ _ _ _ _ h

/-- A next active step has the prescribed failure probability under the
actual coupled transition, using the genuine spatial exit probabilities. -/
theorem walkBrownianCouplingKernel_active_bad_le (hd : 1 ≤ d) (hμ : IsStandardBrownianLaw μ)
    (hUb : ∀ j, Bornology.IsBounded (U j)) (n : ℕ)
    (h : Finset.Iic n → (Bool × ClockedWalkExcursion d) × (Bool × C(unitInterval, Euc d)))
    (hflagw : (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).1.1 = false)
    (hflagb : (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2.1 = false)
    (v : V) (hv : ClockedWalkExcursion.endPoint (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).1.2 = pos v)
    (j : J) (hjw : select n (pos v) = some j)
    (hjb : select n ((h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2.2 1) = some j)
    (hz : (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2.2 1 ∈ U j)
    (hcover : closure (U j) ⊆ ⋃ i, E (n + 1) i)
    {b : ℝ} (hb : 0 ≤ b)
    (herror : ∀ i, |(((discreteHarmonicMeasure κ (B j) (hB j) v).map pos) (E (n + 1) i)).toReal -
      (((stoppedBrownianLaw (U j) ((h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2.2 1) μ).map
        CurveSpace.endPoint) (E (n + 1) i)).toReal| ≤ b / (m (n + 1) + 1)) (a : ℝ) :
    walkBrownianCouplingKernel κ pos hpos B hB U hU μ select hs m E hE hdE n h
      (goodExcursionPair pos (E (n + 1)) a)ᶜ ≤ ENNReal.ofReal b := by
  rw [walkBrownianCouplingKernel_apply κ pos hpos B hB select hs U hU μ m E hE hdE,
    walkSkeletonHistoryKernel_active_row κ pos hpos B hB select hs n _ hflagw v hv j hjw,
    brownianSkeletonKernel_active_row select hs U hU μ n _ hflagb j hjb]
  exact finite_walkBrownian_excursion_bad_le κ hd pos hpos (B j) (hB j) v (hU j) (hUb j)
    μ hμ hz (E (n + 1)) (hE (n + 1)) (hdE (n + 1)) hcover hb herror _
    (goodExcursionPair_compl_disjoint_cell pos (E (n + 1)) a)

omit [MeasurableEq V] in
/-- Two terminated rows preserve the distance bound with zero failure mass.
This also applies when the current active pair both select termination now. -/
theorem walkBrownianCouplingKernel_constant_bad_zero (n : ℕ)
    (h : Finset.Iic n → (Bool × ClockedWalkExcursion d) × (Bool × C(unitInterval, Euc d)))
    (hstopw : (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).1.1 = true ∨
      select n (ClockedWalkExcursion.endPoint (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).1.2) = none)
    (hstopb : (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2.1 = true ∨
      select n ((h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2.2 1) = none)
    (hx : ClockedWalkExcursion.endPoint (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).1.2 ∈ Set.range pos)
    {a : ℝ} (hxy : dist (ClockedWalkExcursion.endPoint (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).1.2)
      ((h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2.2 1) ≤ a) :
    walkBrownianCouplingKernel κ pos hpos B hB U hU μ select hs m E hE hdE n h
      (goodExcursionPair pos (E (n + 1)) a)ᶜ = 0 := by
  have hm := walkBrownianCouplingKernel_marginals κ pos hpos B hB U hU μ select hs m E hE hdE n h
  apply coupling_bad_goodExcursionPair_constants_zero pos (E (n + 1)) hx hxy
  · exact hm.1.trans (walkSkeletonHistoryKernel_constant_row κ pos hpos B hB select hs n _ hstopw)
  · exact hm.2.trans (brownianSkeletonKernel_constant_row select hs U hU μ n _ hstopb)

include hpos hE hdE in
/-- The initial coupling uses the fixed ball selected from the prescribed
start, so no matching of a previous cell label is required. -/
theorem walkBrownianInitialCoupling_bad_le (hd : 1 ≤ d) (hμ : IsStandardBrownianLaw μ)
    (hUb : ∀ j, Bornology.IsBounded (U j)) (initial : J) (v : V) (z : Euc d)
    (hz : z ∈ U initial) (hcover : closure (U initial) ⊆ ⋃ i, E 0 i)
    {b : ℝ} (hb : 0 ≤ b)
    (herror : ∀ i, |(((discreteHarmonicMeasure κ (B initial) (hB initial) v).map pos) (E 0 i)).toReal -
      (((stoppedBrownianLaw (U initial) z μ).map CurveSpace.endPoint) (E 0 i)).toReal| ≤
        b / (m 0 + 1)) (a : ℝ) :
    walkBrownianInitialCoupling κ pos B hB U hU μ m E initial v z
      (goodExcursionPair pos (E 0) a)ᶜ ≤ ENNReal.ofReal b := by
  change finitePartitionCoupling
    ((clockedWalkExcursionKernel κ pos (hB initial) v).map (fun e => (false, e)))
    ((brownianExcursionKernel (hU initial) μ z).map (fun e => (false, e)))
    (fun i => walkEndpointCell pos (E 0 i))
    (fun i => activeEndpointCell (fun c : C(unitInterval, Euc d) => c 1) (E 0 i)) _ ≤ _
  exact finite_walkBrownian_excursion_bad_le κ hd pos hpos (B initial) (hB initial) v
    (hU initial) (hUb initial) μ hμ hz (E 0) (hE 0) (hdE 0) hcover hb herror _
    (goodExcursionPair_compl_disjoint_cell pos (E 0) a)

end SpherePackings.MarkovChain
