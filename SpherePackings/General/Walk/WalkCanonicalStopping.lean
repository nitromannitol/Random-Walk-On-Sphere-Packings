module

-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/WalkCanonicalStopping.lean` at commit cf73d6e): its declarations that assume a
-- finite state space or a finite conductance network, for the chain of an arbitrary Markov
-- kernel on a measurable space.
public import BouRabeeGwynne.WalkCanonicalStopping
public import SpherePackings.General.MarkovChain.Absorbed
public import SpherePackings.General.Walk.ActualWalkSkeleton
public import SpherePackings.General.Walk.WalkReconstructionLaw
public import SpherePackings.General.Walk.WalkSkeletonLaw
public import SpherePackings.General.Walk.WalkSkeletonPrefix

@[expose] public section

/-! General-state-space version of `BouRabeeGwynne.WalkCanonicalStopping`: the declarations of that file
that assume a finite state space or a finite conductance network. -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval
namespace SpherePackings.MarkovChain

open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork BouRabeeGwynne.TrajectoryCoupling
variable {d : ℕ} {V J : Type*} [MeasurableSpace V] [MeasurableEq V] [Countable J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

omit [MeasurableSpace V] [MeasurableEq V] [Countable J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)] in
private lemma polygonalCurve_prefix_of_scaled_vertex (pos : V → Euc d) (ω : ℕ → V)
    {M m : ℕ} (hmM : m ≤ M) (b : unitInterval) (hb : (M : ℝ) * (b : ℝ) = m) :
    prefixUnitCurve (polygonalCurve pos ω M) b = polygonalCurve pos ω m := by
  apply ContinuousMap.ext
  intro u
  change polygonalCurve pos ω M (b * u) = polygonalCurve pos ω m u
  simpa only [Nat.zero_add] using polygonalCurve_shift_of_scaled_time pos ω
    (a := 0) (m := m) (M := M) (by simpa only [Nat.zero_add] using hmM) u (b * u)
    (by
      rw [Set.Icc.coe_mul, Nat.cast_zero, zero_add, ← mul_assoc, hb])

lemma pastedWalkCurve_actual_eq_comp_canonical (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → Euc d → Option J) (n : ℕ) (ω : ℕ → V)
    (hfinite : (actualWalkStage pos B initial (fun i v => select i (pos v)) n ω).1 ≠ ⊤)
    (P : TimePartition n) :
    pastedWalkCurve P (actualWalkExcursionSequence pos B initial select ω) =
      (polygonalCurve pos ω
        ((actualWalkStage pos B initial (fun i v => select i (pos v)) n ω).1.untopD 0)).comp
      (P.weakClock ((ClockedWalkExcursion.prefixTimeData
        (actualWalkExcursionSequence pos B initial select ω)).knots P)) := by
  let s := fun i v => select i (pos v)
  let D := ClockedWalkExcursion.prefixTimeData (n := n)
    (actualWalkExcursionSequence pos B initial select ω)
  have hD : D.val = actualWalkStage_times pos B initial s n ω :=
    prefixTimeData_actualWalkStage pos B initial s n ω hfinite
  have hM : D.duration = (actualWalkStage pos B initial s n ω).1.untopD 0 :=
    congrFun hD (Fin.last (n + 1))
  have hQ (i : Fin (n + 2)) :
      (((actualWalkStage pos B initial s n ω).1.untopD 0 : ℕ) : ℝ) *
        ((D.knots P).knots i : ℝ) = (actualWalkStage_times pos B initial s n ω i : ℝ) := by
    rw [← hM, ← hD]
    exact D.knots_scaled P i
  have hchain := clockedWalkSegments_eq_restrictChain (D.knots P) pos ω
    (actualWalkStage_times pos B initial s n ω)
    (actualWalkStage_times_monotone pos B initial s n ω hfinite) rfl hQ
    (ExcursionTrajectory.prefixChain n d
      (fun k => ClockedWalkExcursion.curve (actualWalkStage pos B initial s k ω).2.2))
    (by
      intro i
      rw [ExcursionTrajectory.prefixChain_apply
        (actualWalkStage_compatiblePaths pos B initial s n ω hfinite)]
      exact congrArg ClockedWalkExcursion.curve
        (actualWalkStage_eq_segment_times pos B initial s n ω hfinite i))
  change P.concatenate (ExcursionTrajectory.prefixChain n d
      (fun k => ClockedWalkExcursion.curve (actualWalkStage pos B initial s k ω).2.2)) =
    (polygonalCurve pos ω ((actualWalkStage pos B initial s n ω).1.untopD 0)).comp
      (P.weakClock (D.knots P))
  rw [hchain, WeakTimeKnots.concatenate_restrictChain]
  rfl

theorem canonicalWalkStoppingSupport_actual (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → Euc d → Option J) (U : Set (Euc d))
    (n : ℕ) (ω : ℕ → V) (δ : ℝ)
    (hfinite : (actualWalkStage pos B initial (fun i v => select i (pos v)) n ω).1 ≠ ⊤)
    (hexit : exitTime (pos ⁻¹' U) ω ≤
      (actualWalkStage pos B initial (fun i v => select i (pos v)) n ω).1)
    (hedge : ∀ k < (exitTime (pos ⁻¹' U) ω).untopD 0,
      dist (pos (ω (k + 1))) (pos (ω k)) ≤ δ) (P : TimePartition n) :
    actualWalkExcursionSequence pos B initial select ω ∈ canonicalWalkStoppingSupport U δ P := by
  let s := fun i v => select i (pos v)
  let e := actualWalkExcursionSequence pos B initial select ω
  let D := ClockedWalkExcursion.prefixTimeData (n := n) e
  let M := (actualWalkStage pos B initial s n ω).1.untopD 0
  have hclock : (actualWalkStage pos B initial s n ω).1 = (M : WithTop ℕ) := by
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hfinite
    dsimp only [M]
    rw [← hk]
    rfl
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top hfinite hexit)
  have hmM : m ≤ M := WithTop.coe_le_coe.mp (hm.trans_le (hexit.trans_eq hclock))
  have hconcat : ClockedWalkExcursion.concatenate (fun k => (e k).2) n =
      clockedWalkSegment pos ω 0 M :=
    concatenate_actualWalkStage pos B initial s ω n hfinite
  have hduration : D.duration = M := by
    change (ClockedWalkExcursion.concatenate (fun k => (e k).2) n).1 = M
    rw [hconcat]
    exact Nat.sub_zero M
  have he : exitTime U (ClockedWalkExcursion.concatenate (fun k => (e k).2) n).2 =
      exitTime (pos ⁻¹' U) ω := by
    rw [hconcat, ← exitTime_map pos U ω]
    apply exitTime_congr_prefix_of_le U (M := M)
    · intro k hk
      change pos (ω (0 + min k (M - 0))) = pos (ω k)
      simp only [Nat.sub_zero, Nat.zero_add, min_eq_left hk]
    · rw [exitTime_map]
      exact hexit.trans_eq hclock
  have hindex : ClockedWalkExcursion.concatenatedExitIndex (n := n) U e = m := by
    change min ((exitTime U (ClockedWalkExcursion.concatenate (fun k => (e k).2) n).2).untopD 0)
      D.duration = m
    rw [he, ← hm, WithTop.untopD_coe, hduration, min_eq_left hmM]
  let a := ClockedWalkExcursion.pastedVertexExitParameter U P e
  let b := D.vertexTime m
  let f := pastedWalkCurve P e
  have hab : P.weakClock (D.knots P) a = b := by
    simpa only [hindex] using ClockedWalkExcursion.pastedVertexExitParameter_clock U P e
  have hb : (M : ℝ) * (b : ℝ) = m := by
    simpa only [hduration, min_eq_left hmM] using D.vertexTime_scaled m
  have hcomp : f = (polygonalCurve pos ω M).comp (P.weakClock (D.knots P)) :=
    pastedWalkCurve_actual_eq_comp_canonical pos B initial select n ω hfinite P
  have hinside : ∀ k < m, pos (ω k) ∈ U := by
    intro k hk
    change ω k ∈ pos ⁻¹' U
    apply mem_of_lt_exitTime
    rw [← hm]
    exact WithTop.coe_lt_coe.mpr hk
  have hout : pos (ω m) ∉ U := by
    have h := exitTime_mem_compl_of_ne_top (ne_top_of_le_ne_top hfinite hexit)
    rw [← hm] at h
    exact h
  have hstep : ∀ k < m, dist (pos (ω (k + 1))) (pos (ω k)) ≤ δ := by
    simpa only [← hm, WithTop.untopD_coe] using hedge
  have hfa : f a = pos (ω m) := by
    rw [hcomp, ContinuousMap.comp_apply, hab]
    exact polygonalCurve_at_scaled_vertex pos ω hmM b hb
  refine ⟨?_, hfa ▸ hout, ?_⟩
  · change CurveSpace.project (prefixUnitCurve f a) = reconstructedVertexStoppedCurve U n e
    rw [hcomp, curveSpace_project_prefix_comp_monotone _ _
      (P.weakClock_monotone _) (P.weakClock_zero _) a b hab,
      polygonalCurve_prefix_of_scaled_vertex pos ω hmM b hb,
      reconstructedVertexStoppedCurve_actual pos B initial select U ω n hfinite hexit]
    simp only [stoppedPolygonalCurve, ← hm, WithTop.untopD_coe]
  · by_cases hmzero : m = 0
    · left
      change D.exitParameter P (ClockedWalkExcursion.concatenatedExitIndex (n := n) U e) = 0
      rw [hindex, hmzero, WalkPrefixTimeData.exitParameter_zero]
    · right
      intro u
      change f (a * u) ∈ Metric.cthickening δ U
      rw [hcomp, ContinuousMap.comp_apply]
      apply polygonalCurve_mem_cthickening_before_vertex pos ω (Nat.pos_of_ne_zero hmzero)
        hmM hinside hstep
      calc
        (M : ℝ) * (P.weakClock (D.knots P) (a * u) : ℝ) ≤
            (M : ℝ) * (P.weakClock (D.knots P) a : ℝ) :=
          mul_le_mul_of_nonneg_left ((P.weakClock_monotone _) (show a * u ≤ a from
            mul_le_of_le_one_right a.property.1 u.property.2)) (Nat.cast_nonneg M)
        _ = m := by rw [hab]; exact hb

/-- Almost surely under the rich walk marginal, the excursion sequence either is still active at
stage `n` (flag `false`) or lies in the support needed by the joint comparison; an active prefix is
left for the separate tail bound. -/
theorem trajectoryLaw_map_ae_canonicalWalkStoppingSupport (κ : Kernel V V) [IsMarkovKernel κ]
    (pos : V → Euc d) (hpos : Measurable pos) {A : Set V} (B : J → Set V)
    (hB : ∀ j, MeasurableSet (B j)) (hBA : ∀ j, B j ⊆ A)
    (hA : MeasurableSet A)
    (hexit : ∀ v, ∀ᵐ ω ∂law (absorbedKernel κ hA) v, exitTime A ω ≠ ⊤)
    (initial : J) (select : ℕ → Euc d → Option J) (hs : ∀ i, Measurable (select i))
    (U : Set (Euc d))
    (hU : MeasurableSet U) (hselect : ∀ i x, select i x = none → x ∉ U)
    (v : V) (n : ℕ) (δ : ℝ)
    (hsteps : ∀ᵐ ω ∂law (absorbedKernel κ hA) v, ∀ k,
      dist (pos (ω k)) (pos (ω (k + 1))) ≤ δ) (P : TimePartition n) :
    ∀ᵐ e ∂(law (absorbedKernel κ hA) v).map (actualWalkExcursionSequence pos B initial select),
      (e n).1 = false ∨ e ∈ canonicalWalkStoppingSupport U δ P := by
  have hflag : MeasurableSet {e : ℕ → Bool × ClockedWalkExcursion d | (e n).1 = false} :=
    measurableSet_eq_fun (measurable_pi_apply n).fst measurable_const
  apply (ae_map_iff
    (measurable_actualWalkExcursionSequence pos B initial select hpos hB hs).aemeasurable
    (hflag.union (measurableSet_canonicalWalkStoppingSupport hU δ P))).mpr
  filter_upwards [hsteps, actualWalkStage_ae_all_clocks_finite κ pos B hBA hA hexit initial
    (fun i v => select i (pos v)) v] with ω hω hfinite
  by_cases hactive : (actualWalkExcursionSequence pos B initial select ω n).1 = false
  · exact Or.inl hactive
  right
  have hstopped : (actualWalkStage pos B initial (fun i v => select i (pos v)) n ω).2.1 = true :=
    Bool.eq_true_of_not_eq_false hactive
  apply canonicalWalkStoppingSupport_actual pos B initial select U n ω δ (hfinite n)
    (actualWalkStage_exit_le_of_stopped pos B initial (fun i v => select i (pos v))
      (pos ⁻¹' U) hpos hB (fun i => (hs i).comp hpos) (fun i v hv => hselect i (pos v) hv) ω n
      (hfinite n) hstopped) ?_ P
  intro k _
  simpa only [dist_comm] using hω k

end SpherePackings.MarkovChain
