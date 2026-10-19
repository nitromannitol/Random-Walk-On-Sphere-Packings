-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/WalkStoppedReconstruction.lean` at commit cf73d6e); unchanged apart from this header and
-- from `omit [Fintype V] in` before declarations that do not use finiteness.
import BouRabeeGwynne.ClockedWalkStopping
import BouRabeeGwynne.WalkSkeletonLaw

/-! Recover the actual stopped walk from a finite sequence of its rich
excursions once that sequence reaches the domain's first vertex exit. -/

open MeasureTheory Set

namespace BouRabeeGwynne

noncomputable def reconstructedVertexStoppedCurve {d : ℕ} (U : Set (Euc d))
    (n : ℕ) (e : ℕ → Bool × ClockedWalkExcursion d) : CurveSpace d :=
  ClockedWalkExcursion.vertexStoppedCurve U
    (ClockedWalkExcursion.concatenate (fun i => (e i).2) n)

lemma measurable_reconstructedVertexStoppedCurve {d : ℕ} {U : Set (Euc d)}
    (hU : MeasurableSet U) (n : ℕ) :
    Measurable (reconstructedVertexStoppedCurve U n) :=
  (ClockedWalkExcursion.measurable_vertexStoppedCurve hU).comp
    ((ClockedWalkExcursion.measurable_concatenate n).comp
      (Measurable.of_eval fun i => (measurable_pi_apply i).snd))

namespace FiniteConductanceNetwork

variable {d : ℕ} {V J : Type*} [Fintype V] [MeasurableSpace V]
  [MeasurableSingletonClass V] [Countable J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

omit [Fintype V] in -- finiteness is not used
theorem concatenate_actualWalkStage (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → V → Option J) (ω : ℕ → V) (n : ℕ)
    (hfinite : (actualWalkStage pos B initial select n ω).1 ≠ ⊤) :
    ClockedWalkExcursion.concatenate
        (fun i => (actualWalkStage pos B initial select i ω).2.2) n =
      clockedWalkSegment pos ω 0
        ((actualWalkStage pos B initial select n ω).1.untopD 0) := by
  induction n with
  | zero =>
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hfinite
    rw [ClockedWalkExcursion.concatenate, ← hm, WithTop.untopD_coe]
    exact actualWalkStage_zero_segment pos B initial select ω m hm.symm
  | succ n ih =>
    have hle := actualWalkStage_clock_mono pos B initial select ω (Nat.le_succ n)
    have hprevious : (actualWalkStage pos B initial select n ω).1 ≠ ⊤ :=
      ne_top_of_le_ne_top hfinite hle
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hprevious
    obtain ⟨l, hl⟩ := WithTop.ne_top_iff_exists.mp hfinite
    have hkl : k ≤ l := WithTop.coe_le_coe.mp (hk.trans_le (hle.trans_eq hl.symm))
    rw [ClockedWalkExcursion.concatenate, ih hprevious,
      actualWalkStage_succ_segment pos B initial select n ω k l hk.symm hl.symm,
      ← hk, ← hl, WithTop.untopD_coe, WithTop.untopD_coe]
    exact ClockedWalkExcursion.append_clockedWalkSegment pos ω (Nat.zero_le k) hkl

omit [Fintype V] in -- finiteness is not used
theorem reconstructedVertexStoppedCurve_actual (pos : V → Euc d)
    (B : J → Set V) (initial : J) (select : ℕ → Euc d → Option J)
    (U : Set (Euc d)) (ω : ℕ → V) (n : ℕ)
    (hfinite : (actualWalkStage pos B initial (fun i v => select i (pos v)) n ω).1 ≠ ⊤)
    (hexit : exitTime (pos ⁻¹' U) ω ≤
      (actualWalkStage pos B initial (fun i v => select i (pos v)) n ω).1) :
    reconstructedVertexStoppedCurve U n (actualWalkExcursionSequence pos B initial select ω) =
      stoppedPolygonalCurve pos (pos ⁻¹' U) ω := by
  unfold reconstructedVertexStoppedCurve actualWalkExcursionSequence
  rw [concatenate_actualWalkStage pos B initial (fun i v => select i (pos v)) ω n hfinite]
  apply ClockedWalkExcursion.vertexStoppedCurve_clockedWalkSegment pos U ω
    (M := (actualWalkStage pos B initial (fun i v => select i (pos v)) n ω).1.untopD 0)
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hfinite
  have hclock :
      (((actualWalkStage pos B initial (fun i v => select i (pos v)) n ω).1.untopD 0 : ℕ) :
        WithTop ℕ) = (actualWalkStage pos B initial (fun i v => select i (pos v)) n ω).1 := by
    rw [← hm]
    rfl
  exact hexit.trans_eq hclock.symm

end FiniteConductanceNetwork
end BouRabeeGwynne
