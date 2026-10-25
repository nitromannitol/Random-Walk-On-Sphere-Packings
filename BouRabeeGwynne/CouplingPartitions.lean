module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/CouplingPartitions.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.AmbientExitPartitions
public import BouRabeeGwynne.WalkBrownianFailure

@[expose] public section

/-! Instantiate the actual whole-sequence coupling with the backward chosen
continuity partitions. The stage count and finite ball margins are fixed first. -/

set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology Classical ENNReal

namespace BouRabeeGwynne

local instance {X : Type*} : MeasurableSpace (Option X) := ⊤

/-- Actual finite-ball couplings with a single eventual index uniform over
both nearby starts. Selectors are total, keep the fixed inner ball margin,
and cannot terminate at a point of the active compact region. -/
theorem exists_eventual_walkBrownian_coupling_partitions {d : ℕ} (hd : 1 ≤ d)
    (G : TilingSequence d) (N : NearestVertexData G)
    (happrox : N.ApproximationCondition) (hreg : PaperRegularity G)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (centers : Finset (Euc d)) {r : ℝ} (hr : 0 < r)
    {W C Q : Set (Euc d)} (hW : Bornology.IsBounded W) (hWD : HasAmbientCollar W G.domain)
    (hQ : IsCompact Q) (hCQ : C ⊆ Q)
    (hballW : ∀ j : centers, ball j.val r ⊆ W)
    (hballQ : ∀ j : centers, closure (ball j.val r) ⊆ Q)
    (hquarter : ∀ x ∈ C, ∃ c ∈ centers, x ∈ ball c (r / 4))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (K : ℕ) :
    ∃ (m : ℕ → ℕ) (E : ∀ i, Fin (m i) → Set (Euc d))
      (hE : ∀ i k, MeasurableSet (E i k))
      (hdE : ∀ i, Pairwise (fun k l => Disjoint (E i k) (E i l)))
      (select : ℕ → Euc d → Option ↥centers)
      (hs : ∀ i, Measurable (select i)) (δ₀ : ℝ), 0 < δ₀ ∧
      (∀ i x j, select i x = some j → ball x (r / 2) ⊆ ball j.val r) ∧
      (∀ i, ∀ x ∈ C, select i x ≠ none) ∧
      (∀ i k, ∀ x ∈ E i k, ∀ y ∈ E i k, dist x y ≤ a) ∧
      ∀ᶠ n in atTop, ∃ hfin : ((G.tiling n).closedVertices W).Finite,
        letI : Fintype ((G.tiling n).closedVertices W) := hfin.fintype
        letI : MeasurableSpace ((G.tiling n).closedVertices W) := ⊤
        let T := G.tiling n
        let NW := T.finiteNetwork (T.closedVertices W)
        let pos := fun v : T.closedVertices W => T.pos v
        let B := fun j : centers => {v : T.closedVertices W | T.pos v ∈ ball j.val r}
        ∃ haccess : NW.BoundaryAccessible (T.finiteInterior W),
        ∃ hA : ∀ v ∈ T.finiteInterior W, 0 < NW.totalConductance v,
        ∃ hB : ∀ j v, v ∈ B j → 0 < NW.totalConductance v,
          letI : IsProbabilityMeasure μ := hμ.1
          ∀ (initial : centers) (v₀ : T.closedVertices W) (z : Euc d),
            pos v₀ ∈ closedBall initial.val (r / 2) → z ∈ closedBall initial.val (r / 2) →
            dist (pos v₀) z ≤ δ₀ →
            NW.walkBrownianJointLaw pos (T.pos_injective.comp Subtype.val_injective)
              B hB (fun j : centers => ball j.val r) (fun _ => isOpen_ball) μ
              select hs m E hE hdE initial v₀ z
              {p | ∃ i ≤ K, (p.1 i, p.2 i) ∉ goodExcursionPair pos (E i) a} ≤
                (K + 1 : ℝ≥0∞) * ENNReal.ofReal b := by
  obtain ⟨mf, Ef, δ, hδ, hdEf, hcoverf, hEf, hbounded, hdiamf, hbackf, hnull, hevent⟩ :=
    exists_backward_ambient_exit_partitions hd G N (fun j : centers => j.val) hr W hW hWD
      hballW happrox hreg hμ hQ ha hb K
  let ix : ℕ → Fin (K + 1) := fun n => ⟨min n K, Nat.lt_succ_of_le (min_le_right _ _)⟩
  let m : ℕ → ℕ := fun n => mf (ix n)
  let E : ∀ n, Fin (m n) → Set (Euc d) := fun n => Ef (ix n)
  have hE : ∀ n i, MeasurableSet (E n i) := fun n => hEf (ix n)
  have hdE : ∀ n, Pairwise (fun i j => Disjoint (E n i) (E n j)) := fun n => hdEf (ix n)
  have hdiam : ∀ n i, ∀ x ∈ E n i, ∀ y ∈ E n i, dist x y ≤ min a (r / 4) :=
    fun n => hdiamf (ix n)
  have hback : ∀ n < K, ∀ i, ∀ x ∈ E n i, ∀ y ∈ E n i,
      dist x y ≤ δ (ix (n + 1)) := by
    intro n hn
    have hix : ix n = (⟨n, hn⟩ : Fin K).castSucc :=
      Fin.ext (Nat.min_eq_left hn.le)
    have hix' : ix (n + 1) = (⟨n, hn⟩ : Fin K).succ :=
      Fin.ext (Nat.min_eq_left (Nat.succ_le_of_lt hn))
    change ∀ k : Fin (mf (ix n)), ∀ x ∈ Ef (ix n) k, ∀ y ∈ Ef (ix n) k,
      dist x y ≤ δ (ix (n + 1))
    rw [hix, hix']
    exact hbackf (⟨n, hn⟩ : Fin K)
  have hex (n : ℕ) : ∃ choice : Fin (m n) → Option ↥centers,
      (∀ i, choice i = none ↔ E n i ∩ C = ∅) ∧
      ∀ i j, choice i = some j → E n i ⊆ ball j.val (r / 2) :=
    exists_cell_ball_choices (E n) hquarter
      (fun i x hx y hy => (hdiam n i x hx y hy).trans (min_le_right _ _))
  choose choice hnone hinner using hex
  let select := fun n => cellSelector (E n) (choice n)
  have hs : ∀ n, Measurable (select n) :=
    fun n => measurable_cellSelector (E n) (choice n) (hdE n) (hE n)
  refine ⟨m, E, hE, hdE, select, hs, δ (ix 0), hδ _, ?_, ?_, ?_, ?_⟩
  · intro n x j hj
    obtain ⟨i, hxi, hij⟩ := cellSelector_some_mem (E n) (choice n) hj
    have hx := hinner n i j hij hxi
    intro y hy
    change dist y j.val < r
    calc
      dist y j.val ≤ dist y x + dist x j.val := dist_triangle _ _ _
      _ < r / 2 + r / 2 := add_lt_add hy hx
      _ = r := by ring
  · intro n x hxC hn
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hcoverf (ix n) (hCQ hxC))
    have hlabel := (cellLabel_eq_some_iff (E n) (hdE n) x i).mpr hxi
    have hn' : choice n i = none := (cellSelector_of_label (E n) (choice n) hlabel).symm.trans hn
    exact (Set.notMem_empty x) ((hnone n i).mp hn' ▸ (show x ∈ E n i ∩ C from ⟨hxi, hxC⟩))
  · exact fun n i x hx y hy => (hdiam n i x hx y hy).trans (min_le_left _ _)
  · filter_upwards [hevent] with n hn
    obtain ⟨hfin, hn⟩ := hn
    refine ⟨hfin, ?_⟩
    letI : Fintype ((G.tiling n).closedVertices W) := hfin.fintype
    letI : MeasurableSpace ((G.tiling n).closedVertices W) := ⊤
    obtain ⟨haccess, hA, hB, herr⟩ := hn
    refine ⟨haccess, hA, hB, ?_⟩
    letI : IsProbabilityMeasure μ := hμ.1
    intro initial v₀ z hv₀ hz hnear
    refine FiniteConductanceNetwork.walkBrownianJointLaw_firstFailure_le
      ((G.tiling n).finiteNetwork ((G.tiling n).closedVertices W)) hd
      (fun v : (G.tiling n).closedVertices W => (G.tiling n).pos v)
      ((G.tiling n).pos_injective.comp Subtype.val_injective)
      (fun j : centers => {v : (G.tiling n).closedVertices W | (G.tiling n).pos v ∈ ball j.val r})
      hB (fun j : centers => ball j.val r) (fun _ => isOpen_ball) (fun _ => isBounded_ball)
      μ hμ select hs m E hE hdE choice (fun _ => rfl) K hb.le
      (fun i _ k x hx y hy => (hdiam i k x hx y hy).trans (min_le_left _ _))
      (fun i _ k j hkj => (hinner i k j hkj).trans (ball_subset_ball (half_le_self hr.le)))
      (fun i _ j => (hballQ j).trans (hcoverf (ix i)))
      ?_ initial v₀ z (closedBall_subset_ball (half_lt_self hr) hz)
      (herr (ix 0) initial v₀ hv₀ z hz hnear)
    intro i hi k j hkj v hv y hy l
    exact herr (ix (i + 1)) j v (mem_closedBall.mpr (mem_ball.mp (hinner i k j hkj hv)).le)
      y (mem_closedBall.mpr (mem_ball.mp (hinner i k j hkj hy)).le)
      (hback i hi k _ hv y hy) l

end BouRabeeGwynne
