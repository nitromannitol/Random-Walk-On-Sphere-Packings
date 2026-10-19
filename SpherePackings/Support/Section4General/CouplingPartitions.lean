-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne (file
-- `BouRabeeGwynne/CouplingPartitions.lean` at commit cf73d6e): its main theorem for an arbitrary
-- nearest-neighbour walk under Assumption D as printed.
import BouRabeeGwynne.CouplingPartitions
import SpherePackings.Support.Section4General.ExitPartitions
import SpherePackings.Support.Section4General.StoppedWalkLaw
import SpherePackings.General.NearestNeighbourWalkHarmonic
import SpherePackings.General.Walk.WalkBrownianFailure

/-! Section 4 of rw-spheres.tex: couplings of the walk and Brownian excursions from finitely many
balls, with partitions of the exit points whose cells are small, for a nearest-neighbour walk
under Assumption D.  The first failure of a good pairing has probability at most `(K + 1) b`. -/

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology Classical ENNReal

namespace SpherePackings

open BouRabeeGwynne

local instance {X : Type*} : MeasurableSpace (Option X) := ⊤

variable {d : ℕ}

/-- **Coupling partitions.**  The walk's excursions are from the vertex sets
`{v | v ∈ B_r(c)}` of the balls; a single eventual index serves every nearby pair of starts. -/
theorem exists_eventual_walkBrownian_coupling_partitions_general (hd : 1 ≤ d)
    (W : ℕ → NearestNeighbourWalk d) (near : ∀ n, Euc d → (W n).V)
    (hnear : ∀ n, (W n).IsNearestVertex (near n))
    {D : Set (Euc d)} {δD : ℝ} (hAD : AssumptionD W near D δD)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (centers : Finset (Euc d)) {r : ℝ} (hr : 0 < r)
    {C Q : Set (Euc d)} (hQ : IsCompact Q) (hCQ : C ⊆ Q)
    (hballD : ∀ j : centers, closedBall j.val r ⊆ cthickening δD D)
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
      ∀ᶠ n in atTop,
        letI : IsProbabilityMeasure μ := hμ.1
        ∀ (initial : centers) (v₀ : (W n).V) (z : Euc d),
          (v₀ : Euc d) ∈ closedBall initial.val (r / 2) → z ∈ closedBall initial.val (r / 2) →
          dist (v₀ : Euc d) z ≤ δ₀ →
          MarkovChain.walkBrownianJointLaw (W n).kernel Subtype.val
            ((W n).measurableEmbedding_val_of_isNearestVertex (hnear n))
            (fun j : centers => {w : (W n).V | (w : Euc d) ∈ ball j.val r})
            (fun _ => measurable_subtype_coe measurableSet_ball)
            (fun j : centers => ball j.val r) (fun _ => isOpen_ball) μ select hs m E hE hdE
            initial v₀ z
            {p | ∃ i ≤ K, (p.1 i, p.2 i) ∉ goodExcursionPair (Subtype.val : (W n).V → Euc d) (E i) a} ≤
              (K + 1 : ℝ≥0∞) * ENNReal.ofReal b := by
  obtain ⟨mf, Ef, δ, hδ, hdEf, hcoverf, hEf, -, hdiamf, hbackf, -, hevent⟩ :=
    exists_backward_ball_exit_partitions hd W near hAD (fun j : centers => j.val) hr hballD hμ
      hQ ha hb K
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
  -- the walk leaves every ball almost surely
  have hexits : ∀ᶠ n in atTop, ∀ j : centers, ∀ v : (W n).V,
      ∀ᵐ ω ∂MarkovChain.law (W n).kernel v,
        FiniteConductanceNetwork.exitTime ((W n).inner (ball j.val r)) ω ≠ ⊤ :=
    eventually_all.mpr fun j => eventually_ae_exit W near hAD isBounded_ball
      (ball_subset_closedBall.trans (hballD j))
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
  · filter_upwards [hevent, hexits] with n herr hex
    have : IsProbabilityMeasure μ := hμ.1
    -- the walk's exit law from a ball is its harmonic measure
    have hhm : ∀ (j : centers) (v : (W n).V),
        (MarkovChain.discreteHarmonicMeasure (W n).kernel
          {w : (W n).V | (w : Euc d) ∈ ball j.val r}
          (measurable_subtype_coe measurableSet_ball) v).map Subtype.val =
          (W n).harmonicMeasure (ball j.val r) v := fun j v =>
      (W n).discreteHarmonicMeasure_map_val_of_eq (ball j.val r) _
        ((W n).inner_of_isOpen isOpen_ball).symm v (hex j v)
    intro initial v₀ z hv₀ hz hnear'
    refine MarkovChain.walkBrownianJointLaw_firstFailure_le (W n).kernel hd Subtype.val
      ((W n).measurableEmbedding_val_of_isNearestVertex (hnear n))
      (fun j : centers => {w : (W n).V | (w : Euc d) ∈ ball j.val r})
      (fun _ => measurable_subtype_coe measurableSet_ball)
      (fun j : centers => ball j.val r) (fun _ => isOpen_ball) (fun _ => isBounded_ball)
      μ hμ select hs m E hE hdE choice (fun _ => rfl) K hb.le
      (fun i _ k x hx y hy => (hdiam i k x hx y hy).trans (min_le_left _ _))
      (fun i _ k j hkj => (hinner i k j hkj).trans (ball_subset_ball (half_le_self hr.le)))
      (fun i _ j => (hballQ j).trans (hcoverf (ix i)))
      ?_ initial v₀ z (closedBall_subset_ball (half_lt_self hr) hz) ?_
    · intro i hi k j hkj v hv y hy l
      rw [hhm j v]
      exact herr j (ix (i + 1)) v (mem_closedBall.mpr (mem_ball.mp (hinner i k j hkj hv)).le)
        y (mem_closedBall.mpr (mem_ball.mp (hinner i k j hkj hy)).le)
        (hback i hi k _ hv y hy) l
    · intro l
      rw [hhm initial v₀]
      exact herr initial (ix 0) v₀ hv₀ z hz hnear' l

end SpherePackings
