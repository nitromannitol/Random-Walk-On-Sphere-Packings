-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/HypIIIErrorBound.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.HypIIICorrectedRegions
import BouRabeeGwynne.HypIIIRegionScale
import BouRabeeGwynne.HypIIITaylorCost
import BouRabeeGwynne.HypIIICostBound

/-! The actual finite Dirichlet error is bounded by the corrected cost series. -/

open scoped Classical BigOperators ENNReal
open Filter

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

/-- The mass decay premise is supplied by `correctedRegions_mass_le_geometric`.
All regions, corrections, and diameters in this conclusion are the concrete
ones, and hypothesis III supplies termination and the summable scale bound. -/
theorem dirichlet_error_le_hypIIICost_of_mass_decay (hd : 1 ≤ d)
    (R : Set T.V) [Fintype R] (A : Set R)
    (hA : (T.finiteNetwork R).BoundaryAccessible A)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    (h : Euc d → ℝ) {K M ε : ℝ} (hK : 0 ≤ K) (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hlength : ∀ v w : R, T.adj v w → ‖T.pos w - T.pos v‖ ≤ 2 * ε)
    (hdiam : ∀ v ∈ A, Metric.diam (T.cell v).carrier ≤ ε)
    {W : Set (Euc d)} (hW : IsOpen W) (hh : IsHarmonicOn h W)
    (hball : ∀ v ∈ A, Metric.closedBall (T.pos v) (2 * ε) ⊆ W)
    (hH : ∀ v ∈ A, ∀ x ∈ Metric.closedBall (T.pos v) (2 * ε),
      ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M)
    {α : ℝ} (hα : 0 < α) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hreg : ∀ v ∈ A, (T.cell v).diamENN ≤ C * T.incidentScale α v)
    {I : ℝ} (hI : 0 ≤ I)
    (hmass : ∀ n, T.incidentMass R (T.correctedRegions R A hA h K M ε n).val ≤
      I * (1 / 2 : ℝ) ^ n) (v : R) :
    |(T.finiteNetwork R).dirichletSolution A hA (fun v => h (T.pos v)) v - h (T.pos v)| ≤
      hypIIICost K (3 * M) ε
        (fun n => T.toTilingData.regionDiameter R
          (T.correctedRegions R A hA h K M ε n).val) := by
  let N := T.finiteNetwork R
  let S : ℕ → Set R := fun n => (T.correctedRegions R A hA h K M ε n).val
  have hsub (n : ℕ) : S n ⊆ A := (T.correctedRegions R A hA h K M ε n).property
  have hS (n : ℕ) : N.BoundaryAccessible (S n) := N.boundaryAccessible_mono (hsub n) hA
  let δ : ℕ → ℝ := fun n => T.toTilingData.regionDiameter R (S n)
  have hδ (n : ℕ) : 0 ≤ δ n := T.toTilingData.regionDiameter_nonneg R (S n)
  have hmesh (n : ℕ) : δ n ≤ ε := T.toTilingData.regionDiameter_le R (S n) hε
    (fun u hu => hdiam u (hsub n hu))
  have hneigh (n : ℕ) : ∀ u ∈ S n, ∀ w, T.adj u w → w ∈ R :=
    fun u hu => hneighbors u (hsub n hu)
  have hregS (n : ℕ) : ∀ u ∈ S n,
      (T.cell u).diamENN ≤ C * T.incidentScale α u := fun u hu => hreg u (hsub n hu)
  have hgeom := T.regionDiameter_le_geometric_of_mass R S hneigh hα.le hC hregS hI hmass
  obtain ⟨n, hempty⟩ := (T.eventually_empty_of_geometric_mass_hypIII hd R S hneigh
    hα hC hregS hI hmass).exists
  have hB (i : ℕ) (u : R) : Metric.closedBall (T.pos u) (2 * δ i) ⊆
      Metric.closedBall (T.pos u) (2 * ε) :=
    Metric.closedBall_subset_closedBall (by have := hmesh i; linarith)
  let g : R → ℝ := fun u => h (T.pos u)
  let reward : R → R → ℝ := fun u w => T.surfaceTaylorRemainder h u w
  have hq (i : ℕ) (u : R) (hu : u ∉ S (i + 1)) :
      |N.boundaryCorrectedError (S i) (hS i) g reward u| ≤
        K * M * δ i + Real.sqrt (ε * δ i) := by
    have hδi := hδ i
    apply N.abs_le_outside_trimmedErrorSet (by positivity) (Real.sqrt_nonneg _)
      (fun z hz => N.boundaryCorrectedError_boundary (S i) (hS i) g reward hz)
    exact hu
  have hnew (i : ℕ) (u : R) (hu : u ∈ S i) (w : R) (hw : w ∈ S i)
      (huw : 0 < N.a u w) : |reward u w| ≤ 6 * M * δ i ^ 2 := by
    have ha : T.adj u w := T.conductanceReal_pos_iff.mp huw
    exact T.surfaceTaylorRemainder_abs_le h (hδ i) hM
      (T.edge_dist_le_two_diam_bound ha
        (T.toTilingData.cell_diam_le_regionDiameter R (S i) hu)
        (T.toTilingData.cell_diam_le_regionDiameter R (S i) hw)) hW hh.contDiffOn
      ((hB i u).trans (hball u (hsub i hu)))
      (fun x hx => hH u (hsub i hu) x (hB i u hx))
  have hinitial (u : R) (hu : u ∈ S 0) (w : R) (_ : w ∉ S 0)
      (huw : 0 < N.a u w) : |reward u w| ≤ 6 * M * ε ^ 2 := by
    have ha : T.adj u w := T.conductanceReal_pos_iff.mp huw
    have hdist : dist (T.pos u) (T.pos w) ≤ 2 * ε := by
      simpa only [dist_eq_norm, norm_sub_rev] using hlength u w ha
    exact T.surfaceTaylorRemainder_abs_le h hε hM hdist hW hh.contDiffOn
      (hball u (hsub 0 hu)) (hH u (hsub 0 hu))
  have hbound := N.boundaryCorrectedIteration_error_bound S hS
    (fun i => T.correctedRegions_antitone R A hA h K M ε (Nat.le_succ i))
    g reward (fun i => K * M * δ i + Real.sqrt (ε * δ i))
    (fun i => 6 * M * δ i ^ 2) (fun i => by positivity) hq hnew
    (by positivity : 0 ≤ 6 * M * ε ^ 2) hinitial n hempty v
  have hcost := finite_corrected_cost_le_hypIIICost δ hK hM hε
    (show 0 ≤ C.toReal * (2 * I) ^ α by positivity)
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) α)
    (Real.rpow_lt_one (by norm_num) (by norm_num) hα) hδ hmesh hgeom n
  exact hbound.trans hcost

/-- Finite hypothesis III estimate with all energy, contraction and
termination inputs derived from the actual harmonic function and geometry. -/
theorem dirichlet_error_le_hypIIICost (hd : 1 ≤ d)
    (R : Set T.V) [Fintype R] (A : Set R)
    (hA : (T.finiteNetwork R).BoundaryAccessible A)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    (hcellD : ∀ v ∈ A, (T.cell v).carrier ⊆ interior T.domain)
    (h : Euc d → ℝ) (e : Euc d) (he : e ≠ 0) (a b : ℝ) (hab : a ≤ b)
    (hheight : ∀ v ∈ A, ∀ x ∈ (T.cell v).carrier,
      inner ℝ e x / inner ℝ e e ∈ Set.Icc a b)
    {K M ε : ℝ} (hK : 0 < K) (hM : 0 < M) (hε : 0 < ε)
    (hwidth : 12 * ((d : ℝ) * ‖e‖ * (b - a)) ≤ K)
    (hsmall : 144 * M ^ 2 * ε ^ 2 ≤ 1)
    (hlength : ∀ v w : R, T.adj v w → ‖T.pos w - T.pos v‖ ≤ 2 * ε)
    (hdiam : ∀ v ∈ A, Metric.diam (T.cell v).carrier ≤ ε)
    {W : Set (Euc d)} (hW : IsOpen W) (hh : IsHarmonicOn h W)
    (hball : ∀ v ∈ A, Metric.closedBall (T.pos v) (2 * ε) ⊆ W)
    (hH : ∀ v ∈ A, ∀ x ∈ Metric.closedBall (T.pos v) (2 * ε),
      ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M)
    {α : ℝ} (hα : 0 < α) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hreg : ∀ v ∈ A, (T.cell v).diamENN ≤ C * T.incidentScale α v)
    {I : ℝ} (hI : 0 ≤ I) (hIbound : T.incidentMass R A ≤ I) (v : R) :
    |(T.finiteNetwork R).dirichletSolution A hA (fun v => h (T.pos v)) v - h (T.pos v)| ≤
      hypIIICost K (3 * M) ε
        (fun n => T.toTilingData.regionDiameter R
          (T.correctedRegions R A hA h K M ε n).val) := by
  apply T.dirichlet_error_le_hypIIICost_of_mass_decay hd R A hA hneighbors h
    hK.le hM.le hε.le hlength hdiam hW hh hball hH hα hC hreg hI _ v
  intro n
  exact (T.correctedRegions_mass_le_geometric hd R A hA hneighbors hcellD h e he a b
    hab hheight hK hM hε hwidth hsmall hlength hdiam hW hh hball hH n).trans
    (mul_le_mul_of_nonneg_right hIbound (pow_nonneg (by norm_num) n))

end BouRabeeGwynne.OrthogonalTiling
