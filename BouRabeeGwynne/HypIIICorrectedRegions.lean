module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/HypIIICorrectedRegions.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.HypIIICorrectedTrimming
public import BouRabeeGwynne.RegionDiameter

@[expose] public section

/-! The actual adaptive corrected iteration and its geometric mass decay. -/

open scoped Classical BigOperators

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

noncomputable def correctedRegionStep (R : Set T.V) [Fintype R] (A : Set R)
    (hA : (T.finiteNetwork R).BoundaryAccessible A) (h : Euc d → ℝ)
    (K M ε : ℝ) (S : {S : Set R // S ⊆ A}) : {S : Set R // S ⊆ A} :=
  let N := T.finiteNetwork R
  let hS := N.boundaryAccessible_mono S.property hA
  let f := N.boundaryCorrectedError S.val hS (fun v => h (T.pos v))
    (fun v w => T.surfaceTaylorRemainder h v w)
  let δ := T.toTilingData.regionDiameter R S.val
  ⟨N.trimmedErrorSet S.val f (K * M * δ) (Real.sqrt (ε * δ)),
    (N.trimmedErrorSet_subset S.val f _ _).trans S.property⟩

noncomputable def correctedRegions (R : Set T.V) [Fintype R] (A : Set R)
    (hA : (T.finiteNetwork R).BoundaryAccessible A) (h : Euc d → ℝ)
    (K M ε : ℝ) : ℕ → {S : Set R // S ⊆ A} :=
  fun n => Nat.rec ⟨A, Set.Subset.rfl⟩
    (fun _ S => T.correctedRegionStep R A hA h K M ε S) n

lemma correctedRegions_antitone (R : Set T.V) [Fintype R] (A : Set R)
    (hA : (T.finiteNetwork R).BoundaryAccessible A) (h : Euc d → ℝ) (K M ε : ℝ) :
    Antitone (fun n => (T.correctedRegions R A hA h K M ε n).val) := by
  apply antitone_nat_of_succ_le
  intro n
  exact (T.finiteNetwork R).trimmedErrorSet_subset _ _ _ _

@[simp] lemma incidentMass_empty (R : Set T.V) [Fintype R] :
    T.incidentMass R ∅ = 0 := by
  rw [T.incidentMass_eq_half_ordered]
  simp

/-- Every step uses its actual current maximum diameter and its actual
corrected Dirichlet solution; the mass halves at each step. -/
theorem correctedRegions_mass_le_geometric (hd : 1 ≤ d)
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
      ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M) :
    ∀ n, T.incidentMass R (T.correctedRegions R A hA h K M ε n).val ≤
      T.incidentMass R A * (1 / 2 : ℝ) ^ n := by
  let S := T.correctedRegions R A hA h K M ε
  have hsub (n : ℕ) : (S n).val ⊆ A := (S n).property
  have hstep (n : ℕ) : T.incidentMass R (S (n + 1)).val ≤
      (1 / 2 : ℝ) * T.incidentMass R (S n).val := by
    by_cases hempty : (S n).val = ∅
    · have hnext : (S (n + 1)).val = ∅ := by
        apply Set.eq_empty_of_forall_notMem
        intro v hv
        have hvold : v ∈ (S n).val :=
          T.correctedRegions_antitone R A hA h K M ε (Nat.le_succ n) hv
        simpa only [hempty, Set.mem_empty_iff_false] using hvold
      rw [hnext, hempty, T.incidentMass_empty, mul_zero]
    · let δ := T.toTilingData.regionDiameter R (S n).val
      have hδ : 0 < δ := T.toTilingData.regionDiameter_pos hd R
        (Set.nonempty_iff_ne_empty.mpr hempty)
      have hδε : δ ≤ ε := T.toTilingData.regionDiameter_le R (S n).val hε.le
        (fun v hv => hdiam v (hsub n hv))
      have hB (v : R) : Metric.closedBall (T.pos v) (2 * δ) ⊆
          Metric.closedBall (T.pos v) (2 * ε) :=
        Metric.closedBall_subset_closedBall (by linarith)
      exact T.boundaryCorrected_trimmed_mass_le_half hd R (S n).val
        ((T.finiteNetwork R).boundaryAccessible_mono (hsub n) hA)
        (fun v hv => hneighbors v (hsub n hv))
        (fun v hv => hcellD v (hsub n hv)) h e he a b hab
        (fun v hv => hheight v (hsub n hv)) hK hM hε hδ hδε hwidth hsmall hlength
        (fun _ hv => T.toTilingData.cell_diam_le_regionDiameter R (S n).val hv)
        hW hh (fun v hv => (hB v).trans (hball v (hsub n hv)))
        (fun v hv x hx => hH v (hsub n hv) x (hB v hx))
  intro n
  induction n with
  | zero => simp only [S, correctedRegions, Nat.rec_zero, pow_zero, mul_one, le_refl]
  | succ n ih =>
    calc
      _ ≤ (1 / 2 : ℝ) * T.incidentMass R (S n).val := hstep n
      _ ≤ (1 / 2 : ℝ) * (T.incidentMass R A * (1 / 2 : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; ring

end BouRabeeGwynne.OrthogonalTiling
