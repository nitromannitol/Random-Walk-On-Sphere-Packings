-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (files `BouRabeeGwynne/Section3Accessibility.lean`, `CellVolumeBound.lean`, `Section3CellMass.lean`,
-- `Section3InternalMass.lean`, `Section3MassDecay.lean` and `HypIIICorrectedTrimming.lean` at commit
-- cf73d6e): the Section 3 mass estimates, for complete cells.
import SpherePackings.Support.Complete.Columns
import BouRabeeGwynne.Section3Accessibility
import BouRabeeGwynne.Section3CellMass
import BouRabeeGwynne.Section3MassDecay
import BouRabeeGwynne.HypIIICorrectedTrimming

/-!
# Section 3 estimates for complete cells

leobon12's Section 3 lemmas that take `P_v ⊆ interior D` (accessibility of the boundary, cell volume
against the incident mass, the trimmed mass, the decay of the harmonic iteration, the corrected
trimming), re-proved for complete cells (`CompleteCell`, `rw-spheres-corrected.tex`, Correction 4),
through the column lemmas of `SpherePackings.Support.Complete.Columns`.
-/

namespace SpherePackings

open BouRabeeGwynne BouRabeeGwynne.OrthogonalTiling MeasureTheory

open scoped Classical ENNReal

variable {d : ℕ}

/-- Finite regions of complete cells have positive-conductance paths to their boundary. -/
theorem finiteNetwork_boundaryAccessible_of_complete (hd : 1 ≤ d) (T : OrthogonalTiling d)
    (e : Euc d) (he : e ≠ 0) (R : Set T.V) [Fintype R] (A : Set R)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    (hcomplete : ∀ v ∈ A, CompleteCell T v) :
    (T.finiteNetwork R).BoundaryAccessible A := by
  intro v hv
  have hgood := ae_column_boundary_path_of_complete hd T e he R A hneighbors hcomplete
  obtain ⟨y, hy, hpath⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    ((T.cell v).projectedBase_measure_pos he).ne' (ae_restrict_of_ae hgood)
  obtain ⟨w, hw, hreach⟩ := hpath v ⟨hv, hy⟩
  have hp := (SimpleGraph.reachable_iff_reflTransGen v w).mp hreach
  have hwbase : y ∈ (T.cell w).projectedBase e he := by
    rcases hp.cases_tail with h | ⟨z, _, hzw⟩
    · simpa only [h] using hy
    · obtain ⟨x, hx, hxy⟩ := hzw.2.2
      rw [(T.cell w).projectedBase_eq_image he]
      exact ⟨x, hx.2, hxy⟩
  refine ⟨w, fun hwA => hw ⟨hwA, hwbase⟩, ?_⟩
  have hmono : (T.columnGraph R A e y).Adj ≤
      (fun a b : R => 0 < (T.finiteNetwork R).a a b) :=
    fun a b hab => T.conductanceReal_pos_iff.mpr hab.1
  exact Relation.ReflTransGen.mono hmono v w hp

/-- The volume of a complete cell is at most the sum of the dual volumes of its edges. -/
theorem cell_measure_le_sum_adjacent_dualVolume_of_complete (hd : 1 ≤ d) (T : OrthogonalTiling d)
    {v : T.V} (hv : CompleteCell T v) :
    μHE[d] (T.cell v).carrier ≤
      ∑ w ∈ T.neighborFinset v hv.1, T.toTilingData.dualVolume v w := by
  have hcover : (T.cell v).carrier ⊆
      ⋃ w ∈ T.neighborFinset v hv.1, T.toTilingData.dualPolytope v w := by
    intro x hx
    obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp (hv.cell_subset_iUnion_dualPolytope hd hx)
    exact Set.mem_iUnion₂.mpr ⟨w, (T.mem_neighborFinset hv.1).mpr hw, hxw⟩
  calc
    μHE[d] (T.cell v).carrier ≤ μHE[d]
        (⋃ w ∈ T.neighborFinset v hv.1, T.toTilingData.dualPolytope v w) := measure_mono hcover
    _ ≤ ∑ w ∈ T.neighborFinset v hv.1, T.toTilingData.dualVolume v w :=
      measure_biUnion_finset_le (T.neighborFinset v hv.1) (T.toTilingData.dualPolytope v)

theorem cellVolume_le_adjacent_row_of_complete (hd : 1 ≤ d) (T : OrthogonalTiling d)
    (R : Set T.V) [Fintype R] (A : Set R)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    {v : R} (hv : v ∈ A) (hvc : CompleteCell T v) :
    (T.cell v).volume.toReal ≤ ∑ w : R,
      if T.adj v w then (T.facetVolume v w).toReal * ‖T.pos w - T.pos v‖ else 0 := by
  let E := T.neighborFinset v hvc.1
  let j : T.V → R := fun w => if hw : w ∈ R then ⟨w, hw⟩ else v
  have hER : ∀ w ∈ E, w ∈ R := fun w hw => hneighbors v hv w ((T.mem_neighborFinset hvc.1).mp hw)
  have hj : ∀ w ∈ E, (j w : T.V) = w := by
    intro w hw
    simp only [j, hER w hw, dite_true]
  have hinj : Set.InjOn j E := by
    intro w hw z hz heq
    simpa only [hj w hw, hj z hz] using congrArg Subtype.val heq
  have hsum : (∑ w ∈ E, T.toTilingData.dualVolume v w) ≤
      ∑ w : R, if T.adj v w then T.toTilingData.dualVolume v w else 0 := by
    apply Finset.sum_le_sum_of_injOn j hinj (Finset.subset_univ _)
    · intro w hw
      simp only [hj w hw, (T.mem_neighborFinset hvc.1).mp hw, ↓reduceIte, le_refl]
    · intro w _ _
      exact zero_le
  have hmeasure : (T.cell v).volume ≤
      ∑ w : R, if T.adj v w then T.toTilingData.dualVolume v w else 0 :=
    (cell_measure_le_sum_adjacent_dualVolume_of_complete hd T hvc).trans hsum
  have hfinite (w : R) :
      (if T.adj v w then T.toTilingData.dualVolume v w else 0) ≠ ∞ := by
    split_ifs
    · exact (T.toTilingData.dualVolume_lt_top v w).ne
    · exact ENNReal.zero_ne_top
  have hreal := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun w _ => hfinite w)) hmeasure
  rw [ENNReal.toReal_sum (fun w _ => hfinite w)] at hreal
  apply hreal.trans
  apply Finset.sum_le_sum
  intro w _
  by_cases ha : T.adj v w
  · simp only [ha, ↓reduceIte]
    rw [mul_comm, T.edgeLength_mul_facetVolume_eq_dim_mul_dualVolume hd ha]
    exact le_mul_of_one_le_left ENNReal.toReal_nonneg (by exact_mod_cast hd)
  · simp only [ha, ↓reduceIte, ENNReal.toReal_zero, le_refl]

theorem cellVolume_le_twice_incidentMass_of_complete (hd : 1 ≤ d) (T : OrthogonalTiling d)
    (R : Set T.V) [Fintype R] (A : Set R)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    {v : R} (hv : v ∈ A) (hvc : CompleteCell T v) :
    (T.cell v).volume.toReal ≤ 2 * T.incidentMass R A := by
  have hrow := cellVolume_le_adjacent_row_of_complete hd T R A hneighbors hv hvc
  let F : R → R → ℝ := fun u w =>
    if T.adj u w ∧ (u ∈ A ∨ w ∈ A) then
      (T.facetVolume u w).toReal * ‖T.pos w - T.pos u‖ else 0
  have hnonneg : ∀ u w, 0 ≤ F u w := by
    intro u w
    dsimp [F]
    split_ifs
    · exact mul_nonneg ENNReal.toReal_nonneg (norm_nonneg _)
    · exact le_rfl
  have hrow' : (T.cell v).volume.toReal ≤ ∑ w, F v w := by
    simpa only [F, hv, true_or, and_true] using hrow
  have hsingle : (∑ w, F v w) ≤ ∑ u, ∑ w, F u w :=
    Finset.single_le_sum (fun u _ => Finset.sum_nonneg (fun w _ => hnonneg u w))
      (Finset.mem_univ v)
  apply hrow'.trans (hsingle.trans_eq _)
  rw [T.incidentMass_eq_half_ordered]
  dsimp [F]
  ring

theorem incidentMass_trimmed_le_contraction_factor_of_complete (hd : 1 ≤ d)
    (T : OrthogonalTiling d) (R : Set T.V) [Fintype R] (A : Set R)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    (hcomplete : ∀ v ∈ A, CompleteCell T v)
    (f : T.V → ℝ) (hzero : ∀ v : R, v ∉ A → f v = 0)
    (e : Euc d) (he : e ≠ 0) (a b : ℝ) (hab : a ≤ b)
    (hheight : ∀ v ∈ A, ∀ x ∈ (T.cell v).carrier,
      inner ℝ e x / inner ℝ e e ∈ Set.Icc a b)
    {C τ L ℓ : ℝ} (hC : 0 ≤ C) (hτ : 0 < τ) (hℓ : 0 < ℓ)
    (hlength : ∀ v w : R, T.adj v w → ‖T.pos w - T.pos v‖ ≤ L)
    (henergy : T.incidentEnergy R A f ≤ C ^ 2 * T.incidentMass R A) :
    T.incidentMass R ((T.finiteNetwork R).trimmedErrorSet A (fun v => f v) τ ℓ) ≤
      ((d : ℝ) * ‖e‖ * (b - a) * C / τ + (L ^ 2 / ℓ ^ 2) * C ^ 2) *
        T.incidentMass R A := by
  have hm := T.incidentMass_nonneg R A
  have hsq : T.incidentEnergy R A f * T.incidentMass R A ≤
      (C * T.incidentMass R A) ^ 2 := by
    calc
      _ ≤ (C ^ 2 * T.incidentMass R A) * T.incidentMass R A :=
        mul_le_mul_of_nonneg_right henergy hm
      _ = _ := by ring
  have hsqrt := Real.sqrt_le_iff.mpr ⟨mul_nonneg hC hm, hsq⟩
  rw [Real.sqrt_mul (T.incidentEnergy_nonneg R A f)] at hsqrt
  have hbad : μHE[d - 1] (T.columnBadSet R A e he f τ) ≤
      ENNReal.ofReal (C * T.incidentMass R A / τ) :=
    (column_bad_measure_le_of_complete hd T e he R A hneighbors hcomplete f hzero hτ).trans
      (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hsqrt hτ.le))
  have hinter := T.internalMass_bad_le_of_column_bound hd R A f τ e he a b hab
    hheight (div_nonneg (mul_nonneg hC hm) hτ.le) hbad
  have hE : (T.finiteNetwork R).energy (fun v : R => f v) ≤
      C ^ 2 * T.incidentMass R A := by
    rw [← T.incidentEnergy_eq_networkEnergy R A f hzero]
    exact henergy
  calc
    _ ≤ T.internalMass R (FiniteConductanceNetwork.errorBadSet A (fun v => f v) τ) +
        (L ^ 2 / ℓ ^ 2) * (T.finiteNetwork R).energy (fun v => f v) :=
      T.incidentMass_trimmed_le_internalMass_add_scaled_energy R A f τ hℓ hlength
    _ ≤ (d : ℝ) * ‖e‖ * (b - a) * (C * T.incidentMass R A / τ) +
        (L ^ 2 / ℓ ^ 2) * (C ^ 2 * T.incidentMass R A) :=
      add_le_add hinter (mul_le_mul_of_nonneg_left hE
        (div_nonneg (sq_nonneg _) (sq_nonneg _)))
    _ = _ := by ring

theorem harmonicIteration_mass_le_geometric_of_complete (hd : 1 ≤ d) (T : OrthogonalTiling d)
    (R : Set T.V) [Fintype R] (A : Set R)
    (haccess : (T.finiteNetwork R).BoundaryAccessible A)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    (hcomplete : ∀ v ∈ A, CompleteCell T v)
    (g : R → ℝ) (e : Euc d) (he : e ≠ 0) (a b : ℝ) (hab : a ≤ b)
    (hheight : ∀ v ∈ A, ∀ x ∈ (T.cell v).carrier,
      inner ℝ e x / inner ℝ e e ∈ Set.Icc a b)
    {C τ L ℓ : ℝ} (hC : 0 ≤ C) (hτ : 0 < τ) (hℓ : 0 < ℓ)
    (hlength : ∀ v w : R, T.adj v w → ‖T.pos w - T.pos v‖ ≤ L)
    (henergy : ∀ S ⊆ A, ∀ h : R → ℝ,
      (T.finiteNetwork R).SolvesDirichlet S g h →
      (T.finiteNetwork R).energy (h - g) ≤ C ^ 2 * T.incidentMass R S)
    (hfactor : (d : ℝ) * ‖e‖ * (b - a) * C / τ + (L ^ 2 / ℓ ^ 2) * C ^ 2 ≤ 1 / 2) :
    ∀ j, T.incidentMass R
      ((T.finiteNetwork R).harmonicIteration A haccess g (fun _ => τ) (fun _ => ℓ) j).region ≤
      T.incidentMass R A * (1 / 2 : ℝ) ^ j := by
  let N := T.finiteNetwork R
  let s := N.harmonicIteration A haccess g (fun _ => τ) (fun _ => ℓ)
  have hsub (j : ℕ) : (s j).region ⊆ A :=
    N.harmonicIteration_region_antitone A haccess g (fun _ => τ) (fun _ => ℓ)
      (Nat.zero_le j)
  have hstep (j : ℕ) : T.incidentMass R (s (j + 1)).region ≤
      (1 / 2 : ℝ) * T.incidentMass R (s j).region := by
    let f := T.finiteAmbientFunction R ((s j).value - g)
    have hzero : ∀ v : R, v ∉ (s j).region → f v = 0 := by
      intro v hv
      simp only [f, T.finiteAmbientFunction_apply, Pi.sub_apply,
        (s j).solves.2 v hv, sub_self]
    have hE : T.incidentEnergy R (s j).region f ≤
        C ^ 2 * T.incidentMass R (s j).region := by
      rw [T.incidentEnergy_eq_networkEnergy R (s j).region f hzero]
      have heq : (fun v : R => f v) = (s j).value - g := by
        funext v
        exact T.finiteAmbientFunction_apply R _ v
      rw [heq]
      exact henergy _ (hsub j) _ (s j).solves
    have htrim := incidentMass_trimmed_le_contraction_factor_of_complete hd T R (s j).region
      (fun v hv => hneighbors v (hsub j hv))
      (fun v hv => hcomplete v (hsub j hv)) f hzero e he a b hab
      (fun v hv => hheight v (hsub j hv)) hC hτ hℓ hlength hE
    have heq : (s (j + 1)).region = N.trimmedErrorSet (s j).region
        (fun v : R => f v) τ ℓ := by
      simp only [f, T.finiteAmbientFunction_apply]
      rfl
    rw [heq]
    exact htrim.trans (mul_le_mul_of_nonneg_right hfactor (T.incidentMass_nonneg _ _))
  intro j
  induction j with
  | zero =>
    simp [FiniteConductanceNetwork.harmonicIteration,
      FiniteConductanceNetwork.HarmonicIterationState.initial]
  | succ j ih =>
    calc
      _ ≤ (1 / 2 : ℝ) * T.incidentMass R (s j).region := hstep j
      _ ≤ (1 / 2 : ℝ) * (T.incidentMass R A * (1 / 2 : ℝ) ^ j) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; ring

theorem correctedError_trimmed_mass_le_half_of_complete (hd : 1 ≤ d) (T : OrthogonalTiling d)
    (R : Set T.V) [Fintype R] (A : Set R)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    (hcomplete : ∀ v ∈ A, CompleteCell T v)
    (f : R → ℝ) (hzero : ∀ v, v ∉ A → f v = 0)
    (e : Euc d) (he : e ≠ 0) (a b : ℝ) (hab : a ≤ b)
    (hheight : ∀ v ∈ A, ∀ x ∈ (T.cell v).carrier,
      inner ℝ e x / inner ℝ e e ∈ Set.Icc a b)
    {K M ε δ : ℝ} (hK : 0 < K) (hM : 0 < M) (hε : 0 < ε)
    (hδ : 0 < δ) (hδε : δ ≤ ε)
    (hwidth : 12 * ((d : ℝ) * ‖e‖ * (b - a)) ≤ K)
    (hsmall : 144 * M ^ 2 * ε ^ 2 ≤ 1)
    (hlength : ∀ v w : R, T.adj v w → ‖T.pos w - T.pos v‖ ≤ 2 * ε)
    (henergy : (T.finiteNetwork R).energy f ≤
      9 * M ^ 2 * δ ^ 2 * T.incidentMass R A) :
    T.incidentMass R ((T.finiteNetwork R).trimmedErrorSet A f
      (K * M * δ) (Real.sqrt (ε * δ))) ≤ (1 / 2 : ℝ) * T.incidentMass R A := by
  let F := T.finiteAmbientFunction R f
  have hF : (fun v : R => F v) = f := by
    funext v
    exact T.finiteAmbientFunction_apply R f v
  have hzeroF : ∀ v : R, v ∉ A → F v = 0 := by
    intro v hv
    simpa only [F, T.finiteAmbientFunction_apply] using hzero v hv
  have hE : T.incidentEnergy R A F ≤ (3 * M * δ) ^ 2 * T.incidentMass R A := by
    rw [T.incidentEnergy_eq_networkEnergy R A F hzeroF, hF]
    convert henergy using 1
    ring
  have htrim := incidentMass_trimmed_le_contraction_factor_of_complete hd T R A hneighbors
    hcomplete F hzeroF e he a b hab hheight (C := 3 * M * δ) (τ := K * M * δ)
    (L := 2 * ε) (ℓ := Real.sqrt (ε * δ))
    (by positivity) (by positivity) (Real.sqrt_pos.mpr (mul_pos hε hδ)) hlength hE
  rw [hF] at htrim
  have hfactor : (d : ℝ) * ‖e‖ * (b - a) * (3 * M * δ) / (K * M * δ) +
      ((2 * ε) ^ 2 / (Real.sqrt (ε * δ)) ^ 2) * (3 * M * δ) ^ 2 ≤ 1 / 2 := by
    have hid : (d : ℝ) * ‖e‖ * (b - a) * (3 * M * δ) / (K * M * δ) +
        ((2 * ε) ^ 2 / (Real.sqrt (ε * δ)) ^ 2) * (3 * M * δ) ^ 2 =
        3 * ((d : ℝ) * ‖e‖ * (b - a)) / K + 36 * M ^ 2 * ε * δ := by
      rw [Real.sq_sqrt (mul_pos hε hδ).le]
      field_simp [hK.ne', hM.ne', hε.ne', hδ.ne']
      ring
    rw [hid]
    have hfirst : 3 * ((d : ℝ) * ‖e‖ * (b - a)) / K ≤ 1 / 4 :=
      (div_le_iff₀ hK).mpr (by linarith)
    have hsecond : 36 * M ^ 2 * ε * δ ≤ 1 / 4 := by
      have hle := mul_le_mul_of_nonneg_left hδε
        (show 0 ≤ 36 * M ^ 2 * ε by positivity)
      nlinarith
    linarith
  exact htrim.trans (mul_le_mul_of_nonneg_right hfactor (T.incidentMass_nonneg R A))

end SpherePackings
