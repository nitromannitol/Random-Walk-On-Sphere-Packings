module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/PolytopeGaussGreen.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.ContactCoordinateFlux
public import BouRabeeGwynne.ProjectedContactPartition
public import BouRabeeGwynne.CoordinateFiberFubini
public import BouRabeeGwynne.CoordinateLaplacian
public import BouRabeeGwynne.FacetFlux

@[expose] public section

open scoped BigOperators ENNReal MeasureTheory
open MeasureTheory Laplacian

namespace BouRabeeGwynne.OrthogonalTiling

noncomputable section

variable {n : ℕ} (T : OrthogonalTiling (n + 1))

lemma upperContactFinset_eq_filter_neighborFinset (e : Euc (n + 1)) (v : T.V)
    (hvD : (T.cell v).carrier ⊆ T.domain) (hv : (T.neighbors v).Finite) :
    T.upperContactFinset e v hvD =
      (T.neighborFinset v hv).filter (fun w => 0 < inner ℝ (T.pos w - T.pos v) e) := by
  classical
  ext w
  simp only [upperContactFinset, Finset.mem_filter, T.mem_neighborFinset,
    T.toTilingData.mem_contactFinset]
  constructor
  · exact fun hw => hw.2
  · intro hw
    exact ⟨⟨hw.1.1.symm, hw.1.2.1⟩, hw⟩

lemma lowerContactFinset_eq_filter_neighborFinset (e : Euc (n + 1)) (v : T.V)
    (hvD : (T.cell v).carrier ⊆ T.domain) (hv : (T.neighbors v).Finite) :
    T.lowerContactFinset e v hvD =
      (T.neighborFinset v hv).filter (fun w => inner ℝ (T.pos w - T.pos v) e < 0) := by
  classical
  ext w
  simp only [lowerContactFinset, Finset.mem_filter, T.mem_neighborFinset,
    T.toTilingData.mem_contactFinset]
  constructor
  · exact fun hw => hw.2
  · intro hw
    exact ⟨⟨hw.1.1.symm, hw.1.2.1⟩, hw⟩

lemma integrableOn_upperEndpoint (i : Fin (n + 1)) (v : T.V)
    {f : Euc (n + 1) → ℝ} (hf : ContinuousOn f (T.cell v).carrier) :
    IntegrableOn (fun y => f ((T.cell v).upperEndpoint
      (coordinateAxis i) (coordinateAxis_ne_zero i) y))
      ((T.cell v).projectedBase (coordinateAxis i) (coordinateAxis_ne_zero i)) (μHE[n]) := by
  let P := T.cell v
  let e := coordinateAxis i
  let he := coordinateAxis_ne_zero i
  have hcont : ContinuousOn (fun y => f (P.upperEndpoint e he y))
      (P.projectedBase e he) := by
    apply hf.comp (P.continuous_upperEndpoint he).continuousOn
    intro y hy
    exact (P.mem_line_iff he y _).mpr ⟨hy.2.1, hy.2.2, le_rfl⟩
  exact hcont.integrableOn_of_subset_isCompact (P.isCompact_projectedBase he)
    (P.isCompact_projectedBase he).measurableSet Set.Subset.rfl
    (P.projectedBase_coordinate_measure_ne_top i)

lemma integrableOn_lowerEndpoint (i : Fin (n + 1)) (v : T.V)
    {f : Euc (n + 1) → ℝ} (hf : ContinuousOn f (T.cell v).carrier) :
    IntegrableOn (fun y => f ((T.cell v).lowerEndpoint
      (coordinateAxis i) (coordinateAxis_ne_zero i) y))
      ((T.cell v).projectedBase (coordinateAxis i) (coordinateAxis_ne_zero i)) (μHE[n]) := by
  let P := T.cell v
  let e := coordinateAxis i
  let he := coordinateAxis_ne_zero i
  have hcont : ContinuousOn (fun y => f (P.lowerEndpoint e he y))
      (P.projectedBase e he) := by
    apply hf.comp (P.continuous_lowerEndpoint he).continuousOn
    intro y hy
    exact (P.mem_line_iff he y _).mpr ⟨hy.2.1, le_rfl, hy.2.2⟩
  exact hcont.integrableOn_of_subset_isCompact (P.isCompact_projectedBase he)
    (P.isCompact_projectedBase he).measurableSet Set.Subset.rfl
    (P.projectedBase_coordinate_measure_ne_top i)

/-- The coordinate flux identity for the actual finite family of cell contacts.
The proof uses closed interval fibers and almost-everywhere contact partitions. -/
theorem sum_coordinate_contact_integral_eq_integral_fderiv
    (i : Fin (n + 1)) (v : T.V)
    (hvD : (T.cell v).carrier ⊆ interior T.domain) (hv : (T.neighbors v).Finite)
    {W : Set (Euc (n + 1))} (hW : IsOpen W) (hPW : (T.cell v).carrier ⊆ W)
    {f : Euc (n + 1) → ℝ} (hf : ContDiffOn ℝ 1 f W) :
    (∑ w ∈ T.neighborFinset v hv,
      ∫ x in T.facet v w, ((T.pos w - T.pos v) i / ‖T.pos w - T.pos v‖) * f x ∂μHE[n]) =
        ∫ x in (T.cell v).carrier, (fderiv ℝ f x) (coordinateAxis i) ∂volume := by
  classical
  let e := coordinateAxis i
  let he := coordinateAxis_ne_zero i
  let P := T.cell v
  let N := T.neighborFinset v hv
  let U : T.V → ℝ := fun w => ∫ y in hyperplaneProjection e '' T.facet v w,
    f (P.upperEndpoint e he y) ∂μHE[n]
  let L : T.V → ℝ := fun w => ∫ y in hyperplaneProjection e '' T.facet v w,
    f (P.lowerEndpoint e he y) ∂μHE[n]
  have hterm (w : T.V) (hw : w ∈ N) :
      (∫ x in T.facet v w, ((T.pos w - T.pos v) i / ‖T.pos w - T.pos v‖) * f x ∂μHE[n]) =
        (if 0 < (T.pos w - T.pos v) i then U w else 0) -
          (if (T.pos w - T.pos v) i < 0 then L w else 0) := by
    have hadj := (T.mem_neighborFinset hv).mp hw
    rcases lt_trichotomy 0 ((T.pos w - T.pos v) i) with hp | hz | hn
    · rw [if_pos hp, if_neg (not_lt_of_ge hp.le), sub_zero]
      exact T.integral_upper_contact_eq_projection i hadj hp f
    · simp only [← hz, div_eq_mul_inv, zero_mul, integral_zero, lt_self_iff_false,
        ↓reduceIte, sub_zero]
    · rw [if_neg (not_lt_of_ge hn.le), if_pos hn, zero_sub]
      exact T.integral_lower_contact_eq_projection i hadj hn f
  have hupper := T.integral_projectedBase_eq_sum_upperContacts (by omega) he v hvD
    (T.integrableOn_upperEndpoint i v (hf.continuousOn.mono hPW))
  have hlower := T.integral_projectedBase_eq_sum_lowerContacts (by omega) he v hvD
    (T.integrableOn_lowerEndpoint i v (hf.continuousOn.mono hPW))
  rw [T.upperContactFinset_eq_filter_neighborFinset e v _ hv,
    Finset.sum_filter] at hupper
  rw [T.lowerContactFinset_eq_filter_neighborFinset e v _ hv,
    Finset.sum_filter] at hlower
  simp only [e, inner_coordinateAxis_right] at hupper hlower
  calc
    _ = ∑ w ∈ N, ((if 0 < (T.pos w - T.pos v) i then U w else 0) -
        (if (T.pos w - T.pos v) i < 0 then L w else 0)) := Finset.sum_congr rfl hterm
    _ = (∫ y in P.projectedBase e he, f (P.upperEndpoint e he y) ∂μHE[n]) -
        (∫ y in P.projectedBase e he, f (P.lowerEndpoint e he y) ∂μHE[n]) := by
      rw [Finset.sum_sub_distrib]
      exact congrArg₂ (· - ·) hupper.symm hlower.symm
    _ = ∫ y in P.projectedBase e he,
        f (P.upperEndpoint e he y) - f (P.lowerEndpoint e he y) ∂μHE[n] :=
      (integral_sub (T.integrableOn_upperEndpoint i v (hf.continuousOn.mono hPW))
        (T.integrableOn_lowerEndpoint i v (hf.continuousOn.mono hPW))).symm
    _ = _ := (P.integral_coordinate_fderiv_eq_endpoint_integral i hW hPW hf).symm

lemma surfaceFlux_eq_sum_coordinate_contact_integral (h : Euc (n + 1) → ℝ)
    {v w : T.V} (hvw : T.adj v w) {W : Set (Euc (n + 1))} (hW : IsOpen W)
    (hh : ContDiffOn ℝ 2 h W) (hfacet : T.facet v w ⊆ W) :
    T.surfaceFlux h v w = ∑ i : Fin (n + 1),
      ∫ x in T.facet v w, ((T.pos w - T.pos v) i / ‖T.pos w - T.pos v‖) *
        (fderiv ℝ h x) (coordinateAxis i) ∂μHE[n] := by
  have hint (i : Fin (n + 1)) : IntegrableOn
      (fun x => ((T.pos w - T.pos v) i / ‖T.pos w - T.pos v‖) *
        (fderiv ℝ h x) (coordinateAxis i)) (T.facet v w) (μHE[n]) := by
    have hDcont := (hh.continuousOn_fderiv_of_isOpen hW (by norm_num)).mono hfacet
    have hcont : ContinuousOn (fun x =>
        ((T.pos w - T.pos v) i / ‖T.pos w - T.pos v‖) *
          (fderiv ℝ h x) (coordinateAxis i)) (T.facet v w) :=
      (hDcont.clm_apply continuousOn_const).const_mul _
    have hK := T.toTilingData.facet_compact v w
    exact hcont.integrableOn_of_subset_isCompact hK hK.measurableSet Set.Subset.rfl
      (T.toTilingData.facetVolume_ne_top hvw)
  unfold surfaceFlux
  simp only [Nat.add_sub_cancel]
  calc
    _ = ∫ x in T.facet v w, ∑ i : Fin (n + 1),
        ((T.pos w - T.pos v) i / ‖T.pos w - T.pos v‖) *
          (fderiv ℝ h x) (coordinateAxis i) ∂μHE[n] := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [continuousLinearMap_apply_eq_sum_coordinates]
        apply Finset.sum_congr rfl
        intro i _
        simp only [unitEdgeDirection, PiLp.smul_apply, smul_eq_mul, coordinateAxis,
          div_eq_mul_inv, mul_comm (‖T.pos w - T.pos v‖⁻¹)]
    _ = _ := integral_finsetSum _ (fun i _ => hint i)

/-- Gauss--Green for a cell, with its actual contact facets and mathlib Laplacian. -/
theorem sum_surfaceFlux_eq_integral_laplacian_succ
    (v : T.V) (hvD : (T.cell v).carrier ⊆ interior T.domain)
    (hv : (T.neighbors v).Finite) {W : Set (Euc (n + 1))}
    (hW : IsOpen W) (hPW : (T.cell v).carrier ⊆ W)
    {h : Euc (n + 1) → ℝ} (hh : ContDiffOn ℝ 2 h W) :
    (∑ w ∈ T.neighborFinset v hv, T.surfaceFlux h v w) =
      ∫ x in (T.cell v).carrier, Δ h x ∂volume := by
  have hD (i : Fin (n + 1)) : ContDiffOn ℝ 1
      (fun y => (fderiv ℝ h y) (coordinateAxis i)) W :=
    contDiffOn_directional_fderiv hW hh _
  have hint (i : Fin (n + 1)) : IntegrableOn
      (fun x => (fderiv ℝ (fun y => (fderiv ℝ h y) (coordinateAxis i)) x)
        (coordinateAxis i)) (T.cell v).carrier :=
    ((((hD i).continuousOn_fderiv_of_isOpen hW le_rfl).clm_apply
      continuousOn_const).mono hPW).integrableOn_compact (T.cell v).compact
  calc
    _ = ∑ w ∈ T.neighborFinset v hv, ∑ i : Fin (n + 1),
        ∫ x in T.facet v w, ((T.pos w - T.pos v) i / ‖T.pos w - T.pos v‖) *
          (fderiv ℝ h x) (coordinateAxis i) ∂μHE[n] := by
      apply Finset.sum_congr rfl
      intro w hw
      exact T.surfaceFlux_eq_sum_coordinate_contact_integral h
        ((T.mem_neighborFinset hv).mp hw) hW hh (fun x hx => hPW hx.1)
    _ = ∑ i : Fin (n + 1), ∑ w ∈ T.neighborFinset v hv,
        ∫ x in T.facet v w, ((T.pos w - T.pos v) i / ‖T.pos w - T.pos v‖) *
          (fderiv ℝ h x) (coordinateAxis i) ∂μHE[n] := Finset.sum_comm
    _ = ∑ i : Fin (n + 1), ∫ x in (T.cell v).carrier,
        (fderiv ℝ (fun y => (fderiv ℝ h y) (coordinateAxis i)) x)
          (coordinateAxis i) ∂volume := by
      apply Finset.sum_congr rfl
      intro i _
      exact T.sum_coordinate_contact_integral_eq_integral_fderiv i v hvD hv hW hPW (hD i)
    _ = ∫ x in (T.cell v).carrier, ∑ i : Fin (n + 1),
        (fderiv ℝ (fun y => (fderiv ℝ h y) (coordinateAxis i)) x)
          (coordinateAxis i) ∂volume := (integral_finsetSum _ (fun i _ => hint i)).symm
    _ = _ := by
      apply setIntegral_congr_fun (T.cell v).compact.measurableSet
      intro x hx
      exact (laplacian_eq_sum_coordinate_second hW hh (hPW hx)).symm

end

variable {d : ℕ} (T : OrthogonalTiling d)

/-- Dimension-uniform form, including intervals in dimension one. -/
theorem sum_surfaceFlux_eq_integral_laplacian
    (hd : 1 ≤ d) (v : T.V) (hvD : (T.cell v).carrier ⊆ interior T.domain)
    (hv : (T.neighbors v).Finite) {W : Set (Euc d)}
    (hW : IsOpen W) (hPW : (T.cell v).carrier ⊆ W)
    {h : Euc d → ℝ} (hh : ContDiffOn ℝ 2 h W) :
    (∑ w ∈ T.neighborFinset v hv, T.surfaceFlux h v w) =
      ∫ x in (T.cell v).carrier, Δ h x ∂volume := by
  cases d with
  | zero => omega
  | succ n => exact T.sum_surfaceFlux_eq_integral_laplacian_succ v hvD hv hW hPW hh

/-- The finite actual outward contact-flux sum vanishes for a harmonic function. -/
theorem sum_surfaceFlux_eq_zero_of_harmonic
    (hd : 1 ≤ d) (v : T.V) (hvD : (T.cell v).carrier ⊆ interior T.domain)
    (hv : (T.neighbors v).Finite) {W : Set (Euc d)}
    (hW : IsOpen W) (hPW : (T.cell v).carrier ⊆ W)
    {h : Euc d → ℝ} (hh : IsHarmonicOn h W) :
    (∑ w ∈ T.neighborFinset v hv, T.surfaceFlux h v w) = 0 := by
  rw [T.sum_surfaceFlux_eq_integral_laplacian hd v hvD hv hW hPW hh.contDiffOn]
  exact setIntegral_eq_zero_of_forall_eq_zero fun x hx => hh.laplacian_eq_zero (hPW hx)

end BouRabeeGwynne.OrthogonalTiling
