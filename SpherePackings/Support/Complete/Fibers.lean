module

-- Built on Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne (commit cf73d6e).
public import BouRabeeGwynne.ProjectedBase
public import BouRabeeGwynne.FacetNull
public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Tactic.Module
public import Mathlib.Analysis.Convex.Measure

@[expose] public section

/-!
# Almost every line through a polytope meets it in a nondegenerate segment

For a convex polytope `P` and a direction `e ≠ 0`, the line `y + ℝ e` over almost every point `y` of
the projected base meets `P` in a segment of positive length.  The degenerate points lie on the
relative boundary of the (convex) projected base, which is null for the `(d - 1)`-dimensional
Hausdorff measure.
-/

namespace SpherePackings

open BouRabeeGwynne MeasureTheory
open scoped Topology

/-- Moving from `y0` through `y` past `y` stays inside a convex set `B` when `y` is in its
intrinsic interior. -/
private lemma exists_pos_add_smul_sub_mem {d : ℕ} {B : Set (Euc d)} {y y0 : Euc d}
    (hy : y ∈ intrinsicInterior ℝ B) (hy0 : y0 ∈ B) :
    ∃ η : ℝ, 0 < η ∧ y + η • (y - y0) ∈ B := by
  obtain ⟨z, hz, hzy⟩ := mem_intrinsicInterior.mp hy
  have hyA : y ∈ affineSpan ℝ B := subset_affineSpan ℝ B (intrinsicInterior_subset hy)
  have hy0A : y0 ∈ affineSpan ℝ B := subset_affineSpan ℝ B hy0
  have hdir : y - y0 ∈ (affineSpan ℝ B).direction := by
    simpa only [vsub_eq_sub] using AffineSubspace.vsub_mem_direction hyA hy0A
  have hmem : ∀ t : ℝ, t • (y - y0) + y ∈ affineSpan ℝ B := fun t =>
    AffineSubspace.vadd_mem_of_mem_direction (Submodule.smul_mem _ t hdir) hyA
  let G : ℝ → affineSpan ℝ B := fun t => ⟨t • (y - y0) + y, hmem t⟩
  have hG : Continuous G := Continuous.subtype_mk (by fun_prop) hmem
  have hG0 : G 0 = z := Subtype.ext (by simp [G, hzy])
  have hG0mem : G 0 ∈ interior ((↑) ⁻¹' B : Set (affineSpan ℝ B)) := by
    rw [hG0]
    exact hz
  have hnhds : G ⁻¹' interior ((↑) ⁻¹' B : Set (affineSpan ℝ B)) ∈ 𝓝 (0 : ℝ) :=
    hG.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hG0mem)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  have hmem_ball : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
    linarith
  have hGin : G (ε / 2) ∈ interior ((↑) ⁻¹' B : Set (affineSpan ℝ B)) := hball hmem_ball
  have hGB : G (ε / 2) ∈ (↑) ⁻¹' B := interior_subset hGin
  refine ⟨ε / 2, half_pos hε, ?_⟩
  rw [add_comm]
  exact hGB

/-- A nonzero direction is recovered from its orthogonal projection and its own coordinate. -/
private lemma eq_hyperplaneProjection_add {d : ℕ} (e x : Euc d) :
    x = hyperplaneProjection e x + (inner ℝ e x / inner ℝ e e) • e := by
  rw [hyperplaneProjection_apply, sub_add_cancel]

/-- Over every point of the relative interior of the projected base, the fibre has positive
length. -/
theorem lowerFiber_lt_upperFiber_of_mem_intrinsicInterior {d : ℕ} (P : ConvexPolytope d)
    {e : Euc d} (he : e ≠ 0) {y : Euc d}
    (hy : y ∈ intrinsicInterior ℝ (P.projectedBase e he)) :
    P.lowerFiber e he y < P.upperFiber e he y := by
  obtain ⟨p, hp⟩ := P.interior_nonempty
  have hpc : p ∈ P.carrier := interior_subset hp
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hp)
  have hy0 : hyperplaneProjection e p ∈ P.projectedBase e he := by
    rw [P.projectedBase_eq_image he]
    exact ⟨p, hpc, rfl⟩
  obtain ⟨η, hη, hy1⟩ := exists_pos_add_smul_sub_mem hy hy0
  rw [P.projectedBase_eq_image he] at hy1
  obtain ⟨k1, hk1, hk1y⟩ := hy1
  have hpos : 0 < 1 + η := by linarith
  obtain ⟨a, ha, ha1⟩ : ∃ a : ℝ, 0 < a ∧ a * (1 + η) = 1 :=
    ⟨1 / (1 + η), div_pos one_pos hpos, one_div_mul_cancel hpos.ne'⟩
  have hsum : a + a * η = 1 := by
    rw [← ha1]
    ring
  have hc : 0 < a * η := mul_pos ha hη
  obtain ⟨q, hq⟩ : ∃ q : ℝ → Euc d, ∀ s, q s = a • k1 + (a * η) • (p + s • e) :=
    ⟨_, fun s => rfl⟩
  have hqmem : ∀ s : ℝ, ‖s • e‖ < ρ → q s ∈ P.carrier := by
    intro s hs
    have hps : p + s • e ∈ P.carrier := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact hs
    rw [hq]
    exact P.convex hk1 hps ha.le hc.le hsum
  have hproj : ∀ s : ℝ, hyperplaneProjection e (q s) = y := by
    have key : ∀ w : Euc d, a • (y + η • (y - w)) + (a * η) • w = y := by
      intro w
      have h : a • (y + η • (y - w)) + (a * η) • w = (a * (1 + η)) • y := by module
      rw [h, ha1, one_smul]
    intro s
    rw [hq, map_add, map_smul, map_smul, hyperplaneProjection_add_smul he, hk1y]
    exact key _
  have hq_shift : ∀ s : ℝ, q s = q 0 + (a * η * s) • e := by
    intro s
    simp only [hq]
    module
  obtain ⟨τ, hq0⟩ : ∃ τ : ℝ, q 0 = y + τ • e := by
    refine ⟨inner ℝ e (q 0) / inner ℝ e e, ?_⟩
    have h := eq_hyperplaneProjection_add e (q 0)
    rwa [hproj 0] at h
  have hline : ∀ s : ℝ, ‖s • e‖ < ρ → y + (τ + a * η * s) • e ∈ P.carrier := by
    intro s hs
    have heq : q s = y + (τ + a * η * s) • e := by
      rw [hq_shift s, hq0]
      module
    rw [← heq]
    exact hqmem s hs
  have hρ2 : 0 < ρ / 2 / ‖e‖ := div_pos (half_pos hρ) (norm_pos_iff.mpr he)
  have hnorm : ‖(ρ / 2 / ‖e‖) • e‖ = ρ / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ2, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr he)]
  obtain ⟨_, hlo, _⟩ := (P.mem_line_iff he y _).mp
    (hline (-(ρ / 2 / ‖e‖)) (by rw [neg_smul, norm_neg, hnorm]; linarith))
  obtain ⟨_, _, hup⟩ := (P.mem_line_iff he y _).mp
    (hline (ρ / 2 / ‖e‖) (by rw [hnorm]; linarith))
  nlinarith [mul_pos hc hρ2]

/-- The relative boundary of a closed convex set `B` is null for the Hausdorff measure of the
dimension of its affine span. -/
private lemma euclideanHausdorffMeasure_diff_intrinsicInterior_eq_zero {d : ℕ} {B : Set (Euc d)}
    (hcl : IsClosed B) (hconv : Convex ℝ B) (hne : B.Nonempty) :
    μHE[Module.finrank ℝ (affineSpan ℝ B).direction] (B \ intrinsicInterior ℝ B) = 0 := by
  obtain ⟨p, hp⟩ := hne
  let A := affineSpan ℝ B
  let pA : A := ⟨p, subset_affineSpan ℝ B hp⟩
  let : Nonempty A := ⟨pA⟩
  let iso : A.direction ≃ᵢ A := IsometryEquiv.vaddConst pA
  let f : A.direction → Euc d := fun a => (iso a).val
  let u : Set A.direction := f ⁻¹' B
  have hf : Isometry f := isometry_subtype_coe.comp iso.isometry
  have hu_closed : IsClosed u := hcl.preimage hf.continuous
  have hu_convex : Convex ℝ u :=
    (hconv.translate_preimage_left p).linear_preimage A.direction.subtype
  have hfrontier : B \ intrinsicInterior ℝ B ⊆ f '' frontier u := by
    rintro x ⟨hxB, hxn⟩
    have hxA : x ∈ A := subset_affineSpan ℝ B hxB
    have hdir : x - p ∈ A.direction := by
      simpa only [vsub_eq_sub] using
        AffineSubspace.vsub_mem_direction hxA (subset_affineSpan ℝ B hp)
    have hfx : f ⟨x - p, hdir⟩ = x := by
      simp [f, iso, pA]
    refine ⟨⟨x - p, hdir⟩, ?_, hfx⟩
    rw [hu_closed.frontier_eq]
    refine ⟨?_, ?_⟩
    · show f ⟨x - p, hdir⟩ ∈ B
      rw [hfx]
      exact hxB
    · intro hint
      apply hxn
      have hint' : (⟨x - p, hdir⟩ : A.direction) ∈
          interior (iso.toHomeomorph ⁻¹' (Subtype.val ⁻¹' B : Set A)) := hint
      rw [← iso.toHomeomorph.preimage_interior] at hint'
      exact mem_intrinsicInterior.mpr ⟨iso.toHomeomorph ⟨x - p, hdir⟩, hint', hfx⟩
  have hkey : μHE[Module.finrank ℝ A.direction] (f '' frontier u) = 0 := by
    rw [hf.euclideanHausdorffMeasure_image, InnerProductSpace.euclideanHausdorffMeasure_eq_volume,
      Convex.addHaar_frontier (volume : Measure A.direction) hu_convex]
  exact measure_mono_null hfrontier hkey

/-- The relative boundary of the projected base is null for `μHE[d - 1]`. -/
theorem projectedBase_diff_intrinsicInterior_null {d : ℕ} (P : ConvexPolytope d)
    {e : Euc d} (he : e ≠ 0) :
    μHE[d - 1] (P.projectedBase e he \ intrinsicInterior ℝ (P.projectedBase e he)) = 0 := by
  have hcl : IsClosed (P.projectedBase e he) := (P.isCompact_projectedBase he).isClosed
  have hconv : Convex ℝ (P.projectedBase e he) := by
    rw [P.projectedBase_eq_image he]
    exact P.convex.linear_image (hyperplaneProjection e).toLinearMap
  have hne := P.projectedBase_nonempty he
  have hle : Module.finrank ℝ (affineSpan ℝ (P.projectedBase e he)).direction ≤ d - 1 := by
    have hf0 : (innerSL ℝ e).toLinearMap ≠ 0 := by
      intro h
      have h2 : inner ℝ e e = 0 := by simpa using LinearMap.congr_fun h e
      exact (real_inner_self_pos.mpr he).ne' h2
    have hker := Module.Dual.finrank_ker_add_one_of_ne_zero hf0
    rw [finrank_euclideanSpace_fin] at hker
    have hsub : (affineSpan ℝ (P.projectedBase e he)).direction ≤
        LinearMap.ker (innerSL ℝ e).toLinearMap := by
      rw [direction_affineSpan, vectorSpan_def]
      apply Submodule.span_le.mpr
      rintro z ⟨x, hx, y, hy, rfl⟩
      have hx' : inner ℝ e x = 0 := hx.1
      have hy' : inner ℝ e y = 0 := hy.1
      simp [LinearMap.mem_ker, hx', hy', inner_sub_right]
    have hdim := Submodule.finrank_mono hsub
    omega
  rcases hle.lt_or_eq with hlt | heq
  · exact measure_mono_null Set.sdiff_subset
      (euclideanHausdorffMeasure_eq_zero_of_affineSpan_rank_lt
        (P.isCompact_projectedBase he) hconv hne hlt)
  · have h := euclideanHausdorffMeasure_diff_intrinsicInterior_eq_zero hcl hconv hne
    rw [heq] at h
    exact h

/-- Almost every fibre of a polytope over its projected base is nondegenerate. -/
theorem ae_lowerFiber_lt_upperFiber {d : ℕ} (P : ConvexPolytope d) {e : Euc d} (he : e ≠ 0) :
    ∀ᵐ y ∂(μHE[d - 1] : Measure (Euc d)), y ∈ P.projectedBase e he →
      P.lowerFiber e he y < P.upperFiber e he y := by
  rw [ae_iff]
  refine measure_mono_null ?_ (projectedBase_diff_intrinsicInterior_null P he)
  intro y hy
  obtain ⟨hyB, hnot⟩ := not_imp.mp hy
  exact ⟨hyB, fun hint => hnot (lowerFiber_lt_upperFiber_of_mem_intrinsicInterior P he hint)⟩

end SpherePackings
