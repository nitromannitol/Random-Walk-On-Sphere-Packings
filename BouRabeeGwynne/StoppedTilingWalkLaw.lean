module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/StoppedTilingWalkLaw.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.FiniteExit
public import BouRabeeGwynne.StoppedCurveMeasurable

@[expose] public section

/-!
# Construction of the stopped tiling-walk law

Finiteness of the closed graph region and structural boundary accessibility
suffice to construct the actual stopped-curve probability law. Enlarging the
region by the initial vertex handles an initial vertex outside the domain.
Deriving these structural hypotheses from the geometric assumptions is a
separate obligation in Theorem A.
-/

open scoped Classical unitInterval
open MeasureTheory

namespace BouRabeeGwynne

namespace FiniteConductanceNetwork

/-- Starting outside the interior gives the Dirac law on the constant curve. -/
theorem stoppedPolygonalCurve_map_eq_dirac_of_not_mem {d : ℕ} {V : Type*}
    [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (N : FiniteConductanceNetwork V) (pos : V → Euc d) (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (start : V) (hstart : start ∉ A) :
    (N.trajectoryLaw A hpos start).map (stoppedPolygonalCurve pos A) =
      Measure.dirac (CurveSpace.project (ContinuousMap.const unitInterval (pos start))) := by
  have heq : ∀ᵐ ω ∂N.trajectoryLaw A hpos start,
      stoppedPolygonalCurve pos A ω =
        CurveSpace.project (ContinuousMap.const unitInterval (pos start)) := by
    filter_upwards [N.trajectoryLaw_ae_start A hpos start] with ω hω
    have hout : ω 0 ∉ A := by simpa only [hω] using hstart
    have hzero := exitTime_eq_zero_of_not_mem hout
    simp [stoppedPolygonalCurve, hzero, hω]
  rw [Measure.map_congr heq, Measure.map_const, measure_univ, one_smul]

end FiniteConductanceNetwork

namespace OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d) (U : Set (Euc d))

/-- Enlarging a finite region preserves the accessible paths from its interior,
provided the entire closed graph region is retained. -/
theorem finiteNetwork_boundaryAccessible_of_closed [Fintype (T.closedVertices U)]
    (R : Set T.V) [Fintype R] (hR : T.closedVertices U ⊆ R)
    (haccess : (T.finiteNetwork (T.closedVertices U)).BoundaryAccessible
      (T.finiteInterior U)) :
    (T.finiteNetwork R).BoundaryAccessible {v : R | T.pos v.val ∈ U} := by
  let includeVertex : T.closedVertices U → R := fun v => ⟨v.val, hR v.property⟩
  intro v hv
  let vClosed : T.closedVertices U := ⟨v.val, Or.inl hv⟩
  obtain ⟨w, hw, hpath⟩ := haccess vClosed hv
  refine ⟨includeVertex w, hw, ?_⟩
  exact hpath.lift (p := fun v w : R => 0 < (T.finiteNetwork R).a v w)
    includeVertex (fun _ _ h => h)

/-- Construct a genuine stopped conductance-walk curve law, allowing the initial
vertex to lie outside `U`. The accessible network hypothesis is structural. -/
theorem exists_isStoppedTilingWalkLaw [Fintype (T.closedVertices U)]
    (haccess : (T.finiteNetwork (T.closedVertices U)).BoundaryAccessible
      (T.finiteInterior U)) (v₀ : T.V) :
    ∃ μ, IsStoppedTilingWalkLaw T U v₀ μ := by
  let R : Finset T.V := insert v₀ (Set.toFinite (T.closedVertices U)).toFinset
  have hR : (R : Set T.V) = T.closedVertices U ∪ {v₀} := by
    ext v
    simp [R, or_comm]
  have hsub : T.closedVertices U ⊆ (R : Set T.V) := by
    rw [hR]
    exact Set.subset_union_left
  letI : MeasurableSpace R := ⊤
  let A : Set R := {v | T.pos v.val ∈ U}
  let N := T.finiteNetwork (R : Set T.V)
  have haccessR : N.BoundaryAccessible A :=
    T.finiteNetwork_boundaryAccessible_of_closed U (R : Set T.V) hsub haccess
  let hpos := N.totalConductance_pos_of_boundaryAccessible A haccessR
  let start : R := ⟨v₀, by simp [R]⟩
  let law := N.trajectoryLaw A hpos start
  let curve := stoppedPolygonalCurve (fun v : R => T.pos v.val) A
  refine ⟨law.map curve, R, hR, hpos, start, rfl, ?_, ?_, ?_, rfl⟩
  · exact aemeasurable_stoppedPolygonalCurve _ _ _
  · exact N.trajectoryLaw_ae_finiteExit A hpos haccessR start
  · exact stoppedPolygonalCurve_map_isProbabilityMeasure _ _ _

/-- Version with explicit finiteness, suited to eventual collar/mesh bounds. -/
theorem exists_isStoppedTilingWalkLaw_of_finite
    (hfinite : (T.closedVertices U).Finite)
    (haccess : letI : Fintype (T.closedVertices U) := hfinite.fintype
      (T.finiteNetwork (T.closedVertices U)).BoundaryAccessible (T.finiteInterior U))
    (v₀ : T.V) : ∃ μ, IsStoppedTilingWalkLaw T U v₀ μ := by
  letI : Fintype (T.closedVertices U) := hfinite.fintype
  exact T.exists_isStoppedTilingWalkLaw U haccess v₀

/-- Every law satisfying the actual stopped-walk predicate is the constant-curve
Dirac law when its initial vertex is already outside the domain. -/
theorem isStoppedTilingWalkLaw_eq_dirac_of_not_mem {v₀ : T.V}
    {μ : Measure (CurveSpace d)} (hμ : IsStoppedTilingWalkLaw T U v₀ μ)
    (hv₀ : T.pos v₀ ∉ U) :
    μ = Measure.dirac (CurveSpace.project (ContinuousMap.const unitInterval (T.pos v₀))) := by
  obtain ⟨R, hR, h⟩ := hμ
  letI : MeasurableSpace R := ⊤
  obtain ⟨hpos, start, hstart, _, _, _, hmap⟩ := h
  have hout : start ∉ {v : R | T.pos v.val ∈ U} := by
    simpa only [Set.mem_setOf_eq, hstart] using hv₀
  rw [hmap]
  simpa only [hstart] using
    (T.finiteNetwork (R : Set T.V)).stoppedPolygonalCurve_map_eq_dirac_of_not_mem
      (fun v : R => T.pos v.val) {v : R | T.pos v.val ∈ U} hpos start hout

end OrthogonalTiling

end BouRabeeGwynne
