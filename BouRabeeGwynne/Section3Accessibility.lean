-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/Section3Accessibility.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.Section3ColumnPaths
import BouRabeeGwynne.TilingNetwork
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

/-! Positive projected-base measure supplies actual positive-conductance boundary paths. -/

open scoped MeasureTheory ENNReal Classical
open MeasureTheory

namespace BouRabeeGwynne

lemma hyperplaneProjection_range {d : ℕ} {e : Euc d} (he : e ≠ 0) :
    LinearMap.range (hyperplaneProjection e).toLinearMap =
      LinearMap.ker (innerSL ℝ e).toLinearMap := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact inner_hyperplaneProjection he x
  · intro hy
    exact ⟨y, hyperplaneProjection_eq_self e hy⟩

namespace ConvexPolytope

variable {d : ℕ} (P : ConvexPolytope d)

theorem projectedBase_affine_rank {e : Euc d} (he : e ≠ 0) :
    Module.finrank ℝ (affineSpan ℝ (P.projectedBase e he)).direction = d - 1 := by
  have hspan : affineSpan ℝ P.carrier = ⊤ :=
    P.convex.interior_nonempty_iff_affineSpan_eq_top.mp P.interior_nonempty
  have hdir : (affineSpan ℝ (P.projectedBase e he)).direction =
      LinearMap.ker (innerSL ℝ e).toLinearMap := by
    rw [P.projectedBase_eq_image he]
    change (affineSpan ℝ ((hyperplaneProjection e).toLinearMap.toAffineMap ''
      P.carrier)).direction = _
    rw [← AffineSubspace.map_span, AffineSubspace.map_direction, hspan]
    simpa using hyperplaneProjection_range he
  have hfunctional : (innerSL ℝ e).toLinearMap ≠ 0 := by
    intro hzero
    have h := congrArg (fun f : Euc d →ₗ[ℝ] ℝ => f e) hzero
    change inner ℝ e e = 0 at h
    exact (real_inner_self_pos.mpr he).ne' h
  have hker := Module.Dual.finrank_ker_add_one_of_ne_zero hfunctional
  have hamb : Module.finrank ℝ (Euc d) = d := finrank_euclideanSpace_fin
  rw [hdir]
  omega

/-- Every full-dimensional cell meets a positive-measure family of columns.
This includes dimension one: the base then has dimension zero. -/
theorem projectedBase_measure_pos {e : Euc d} (he : e ≠ 0) :
    0 < μHE[d - 1] (P.projectedBase e he) := by
  have hconv : Convex ℝ (P.projectedBase e he) := by
    rw [P.projectedBase_eq_image he]
    exact P.convex.linear_image (hyperplaneProjection e).toLinearMap
  have h := (euclideanHausdorffMeasure_affineSpan_pos_lt_top
    (P.isCompact_projectedBase he) hconv (P.projectedBase_nonempty he)).1
  rwa [P.projectedBase_affine_rank he] at h

end ConvexPolytope

namespace OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

/-- Finite collar-contained regions have positive-conductance paths to their
external boundary. Accessibility is derived from actual cell geometry. -/
theorem finiteNetwork_boundaryAccessible_of_cell_interior
    (hd : 1 ≤ d) (e : Euc d) (he : e ≠ 0)
    (R : Set T.V) [Fintype R] (A : Set R)
    (hneighbors : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ R)
    (hcellD : ∀ v ∈ A, (T.cell v).carrier ⊆ interior T.domain) :
    (T.finiteNetwork R).BoundaryAccessible A := by
  intro v hv
  have hgood := T.toTilingData.ae_column_boundary_path hd e he R A hneighbors hcellD
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

end OrthogonalTiling
end BouRabeeGwynne
