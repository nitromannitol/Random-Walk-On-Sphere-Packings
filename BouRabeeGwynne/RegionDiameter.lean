-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/RegionDiameter.lean` at commit cf73d6e); unchanged apart from this header.
import BouRabeeGwynne.PaperObjects
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Order.Filter.Finite

/-! The actual maximum cell diameter of a finite current interior. -/

open scoped Classical Topology
open Filter

namespace BouRabeeGwynne

theorem ConvexPolytope.diam_pos {d : ℕ} (P : ConvexPolytope d) (hd : 1 ≤ d) :
    0 < Metric.diam P.carrier := by
  letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  obtain ⟨x, hx⟩ := P.interior_nonempty
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  have hle := Metric.diam_mono hball P.compact.isBounded
  rw [Metric.diam_ball_eq x hr.le] at hle
  linarith

namespace TilingData

variable {d : ℕ} (T : TilingData d)

noncomputable def regionDiameterNN (R : Set T.V) [Fintype R] (A : Set R) : NNReal :=
  Finset.univ.sup fun v : R =>
    if v ∈ A then ⟨Metric.diam (T.cell v).carrier, Metric.diam_nonneg⟩ else 0

noncomputable def regionDiameter (R : Set T.V) [Fintype R] (A : Set R) : ℝ :=
  T.regionDiameterNN R A

lemma regionDiameter_nonneg (R : Set T.V) [Fintype R] (A : Set R) :
    0 ≤ T.regionDiameter R A := NNReal.coe_nonneg _

lemma cell_diam_le_regionDiameter (R : Set T.V) [Fintype R] (A : Set R)
    {v : R} (hv : v ∈ A) :
    Metric.diam (T.cell v).carrier ≤ T.regionDiameter R A := by
  have h := Finset.le_sup (s := (Finset.univ : Finset R))
    (f := fun u : R => if u ∈ A then
      (⟨Metric.diam (T.cell u).carrier, Metric.diam_nonneg⟩ : NNReal) else 0)
    (Finset.mem_univ v)
  rw [if_pos hv] at h
  exact_mod_cast h

lemma regionDiameter_le (R : Set T.V) [Fintype R] (A : Set R)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hdiam : ∀ v ∈ A, Metric.diam (T.cell v).carrier ≤ δ) :
    T.regionDiameter R A ≤ δ := by
  have h : T.regionDiameterNN R A ≤ (⟨δ, hδ⟩ : NNReal) := by
    apply Finset.sup_le
    intro v _
    change (if v ∈ A then (⟨Metric.diam (T.cell v).carrier, Metric.diam_nonneg⟩ : NNReal)
      else 0) ≤ ⟨δ, hδ⟩
    split_ifs with hv
    · exact hdiam v hv
    · exact bot_le
  exact_mod_cast h

@[simp] lemma regionDiameter_empty (R : Set T.V) [Fintype R] :
    T.regionDiameter R ∅ = 0 := by
  apply le_antisymm (T.regionDiameter_le R ∅ le_rfl (by simp))
  exact T.regionDiameter_nonneg R ∅

lemma regionDiameter_mono (R : Set T.V) [Fintype R] {A B : Set R} (hAB : A ⊆ B) :
    T.regionDiameter R A ≤ T.regionDiameter R B :=
  T.regionDiameter_le R A (T.regionDiameter_nonneg R B)
    (fun _ hv => T.cell_diam_le_regionDiameter R B (hAB hv))

lemma regionDiameter_pos (hd : 1 ≤ d) (R : Set T.V) [Fintype R]
    {A : Set R} (hA : A.Nonempty) : 0 < T.regionDiameter R A := by
  obtain ⟨v, hv⟩ := hA
  exact ((T.cell v).diam_pos hd).trans_le (T.cell_diam_le_regionDiameter R A hv)

/-- In a fixed finite network, shrinking actual diameters force the current
interior to become empty. No bound on the number of iterations is needed. -/
theorem eventually_empty_of_regionDiameter_tendsto_zero
    (hd : 1 ≤ d) (R : Set T.V) [Fintype R] (A : ℕ → Set R)
    (hlim : Tendsto (fun n => T.regionDiameter R (A n)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, A n = ∅ := by
  have hv : ∀ v : R, ∀ᶠ n in atTop, v ∉ A n := by
    intro v
    filter_upwards [hlim.eventually_lt_const ((T.cell v).diam_pos hd)] with n hn
    exact fun hmem => (not_lt_of_ge (T.cell_diam_le_regionDiameter R (A n) hmem)) hn
  filter_upwards [eventually_all.mpr hv] with n hn
  exact Set.eq_empty_of_forall_notMem hn

end TilingData
end BouRabeeGwynne
