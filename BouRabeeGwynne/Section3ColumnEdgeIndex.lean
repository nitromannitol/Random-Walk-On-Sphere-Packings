module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/Section3ColumnEdgeIndex.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.Section3ColumnPaths
public import BouRabeeGwynne.Section3ColumnEnergy

@[expose] public section

/-! Each actual interior-incident edge is counted exactly once. -/

open scoped Classical BigOperators MeasureTheory ENNReal
open MeasureTheory

namespace BouRabeeGwynne.TilingData

variable {d : ℕ} (T : TilingData d)

noncomputable def contactGraph (R : Set T.V) (A : Set R) : SimpleGraph R where
  Adj v w := T.adj v w ∧ (v ∈ A ∨ w ∈ A)
  symm := ⟨fun v w h => ⟨T.adj_symm h.1, h.2.symm⟩⟩
  loopless := ⟨fun v h => h.1.1 rfl⟩

def edgeFacet (R : Set T.V) (a : Sym2 R) : Set (Euc d) :=
  Sym2.lift ⟨fun v w : R => T.facet v w, fun v w => T.facet_symm v w⟩ a

@[simp] lemma edgeFacet_mk (R : Set T.V) (v w : R) :
    T.edgeFacet R s(v, w) = T.facet v w := rfl

lemma edgeFacet_out (R : Set T.V) (a : Sym2 R) :
    T.edgeFacet R a = T.facet a.out.1 a.out.2 := by
  have hout : s(a.out.1, a.out.2) = a := Quot.out_eq a
  exact (congrArg (T.edgeFacet R) hout).symm

noncomputable def orientedContactPair (R : Set T.V) (a : Sym2 R) : T.V × T.V :=
  (a.out.1.val, a.out.2.val)

lemma orientedContactPair_injective (R : Set T.V) :
    Function.Injective (T.orientedContactPair R) := by
  intro a b hab
  have h₁ : (a.out.1 : T.V) = b.out.1 := congrArg Prod.fst hab
  have h₂ : (a.out.2 : T.V) = b.out.2 := congrArg Prod.snd hab
  have hout : a.out = b.out := Prod.ext (Subtype.ext h₁) (Subtype.ext h₂)
  simpa only [Quot.out_eq] using congrArg (Quot.mk (Sym2.Rel R)) hout

noncomputable def orientedInteriorEdges (R : Set T.V) [Fintype R]
    (A : Set R) : Finset (T.V × T.V) :=
  (T.contactGraph R A).edgeFinset.image (T.orientedContactPair R)

lemma orientedInteriorEdges_adj (R : Set T.V) [Fintype R] (A : Set R)
    (p : T.V × T.V) (hp : p ∈ T.orientedInteriorEdges R A) : T.adj p.1 p.2 := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
  have hout : s(a.out.1, a.out.2) ∈ (T.contactGraph R A).edgeFinset := by
    rw [show s(a.out.1, a.out.2) = a from Quot.out_eq a]
    exact ha
  exact (((T.contactGraph R A).mem_edgeSet).mp (SimpleGraph.mem_edgeFinset.mp hout)).1

lemma sum_orientedInteriorEdges (R : Set T.V) [Fintype R] (A : Set R)
    (F : T.V × T.V → ℝ) :
    (∑ p ∈ T.orientedInteriorEdges R A, F p) =
      ∑ a ∈ (T.contactGraph R A).edgeFinset, F (T.orientedContactPair R a) := by
  rw [orientedInteriorEdges, Finset.sum_image]
  exact fun a _ b _ hab => T.orientedContactPair_injective R hab

lemma columnGraph_edgeFinset (R : Set T.V) [Fintype R] (A : Set R)
    (e y : Euc d) :
    (T.columnGraph R A e y).edgeFinset = (T.contactGraph R A).edgeFinset.filter
      (fun a => y ∈ hyperplaneProjection e '' T.edgeFacet R a) := by
  ext a
  induction a using Sym2.inductionOn with
  | hf v w =>
    rw [Finset.mem_filter, T.edgeFacet_mk]
    constructor
    · intro h
      have hadj := ((T.columnGraph R A e y).mem_edgeSet).mp
        (SimpleGraph.mem_edgeFinset.mp h)
      exact ⟨SimpleGraph.mem_edgeFinset.mpr
        (((T.contactGraph R A).mem_edgeSet).mpr ⟨hadj.1, hadj.2.1⟩), hadj.2.2⟩
    · rintro ⟨h, hproj⟩
      have hadj := ((T.contactGraph R A).mem_edgeSet).mp
        (SimpleGraph.mem_edgeFinset.mp h)
      exact SimpleGraph.mem_edgeFinset.mpr
        (((T.columnGraph R A e y).mem_edgeSet).mpr ⟨hadj.1, hadj.2, hproj⟩)

end BouRabeeGwynne.TilingData

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

lemma column_graph_variation_eq (R : Set T.V) [Fintype R] (A : Set R)
    (e y : Euc d) (f : T.V → ℝ) :
    (∑ a ∈ (T.toTilingData.columnGraph R A e y).edgeFinset,
      unorderedEdgeVariation (fun v : R => f v) a) =
      T.columnVariation e (T.toTilingData.orientedInteriorEdges R A) f y := by
  rw [T.toTilingData.columnGraph_edgeFinset, Finset.sum_filter, columnVariation,
    T.toTilingData.sum_orientedInteriorEdges]
  apply Finset.sum_congr rfl
  intro a _
  have hout : s(a.out.1, a.out.2) = a := Quot.out_eq a
  have hvar := congrArg (unorderedEdgeVariation (fun v : R => f v)) hout
  rw [← hvar, unorderedEdgeVariation_mk, T.toTilingData.edgeFacet_out]
  simp only [Set.indicator_apply, TilingData.orientedContactPair, abs_sub_comm]

end BouRabeeGwynne.OrthogonalTiling
