module

-- Built on Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne (commit cf73d6e).
public import SpherePackings.General.MarkovChain.Dirichlet

@[expose] public section

/-!
# Nearest-neighbour walks on graphs in `ℝ^d`

A graph with vertex set `V ⊆ ℝ^d` and a nearest-neighbour random walk on it: a Markov kernel on
the vertices whose steps follow the edges.  For a set `S`, `inner S` is the set of vertices in the
interior of `S` and `boundary S` the set of the other vertices adjacent to one of them;
`harmonicMeasure S a` is the law of the position of the walk started at `a` at its first exit from
`inner S`, on the event of exit.  Nothing here depends on the paper.
-/

open MeasureTheory ProbabilityTheory Set
open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork

namespace SpherePackings

/-- A graph with vertex set in `ℝ^d`, with a nearest-neighbour random walk on it. -/
structure NearestNeighbourWalk (d : ℕ) where
  /-- The vertex set. -/
  V : Set (Euc d)
  /-- The (undirected) edge relation. -/
  adj : V → V → Prop
  adj_symm : ∀ a b, adj a b → adj b a
  /-- The transition kernel of the walk. -/
  kernel : Kernel V V
  isMarkovKernel : IsMarkovKernel kernel
  /-- Every step follows an edge. -/
  ae_adj : ∀ a, ∀ᵐ b ∂kernel a, adj a b

namespace NearestNeighbourWalk

variable {d : ℕ} (W : NearestNeighbourWalk d)

instance : IsMarkovKernel W.kernel := W.isMarkovKernel

/-- `V[S]`: the vertices in the interior of `S`. -/
def inner (S : Set (Euc d)) : Set W.V := {v | (v : Euc d) ∈ interior S}

/-- `∂V[S]`: the vertices outside `V[S]` adjacent to a vertex of `V[S]`. -/
def boundary (S : Set (Euc d)) : Set W.V := {w | w ∉ W.inner S ∧ ∃ v ∈ W.inner S, W.adj v w}

lemma measurableSet_inner (S : Set (Euc d)) : MeasurableSet (W.inner S) :=
  measurable_subtype_coe isOpen_interior.measurableSet

lemma disjoint_inner_boundary (S : Set (Euc d)) : Disjoint (W.inner S) (W.boundary S) :=
  Set.disjoint_right.mpr fun _ hw => hw.1

lemma inner_of_isOpen {S : Set (Euc d)} (hS : IsOpen S) :
    W.inner S = ({v : W.V | (v : Euc d) ∈ S} : Set W.V) := by
  simp [inner, hS.interior_eq]

/-- The discrete harmonic measure of `S` seen from `a`. -/
noncomputable def harmonicMeasure (S : Set (Euc d)) (a : W.V) : Measure (Euc d) :=
  ((MarkovChain.law W.kernel a).restrict {ω | exitTime (W.inner S) ω ≠ ⊤}).map
    (fun ω => (exitVertex (W.inner S) ω).1)

instance (S : Set (Euc d)) (a : W.V) : IsFiniteMeasure (W.harmonicMeasure S a) := by
  unfold harmonicMeasure
  infer_instance

lemma measurable_exitPosition (S : Set (Euc d)) :
    Measurable (fun ω : ℕ → W.V => (exitVertex (W.inner S) ω).1) :=
  measurable_subtype_coe.comp (MarkovChain.measurable_exitVertex' (W.measurableSet_inner S))

lemma harmonicMeasure_univ_le_one (S : Set (Euc d)) (a : W.V) :
    W.harmonicMeasure S a univ ≤ 1 := by
  rw [harmonicMeasure, Measure.map_apply (W.measurable_exitPosition S) MeasurableSet.univ,
    Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  exact prob_le_one

/-- The harmonic measure is carried by the complement of `V[S]`. -/
lemma harmonicMeasure_inner_null (S : Set (Euc d)) (a : W.V) :
    W.harmonicMeasure S a (interior S) = 0 := by
  rw [harmonicMeasure, Measure.map_apply (W.measurable_exitPosition S)
    isOpen_interior.measurableSet, Measure.restrict_apply
    ((W.measurable_exitPosition S) isOpen_interior.measurableSet)]
  convert measure_empty (μ := MarkovChain.law W.kernel a)
  ext ω
  simp only [mem_inter_iff, mem_preimage, mem_empty_iff_false, iff_false, not_and]
  intro h hτ
  exact MarkovChain.exitVertex_not_mem' hτ h

/-- Integrals against the harmonic measure are exit values. -/
lemma integral_harmonicMeasure (S : Set (Euc d)) (a : W.V) {f : Euc d → ℝ} (hf : Measurable f) :
    ∫ x, f x ∂W.harmonicMeasure S a =
      MarkovChain.exitValue W.kernel (W.inner S) (fun v => f v) a := by
  rw [harmonicMeasure, integral_map (W.measurable_exitPosition S).aemeasurable
    hf.aestronglyMeasurable, MarkovChain.exitValue,
    ← integral_indicator (MarkovChain.measurableSet_exitTime_ne_top (W.measurableSet_inner S))]
  congr 1
  funext ω
  by_cases hτ : exitTime (W.inner S) ω = ⊤
  · simp [MarkovChain.exitPayoff, hτ]
  · simp [MarkovChain.exitPayoff, hτ]

/-- `near` selects a nearest vertex to every point. -/
def IsNearestVertex (near : Euc d → W.V) : Prop :=
  ∀ z (v : W.V), dist (near z : Euc d) z ≤ dist (v : Euc d) z

/-- If every point has a nearest vertex, the vertex set is closed: a point of its closure is at
distance `0` from its nearest vertex. -/
lemma isClosed_of_isNearestVertex {near : Euc d → W.V} (h : W.IsNearestVertex near) :
    IsClosed W.V := by
  refine closure_subset_iff_isClosed.mp fun x hx => ?_
  have hne : W.V.Nonempty := ⟨near x, (near x).property⟩
  have h0 : Metric.infDist x W.V = 0 := Metric.infDist_zero_of_mem_closure hx
  have hle : dist ((near x : W.V) : Euc d) x ≤ Metric.infDist x W.V := by
    apply Metric.le_infDist hne |>.mpr
    intro w hw
    rw [dist_comm x w]
    exact h x ⟨w, hw⟩
  have hx' : ((near x : W.V) : Euc d) = x := dist_le_zero.mp (h0 ▸ hle)
  exact hx' ▸ (near x).property

lemma measurableEmbedding_val_of_isNearestVertex {near : Euc d → W.V}
    (h : W.IsNearestVertex near) : MeasurableEmbedding (Subtype.val : W.V → Euc d) :=
  MeasurableEmbedding.subtype_coe (W.isClosed_of_isNearestVertex h).measurableSet

end NearestNeighbourWalk

end SpherePackings
