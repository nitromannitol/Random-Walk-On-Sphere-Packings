-- Built on Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne (commit cf73d6e).
import SpherePackings.General.NearestNeighbourWalk
import BouRabeeGwynne.DiscretePDE

/-!
# The conductance walk of a tiling as a nearest-neighbour walk

For an orthogonal tiling with countably many vertices, the conductance-weighted random walk of
`rw-spheres.tex:233-236`, as a `NearestNeighbourWalk` on the set of vertex positions: from a vertex
with finitely many neighbours and positive total conductance it steps to a neighbour `w` with
probability `a(v, w) / a(v)`; any other vertex is absorbing (it never occurs in the applications,
and it keeps the kernel Markov without a separate argument).  A function that is harmonic for this
walk at a vertex has zero discrete Laplacian there, and the walk's `V[S]` and `∂V[S]` are the
tiling's interior and boundary vertices of `interior S`.
-/

open MeasureTheory ProbabilityTheory Set
open BouRabeeGwynne BouRabeeGwynne.OrthogonalTiling
open scoped ENNReal

namespace SpherePackings

variable {d : ℕ} (T : OrthogonalTiling d)

/-- The vertex positions of a tiling. -/
def tilingPoints : Set (Euc d) := range T.pos

/-- Vertices and their positions. -/
noncomputable def tilingEquiv : T.V ≃ (tilingPoints T) := Equiv.ofInjective T.pos T.pos_injective

@[simp] lemma tilingEquiv_coe (v : T.V) : (((tilingEquiv T) v : (tilingPoints T)) : Euc d) = T.pos v :=
  rfl

/-- Total conductance at a vertex with finitely many neighbours (`0` otherwise). -/
noncomputable def walkWeight (a : T.V) : ℝ := by
  classical
  exact if h : (T.neighbors a).Finite then ∑ w ∈ T.neighborFinset a h, T.conductanceReal a w else 0

/-- The walk moves from `a` when `a` has finitely many neighbours and positive total conductance. -/
def WalkActive (a : T.V) : Prop := (T.neighbors a).Finite ∧ 0 < (walkWeight T) a

/-- One step of the conductance walk from `a`. -/
noncomputable def stepMeasure (a : T.V) : Measure (tilingPoints T) := by
  classical
  exact if h : (WalkActive T) a then
    ∑ w ∈ T.neighborFinset a h.1,
      ENNReal.ofReal (T.conductanceReal a w / (walkWeight T) a) • Measure.dirac ((tilingEquiv T) w)
  else Measure.dirac ((tilingEquiv T) a)

lemma walkWeight_of_finite {a : T.V} (h : (T.neighbors a).Finite) :
    (walkWeight T) a = ∑ w ∈ T.neighborFinset a h, T.conductanceReal a w := by
  classical
  simp only [walkWeight, h, dite_true]

private lemma stepMeasure_of_walkActive {a : T.V} (h : (WalkActive T) a) :
    (stepMeasure T) a = ∑ w ∈ T.neighborFinset a h.1,
      ENNReal.ofReal (T.conductanceReal a w / (walkWeight T) a) • Measure.dirac ((tilingEquiv T) w) := by
  unfold stepMeasure
  simp only [h, ↓reduceDIte]

private lemma stepMeasure_of_not_walkActive {a : T.V} (h : ¬ (WalkActive T) a) :
    (stepMeasure T) a = Measure.dirac ((tilingEquiv T) a) := by
  unfold stepMeasure
  simp only [h, ↓reduceDIte]

lemma stepMeasure_isProbabilityMeasure (a : T.V) : IsProbabilityMeasure ((stepMeasure T) a) := by
  by_cases h : (WalkActive T) a
  · have hW : 0 < (walkWeight T) a := h.2
    have hnn : ∀ w ∈ T.neighborFinset a h.1, 0 ≤ T.conductanceReal a w / (walkWeight T) a :=
      fun w _ => div_nonneg (T.conductanceReal_nonneg a w) hW.le
    rw [stepMeasure_of_walkActive T h]
    refine ⟨?_⟩
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg hnn, ← Finset.sum_div, ← walkWeight_of_finite T h.1,
      div_self hW.ne', ENNReal.ofReal_one]
  · rw [stepMeasure_of_not_walkActive T h]
    infer_instance

instance [Countable T.V] : Countable (tilingPoints T) := (tilingEquiv T).symm.injective.countable

private lemma measurableSet_tilingPoints [Countable T.V] (s : Set (tilingPoints T)) :
    MeasurableSet s :=
  s.to_countable.measurableSet

/-- Every step from a vertex `x` of the walk follows an edge (or stays put at an absorbing `x`). -/
private lemma ae_stepMeasure [Countable T.V] (x : tilingPoints T) :
    ∀ᵐ b ∂(stepMeasure T) ((tilingEquiv T).symm x),
      T.adj ((tilingEquiv T).symm x) ((tilingEquiv T).symm b) ∨
        (x = b ∧ ¬ (WalkActive T) ((tilingEquiv T).symm x)) := by
  obtain ⟨a, rfl⟩ := (tilingEquiv T).surjective x
  rw [Equiv.symm_apply_apply]
  by_cases h : (WalkActive T) a
  · rw [stepMeasure_of_walkActive T h, ae_iff]
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
    refine Finset.sum_eq_zero fun w hw => ?_
    have hadj : T.adj a w := (T.mem_neighborFinset h.1).1 hw
    rw [Measure.dirac_apply' _ (measurableSet_tilingPoints T _), Set.indicator_of_notMem, mul_zero]
    intro hnot
    exact hnot (Or.inl (by rw [Equiv.symm_apply_apply]; exact hadj))
  · rw [stepMeasure_of_not_walkActive T h, ae_dirac_iff (measurableSet_tilingPoints T _)]
    exact Or.inr ⟨rfl, h⟩

/-- **The conductance walk** of a tiling with countably many vertices. -/
noncomputable def conductanceWalk [Countable T.V] : NearestNeighbourWalk d where
  V := (tilingPoints T)
  adj x y := T.adj ((tilingEquiv T).symm x) ((tilingEquiv T).symm y) ∨
    (x = y ∧ ¬ (WalkActive T) ((tilingEquiv T).symm x))
  adj_symm x y h := by
    rcases h with h | ⟨rfl, h⟩
    · exact Or.inl (T.toTilingData.adj_symm h)
    · exact Or.inr ⟨rfl, h⟩
  kernel := Kernel.ofFunOfCountable fun x => (stepMeasure T) ((tilingEquiv T).symm x)
  isMarkovKernel := ⟨fun x => (stepMeasure_isProbabilityMeasure T) _⟩
  ae_adj := fun x => ae_stepMeasure T x

lemma conductanceWalk_kernel_apply [Countable T.V] (a : T.V) :
    (conductanceWalk T).kernel ((tilingEquiv T) a) = (stepMeasure T) a := by
  change (stepMeasure T) ((tilingEquiv T).symm ((tilingEquiv T) a)) = _
  rw [Equiv.symm_apply_apply]

/-- **Harmonicity bridge.**  A function harmonic for the conductance walk at a vertex with finitely
many neighbours has zero discrete Laplacian there. -/
theorem discreteLaplacian_eq_zero_of_isHarmonicAt [Countable T.V] {f : (tilingPoints T) → ℝ}
    {a : T.V} (hv : (T.neighbors a).Finite)
    (hf : MarkovChain.IsHarmonicAt (conductanceWalk T).kernel f ((tilingEquiv T) a)) :
    T.discreteLaplacian (fun w => f ((tilingEquiv T) w)) a hv = 0 := by
  obtain ⟨hint, hmean⟩ := hf
  have hint' : Integrable f ((stepMeasure T) a) := by
    rw [← conductanceWalk_kernel_apply]; exact hint
  have hmean' : ∫ b, f b ∂(stepMeasure T) a = f ((tilingEquiv T) a) := by
    rw [← conductanceWalk_kernel_apply]; exact hmean
  clear hint hmean
  unfold discreteLaplacian
  show ∑ w ∈ T.neighborFinset a hv,
    T.conductanceReal a w * (f ((tilingEquiv T) w) - f ((tilingEquiv T) a)) = 0
  by_cases h : (WalkActive T) a
  · have hW : 0 < (walkWeight T) a := h.2
    have hWne : (walkWeight T) a ≠ 0 := hW.ne'
    rw [stepMeasure_of_walkActive T h] at hint' hmean'
    have hterm : ∀ w ∈ T.neighborFinset a hv,
        ∫ b, f b ∂(ENNReal.ofReal (T.conductanceReal a w / (walkWeight T) a) •
          Measure.dirac ((tilingEquiv T) w))
          = T.conductanceReal a w / (walkWeight T) a * f ((tilingEquiv T) w) := by
      intro w _
      rw [integral_smul_measure, integral_dirac,
        ENNReal.toReal_ofReal (div_nonneg (T.conductanceReal_nonneg a w) hW.le), smul_eq_mul]
    rw [integral_finsetSum_measure (integrable_finsetSum_measure.1 hint'),
      Finset.sum_congr rfl hterm] at hmean'
    have h1 : ∑ w ∈ T.neighborFinset a hv, T.conductanceReal a w * f ((tilingEquiv T) w)
        = (walkWeight T) a * f ((tilingEquiv T) a) := by
      rw [← hmean', Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      field_simp
    have h2 : (walkWeight T) a = ∑ w ∈ T.neighborFinset a hv, T.conductanceReal a w :=
      walkWeight_of_finite T hv
    have key : ∑ w ∈ T.neighborFinset a hv,
        T.conductanceReal a w * (f ((tilingEquiv T) w) - f ((tilingEquiv T) a))
        = ∑ w ∈ T.neighborFinset a hv, T.conductanceReal a w * f ((tilingEquiv T) w)
          - (∑ w ∈ T.neighborFinset a hv, T.conductanceReal a w) * f ((tilingEquiv T) a) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun w _ => mul_sub _ _ _
    rw [key, h1, ← h2, sub_self]
  · refine Finset.sum_eq_zero fun w hw => ?_
    exfalso
    have hadj : T.adj a w := (T.mem_neighborFinset hv).1 hw
    have hnn : ∀ v ∈ T.neighborFinset a hv, 0 ≤ T.conductanceReal a v :=
      fun v _ => T.conductanceReal_nonneg a v
    have hsum : ∑ v ∈ T.neighborFinset a hv, T.conductanceReal a v ≤ 0 := by
      rw [← walkWeight_of_finite T hv]
      exact not_lt.1 fun hpos => h ⟨hv, hpos⟩
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).1
      (le_antisymm hsum (Finset.sum_nonneg hnn)) w hw
    exact (T.conductanceReal_pos_iff.2 hadj).ne' hzero

/-- The walk's vertex set `V[S]` is the set of tiling vertices in `interior S`. -/
lemma conductanceWalk_inner [Countable T.V] (S : Set (Euc d)) (a : T.V) :
    (tilingEquiv T) a ∈ (conductanceWalk T).inner S ↔ a ∈ T.interiorVertices (interior S) :=
  Iff.rfl

/-- The walk's `∂V[S]` is the set of tiling boundary vertices of `interior S`. -/
lemma conductanceWalk_boundary [Countable T.V] (S : Set (Euc d)) (a : T.V) :
    (tilingEquiv T) a ∈ (conductanceWalk T).boundary S ↔ a ∈ T.boundaryVertices (interior S) := by
  rw [T.mem_boundaryVertices_iff]
  constructor
  · rintro ⟨hout, v, hv, hadj⟩
    rcases hadj with h | ⟨rfl, -⟩
    · rw [Equiv.symm_apply_apply] at h
      have hpos : T.pos ((tilingEquiv T).symm v) = (v : Euc d) :=
        (tilingEquiv_coe T _).symm.trans (congrArg Subtype.val ((tilingEquiv T).apply_symm_apply v))
      exact ⟨hout, (tilingEquiv T).symm v, by rw [hpos]; exact hv, h⟩
    · exact (hout hv).elim
  · rintro ⟨hout, b, hb, hadj⟩
    refine ⟨hout, (tilingEquiv T) b, hb, Or.inl ?_⟩
    show T.adj ((tilingEquiv T).symm ((tilingEquiv T) b)) ((tilingEquiv T).symm ((tilingEquiv T) a))
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact hadj

end SpherePackings
