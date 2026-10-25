module

-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/Section4BallExitCouplingInputs.lean` at commit cf73d6e): the ball-exit
-- inputs of the coupling, for any nearest-neighbour walk under Assumption D, from Proposition 4.2.
public import SpherePackings.Support.Section4General.Prop42
public import BouRabeeGwynne.Section4BallExitCouplingInputs

@[expose] public section

/-!
# Ball-exit inputs of the coupling under Assumption D

For a ball in `B_δ(D)` and a compact set `K` inside it: a modulus `δ'` such that, eventually, the
exit law of the walk from any vertex in `K` is `ε`-close in the Lévy–Prokhorov metric to the
Brownian exit law from any point of `K` within `δ'` of it; and the same for the masses of finitely
many cells with Brownian-null boundaries.
-/

open MeasureTheory Metric Filter Set
open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork

namespace SpherePackings

variable {d : ℕ}

/-- The exit law of the walk from a vertex is close to the Brownian exit law from any nearby
point of a compact subset of the ball. -/
theorem eventually_ball_exit_nearby_levyProkhorov_error (hd : 1 ≤ d)
    (W : ℕ → NearestNeighbourWalk d) (near : ∀ n, Euc d → (W n).V) {D : Set (Euc d)} {δ : ℝ}
    (hAD : AssumptionD W near D δ) {c : Euc d} {r : ℝ} (hr : 0 < r)
    (hB : closedBall c r ⊆ cthickening δ D) {μ : Measure (BrownianPath d)}
    (hμ : IsStandardBrownianLaw μ) {K : Set (Euc d)} (hK : IsCompact K) (hKU : K ⊆ ball c r) :
    ∀ ε : ℝ, 0 < ε → ∃ δ' : ℝ, 0 < δ' ∧ ∀ᶠ n in atTop,
      ∀ v : (W n).V, (v : Euc d) ∈ K → ∀ y ∈ K, dist (v : Euc d) y ≤ δ' →
        levyProkhorovEDist ((W n).harmonicMeasure (ball c r) v)
          (brownianSpatialHarmonicMeasure (ball c r) isOpen_ball μ hμ y : Measure (Euc d)) ≤
          ENNReal.ofReal ε := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let ν : K → ProbabilityMeasure (Euc d) := fun x =>
    brownianSpatialHarmonicMeasure (ball c r) isOpen_ball μ hμ x
  have hν : Continuous ν :=
    (continuous_brownianBallHarmonicMeasure hd hμ c hr).comp
      (continuous_subtype_val.subtype_mk (fun x : K => hKU x.property))
  have hνLP : Continuous (fun x => LevyProkhorov.ofMeasure (ν x)) :=
    LevyProkhorov.continuous_ofMeasure_probabilityMeasure.comp hν
  intro ε hε
  obtain ⟨δ₁, hδ₁, hcontrol⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hνLP) (ε / 2) (half_pos hε)
  refine ⟨δ₁ / 2, half_pos hδ₁, ?_⟩
  filter_upwards [prop42_vertex hd W near hAD hr hB hμ (ε / 2) (half_pos hε)] with n hn
  intro v hvK y hy hdist
  have hnear : levyProkhorovEDist (ν ⟨(v : Euc d), hvK⟩ : Measure (Euc d))
      (ν ⟨y, hy⟩ : Measure (Euc d)) ≤ ENNReal.ofReal (ε / 2) := by
    have hdist' : dist (⟨(v : Euc d), hvK⟩ : K) ⟨y, hy⟩ < δ₁ :=
      hdist.trans_lt (half_lt_self hδ₁)
    have h := hcontrol hdist'
    rw [LevyProkhorov.dist_probabilityMeasure_def] at h
    rw [← ENNReal.ofReal_toReal (levyProkhorovEDist_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal h.le
  calc _ ≤ levyProkhorovEDist ((W n).harmonicMeasure (ball c r) v)
        (ν ⟨(v : Euc d), hvK⟩ : Measure (Euc d)) +
        levyProkhorovEDist (ν ⟨(v : Euc d), hvK⟩ : Measure (Euc d))
          (ν ⟨y, hy⟩ : Measure (Euc d)) := levyProkhorovEDist_triangle _ _ _
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
        add_le_add (hn v (hKU hvK)) hnear
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]

/-- On the event of exit, the harmonic measure has full mass. -/
lemma NearestNeighbourWalk.harmonicMeasure_univ_of_survival (W : NearestNeighbourWalk d)
    (S : Set (Euc d)) {a : W.V} (h : MarkovChain.survival W.kernel (W.inner S) a = 0) :
    W.harmonicMeasure S a univ = 1 := by
  rw [NearestNeighbourWalk.harmonicMeasure,
    Measure.map_apply (W.measurable_exitPosition S) MeasurableSet.univ, Set.preimage_univ,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  have hm := MarkovChain.measurableSet_exitTime_eq_top (W.measurableSet_inner S)
  have hc : {ω : ℕ → W.V | exitTime (W.inner S) ω ≠ ⊤} =
      {ω | exitTime (W.inner S) ω = ⊤}ᶜ := by
    ext ω
    simp
  rw [hc, prob_compl_eq_one_sub hm]
  rw [MarkovChain.survival, measureReal_eq_zero_iff] at h
  rw [h, tsub_zero]

/-- Under Assumption D the walk eventually exits every ball of `B_δ(D)` almost surely, from every
vertex of the ball and of its boundary. -/
theorem eventually_survival_eq_zero (W : ℕ → NearestNeighbourWalk d)
    (near : ∀ n, Euc d → (W n).V) {D : Set (Euc d)} {δ : ℝ} (hAD : AssumptionD W near D δ)
    {c : Euc d} {r : ℝ} (hr : 0 < r) (hB : closedBall c r ⊆ cthickening δ D) :
    ∀ᶠ n in atTop, ∀ a : (W n).V, a ∈ (W n).inner (ball c r) ∪ (W n).boundary (closedBall c r) →
      MarkovChain.survival (W n).kernel ((W n).inner (ball c r)) a = 0 := by
  have hBeq : closedBall c r ∩ cthickening δ D = closedBall c r := inter_eq_left.mpr hB
  have hcD : c ∈ cthickening δ D := hB (mem_closedBall_self hr.le)
  obtain ⟨-, -, hAD'⟩ := hAD
  obtain ⟨-, hdir⟩ := hAD' r hr c hcD
  rw [hBeq] at hdir
  have hconv := hdir (fun _ => 0)
    ⟨univ, isOpen_univ, subset_univ _, ⟨contDiffOn_const, fun x _ => by simp⟩⟩ 1 one_pos
  have hinner : ∀ n, (W n).inner (ball c r) = (W n).inner (closedBall c r) := by
    intro n
    ext v
    simp [NearestNeighbourWalk.inner, interior_closedBall c hr.ne', isOpen_ball.interior_eq]
  filter_upwards [hconv] with n hn a ha
  rw [hinner n] at ha ⊢
  rcases ha with ha | ha
  · exact MarkovChain.survival_eq_zero_of_forall_solution_bounded (W n).kernel
      ((W n).measurableSet_inner _) ((W n).disjoint_inner_boundary _) measurable_const le_rfl
      (fun _ => by simp) hn ha
  · exact MarkovChain.survival_of_not_mem (W n).kernel ((W n).measurableSet_inner _) ha.1

/-- Eventually, the discrete harmonic measure of a ball in `B_δ(D)` seen from any vertex of the
ball is a probability measure. -/
theorem eventually_harmonicMeasure_isProbability (W : ℕ → NearestNeighbourWalk d)
    (near : ∀ n, Euc d → (W n).V) {D : Set (Euc d)} {δ : ℝ} (hAD : AssumptionD W near D δ)
    {c : Euc d} {r : ℝ} (hr : 0 < r) (hB : closedBall c r ⊆ cthickening δ D) :
    ∀ᶠ n in atTop, ∀ a : (W n).V, (a : Euc d) ∈ ball c r →
      IsProbabilityMeasure ((W n).harmonicMeasure (ball c r) a) := by
  filter_upwards [eventually_survival_eq_zero W near hAD hr hB] with n hn a ha
  have hin : a ∈ (W n).inner (ball c r) := by
    change (a : Euc d) ∈ interior (ball c r)
    rw [isOpen_ball.interior_eq]
    exact ha
  exact ⟨(W n).harmonicMeasure_univ_of_survival (ball c r) (hn a (Or.inl hin))⟩

/-- For finitely many cells with Brownian-null frontiers, the discrete and Brownian exit masses
are uniformly close at nearby starting points of a compact subset of the ball. -/
theorem eventually_ball_exit_nearby_cell_error (hd : 1 ≤ d)
    (W : ℕ → NearestNeighbourWalk d) (near : ∀ n, Euc d → (W n).V) {D : Set (Euc d)} {δ : ℝ}
    (hAD : AssumptionD W near D δ) {c : Euc d} {r : ℝ} (hr : 0 < r)
    (hB : closedBall c r ⊆ cthickening δ D) {μ : Measure (BrownianPath d)}
    (hμ : IsStandardBrownianLaw μ) {K : Set (Euc d)} (hK : IsCompact K) (hKU : K ⊆ ball c r)
    {ι : Type*} [Fintype ι] (S : ι → Set (Euc d))
    (hnull : ∀ i, ∀ z ∈ K,
      (brownianSpatialHarmonicMeasure (ball c r) isOpen_ball μ hμ z : Measure (Euc d))
        (frontier (S i)) = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ δ' : ℝ, 0 < δ' ∧ ∀ᶠ n in atTop,
      ∀ v : (W n).V, (v : Euc d) ∈ K → ∀ y ∈ K, dist (v : Euc d) y ≤ δ' → ∀ i,
        |((W n).harmonicMeasure (ball c r) v (S i)).toReal -
          ((brownianSpatialHarmonicMeasure (ball c r) isOpen_ball μ hμ y : Measure (Euc d))
            (S i)).toReal| ≤ ε := by
  classical
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let Vn : ℕ → Type _ := fun n => {v : (W n).V // (v : Euc d) ∈ K}
  let p : ∀ n, Vn n → K := fun n v => ⟨(v.1 : Euc d), v.2⟩
  let ν : K → ProbabilityMeasure (Euc d) := fun x =>
    brownianSpatialHarmonicMeasure (ball c r) isOpen_ball μ hμ x
  have hν : Continuous ν :=
    (continuous_brownianBallHarmonicMeasure hd hμ c hr).comp
      (continuous_subtype_val.subtype_mk (fun x : K => hKU x.property))
  let μd : ∀ n, Vn n → ProbabilityMeasure (Euc d) := fun n v =>
    if h : IsProbabilityMeasure ((W n).harmonicMeasure (ball c r) v.1) then
      ⟨(W n).harmonicMeasure (ball c r) v.1, h⟩
    else ν (p n v)
  have hprob := eventually_harmonicMeasure_isProbability W near hAD hr hB
  have hLP : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ v : Vn n,
      levyProkhorovDist (μd n v : Measure (Euc d)) (ν (p n v) : Measure (Euc d)) < η := by
    intro η hη
    filter_upwards [hprob, prop42_vertex hd W near hAD hr hB hμ (η / 2) (half_pos hη)]
      with n hp hn
    intro v
    have hv := hp v.1 (hKU v.2)
    have hμd : (μd n v : Measure (Euc d)) = (W n).harmonicMeasure (ball c r) v.1 := by
      simp only [μd, hv, ↓reduceDIte]
      rfl
    rw [hμd, levyProkhorovDist]
    exact (ENNReal.toReal_le_of_le_ofReal (by positivity) (hn v.1 (hKU v.2))).trans_lt
      (half_lt_self hη)
  intro ε hε
  obtain ⟨δ', hδ', hcell⟩ :=
    uniform_nearby_cell_mass_error_of_uniform_levyProkhorov_error Vn p μd ν hν hLP S
      (fun i z => hnull i z z.property) ε hε
  refine ⟨δ', hδ', ?_⟩
  filter_upwards [hprob, hcell] with n hp hn
  intro v hvK y hy hdist i
  have hv := hp v (hKU hvK)
  have h := hn ⟨v, hvK⟩ ⟨y, hy⟩ hdist i
  have hμd : (μd n ⟨v, hvK⟩ : Measure (Euc d)) = (W n).harmonicMeasure (ball c r) v := by
    simp only [μd, hv, ↓reduceDIte]
    rfl
  rw [hμd] at h
  exact h

end SpherePackings
