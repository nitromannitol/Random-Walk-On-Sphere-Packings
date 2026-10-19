-- Adapted in part from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (commit cf73d6e): it uses its `exitTime` and `exitVertex`, and `exitVertex_not_mem'` is its
-- `exitVertex_not_mem` (file `BouRabeeGwynne/DiscreteHarmonicMeasure.lean`) for any state space.
import SpherePackings.General.MarkovChain.Basic

/-!
# Exit values and the Dirichlet problem for a Markov kernel

For a Markov kernel `κ` on `V` and a measurable set `A`, the chain started at `a` exits `A` at
`exitTime A` (`⊤` if it never does) at the state `exitVertex A`.  For a bounded measurable `g`,
`exitValue κ A g a` is the expectation of `g` at the exit state on the event of exit.  This file
proves the first-step identities, that `exitValue κ A g` solves the Dirichlet problem with data
`g`, and that uniqueness of the solution of a Dirichlet problem forces the chain to exit almost
surely.  Nothing here depends on the paper.
-/

open MeasureTheory ProbabilityTheory Set Preorder
open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork

namespace SpherePackings.MarkovChain

section Paths

variable {V : Type*} {A : Set V}

/-- A path started inside `A` exits at all iff it exits after its first step. -/
lemma exitTime_eq_top_iff_walkShift_one {ω : ℕ → V} (h0 : ω 0 ∈ A) :
    exitTime A ω = ⊤ ↔ exitTime A (walkShift 1 ω) = ⊤ := by
  rw [exitTime_eq_top_iff, exitTime_eq_top_iff]
  constructor
  · intro h n
    simpa [walkShift, Nat.add_comm] using h (n + 1)
  · intro h n
    cases n with
    | zero => exact h0
    | succ n => simpa [walkShift, Nat.add_comm] using h n

/-- A path started inside `A` exits at the same state as its shift after the first step. -/
lemma exitVertex_walkShift_one {ω : ℕ → V} (h0 : ω 0 ∈ A) (hτ : exitTime A ω ≠ ⊤) :
    exitVertex A (walkShift 1 ω) = exitVertex A ω := by
  obtain ⟨τ, hτ'⟩ := WithTop.ne_top_iff_exists.mp hτ
  have h1 : 1 ≤ τ := by
    by_contra h
    have hτ0 : τ = 0 := by omega
    have hle : exitTime A ω ≤ ((0 : ℕ) : WithTop ℕ) := by rw [← hτ', hτ0]; exact le_rfl
    obtain ⟨k, hk, hk'⟩ := (exitTime_le_iff A ω 0).mp hle
    have : k = 0 := by omega
    exact hk' (this ▸ h0)
  exact exitVertex_walkShift_of_eq A ω hτ'.symm h1

lemma exitVertex_not_mem' {ω : ℕ → V} (hτ : exitTime A ω ≠ ⊤) : exitVertex A ω ∉ A := by
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hτ
  have h := exitTime_mem_compl_of_ne_top hτ
  rw [← hm] at h
  rw [exitVertex, ← hm]
  exact h

lemma exitVertex_of_not_mem {ω : ℕ → V} (h0 : ω 0 ∉ A) : exitVertex A ω = ω 0 := by
  simp [exitVertex, exitTime_eq_zero_of_not_mem h0]

/-- The payoff `g` at the exit state, on the event that the path exits. -/
noncomputable def exitPayoff (A : Set V) (g : V → ℝ) (ω : ℕ → V) : ℝ :=
  open Classical in if exitTime A ω = ⊤ then 0 else g (exitVertex A ω)

lemma abs_exitPayoff_le {g : V → ℝ} {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ v, |g v| ≤ C) (ω : ℕ → V) :
    |exitPayoff A g ω| ≤ C := by
  unfold exitPayoff
  split_ifs
  · simpa using hC0
  · exact hC _

lemma exitPayoff_walkShift_one {g : V → ℝ} {ω : ℕ → V} (h0 : ω 0 ∈ A) :
    exitPayoff A g (walkShift 1 ω) = exitPayoff A g ω := by
  unfold exitPayoff
  by_cases hτ : exitTime A ω = ⊤
  · simp only [hτ, (exitTime_eq_top_iff_walkShift_one h0).mp hτ, ↓reduceIte]
  · have hτ1 : exitTime A (walkShift 1 ω) ≠ ⊤ :=
      fun h => hτ ((exitTime_eq_top_iff_walkShift_one h0).mpr h)
    simp only [hτ, hτ1, ↓reduceIte, exitVertex_walkShift_one h0 hτ]

end Paths

variable {V : Type*} [MeasurableSpace V] (κ : Kernel V V) [IsMarkovKernel κ]

/-! ### The start of the chain -/

lemma law_map_eval_zero (a : V) : (law κ a).map (fun ω => ω 0) = Measure.dirac a := by
  have heq : (fun ω : ℕ → V => ω 0) =
      (fun h : Finset.Iic 0 → V => h ⟨0, Finset.mem_Iic.mpr le_rfl⟩) ∘ frestrictLe 0 := rfl
  rw [heq, ← Measure.map_map (g := fun h : Finset.Iic 0 → V => h ⟨0, Finset.mem_Iic.mpr le_rfl⟩)
    (measurable_pi_apply _) (measurable_frestrictLe 0),
    law_initialHistory, Measure.map_dirac' (measurable_pi_apply _)]

lemma law_ae_start_mem {A : Set V} (hA : MeasurableSet A) {a : V} (ha : a ∈ A) :
    ∀ᵐ ω ∂law κ a, ω 0 ∈ A := by
  rw [ae_iff]
  have h := congrArg (fun μ : Measure V => μ Aᶜ) (law_map_eval_zero κ a)
  simp only [Measure.dirac_apply' _ hA.compl,
    Set.indicator_of_notMem (Set.notMem_compl_iff.mpr ha)] at h
  rw [Measure.map_apply (measurable_pi_apply (X := fun _ : ℕ => V) 0) hA.compl] at h
  exact h

lemma law_ae_start_not_mem {A : Set V} (hA : MeasurableSet A) {a : V} (ha : a ∉ A) :
    ∀ᵐ ω ∂law κ a, ω 0 ∉ A :=
  law_ae_start_mem κ hA.compl ha

/-! ### Exit times of measurable sets -/

variable {A : Set V}

lemma exitTime_isStoppingTime' (hA : MeasurableSet A) :
    IsStoppingTime (Filtration.piLE (X := fun _ : ℕ ↦ V)) (exitTime A) :=
  coordinateProcess_adapted.isStoppingTime_hittingAfter hA.compl

lemma measurable_exitTime (hA : MeasurableSet A) : Measurable (exitTime (V := V) A) :=
  (exitTime_isStoppingTime' hA).measurable'

lemma measurable_exitVertex' (hA : MeasurableSet A) : Measurable (exitVertex (V := V) A) := by
  have hev : Measurable (fun p : (ℕ → V) × ℕ ↦ p.1 p.2) :=
    measurable_from_prod_countable_left (fun n ↦ measurable_pi_apply n)
  have hdur : Measurable (fun ω : ℕ → V => (exitTime A ω).untopD 0) :=
    (measurable_of_countable (fun n : WithTop ℕ => n.untopD 0)).comp (measurable_exitTime hA)
  exact hev.comp (measurable_id.prodMk hdur)

lemma measurableSet_exitTime_ne_top (hA : MeasurableSet A) :
    MeasurableSet {ω : ℕ → V | exitTime A ω ≠ ⊤} :=
  (measurable_exitTime hA) (measurableSet_singleton ⊤).compl

/-! ### Exit values -/

lemma measurable_exitPayoff (hA : MeasurableSet A) {g : V → ℝ} (hg : Measurable g) :
    Measurable (exitPayoff A g) := by
  classical
  exact Measurable.ite ((measurable_exitTime hA) (measurableSet_singleton ⊤)) measurable_const
    (hg.comp (measurable_exitVertex' hA))

/-- The expected payoff at the exit state, on the event of exit. -/
noncomputable def exitValue (A : Set V) (g : V → ℝ) (a : V) : ℝ :=
  ∫ ω, exitPayoff A g ω ∂law κ a

lemma measurable_exitValue (hA : MeasurableSet A) {g : V → ℝ} (hg : Measurable g) :
    Measurable (exitValue κ A g) := by
  have h := ((measurable_exitPayoff hA hg).stronglyMeasurable.integral_kernel
    (κ := pathKernel κ)).measurable
  simp only [pathKernel_apply] at h
  exact h

lemma abs_exitValue_le {g : V → ℝ} {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ v, |g v| ≤ C) (a : V) :
    |exitValue κ A g a| ≤ C := by
  unfold exitValue
  calc |∫ ω, exitPayoff A g ω ∂law κ a| ≤ ∫ ω, |exitPayoff A g ω| ∂law κ a :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _ω, C ∂law κ a := by
        apply integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) (integrable_const C)
        exact ae_of_all _ fun ω => abs_exitPayoff_le hC0 hC ω
    _ = C := by simp

/-- Outside `A` the chain exits at once, at its starting state. -/
lemma exitValue_of_not_mem (hA : MeasurableSet A) {g : V → ℝ} (hg : Measurable g) {a : V}
    (ha : a ∉ A) : exitValue κ A g a = g a := by
  have hae : ∀ᵐ ω ∂law κ a, exitPayoff A g ω = g (ω 0) := by
    filter_upwards [law_ae_start_not_mem κ hA ha] with ω hω
    have hne : exitTime A ω ≠ ⊤ := by rw [exitTime_eq_zero_of_not_mem hω]; exact WithTop.zero_ne_top
    simp only [exitPayoff, hne, ↓reduceIte, exitVertex_of_not_mem hω]
  rw [exitValue, integral_congr_ae hae,
    ← integral_map (measurable_pi_apply 0).aemeasurable hg.aestronglyMeasurable,
    law_map_eval_zero, integral_dirac' _ _ hg.stronglyMeasurable]

/-- First-step identity: inside `A`, the exit value is the `κ`-average of the exit values. -/
lemma exitValue_eq_integral (hA : MeasurableSet A) {g : V → ℝ} (hg : Measurable g)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ v, |g v| ≤ C) {a : V} (ha : a ∈ A) :
    exitValue κ A g a = ∫ b, exitValue κ A g b ∂κ a := by
  have hae : ∀ᵐ ω ∂law κ a, exitPayoff A g (walkShift 1 ω) = exitPayoff A g ω := by
    filter_upwards [law_ae_start_mem κ hA ha] with ω hω
    exact exitPayoff_walkShift_one hω
  rw [exitValue, ← integral_congr_ae hae,
    integral_walkShift_one κ a (measurable_exitPayoff hA hg) (abs_exitPayoff_le hC0 hC)]
  rfl

/-! ### The Dirichlet problem -/

/-- `f` is `κ`-harmonic at `a`: it is integrable for the step law from `a`, with mean `f a`. -/
def IsHarmonicAt (f : V → ℝ) (a : V) : Prop :=
  Integrable f (κ a) ∧ ∫ b, f b ∂κ a = f a

/-- `f` is harmonic on `A` and equal to `g` on the boundary set `B`. -/
def SolvesDirichlet (A B : Set V) (g f : V → ℝ) : Prop :=
  (∀ a ∈ A, IsHarmonicAt κ f a) ∧ ∀ b ∈ B, f b = g b

/-- The Dirichlet problem has a solution, unique on `A ∪ B`. -/
def HasUniqueDirichletSolution (A B : Set V) (g : V → ℝ) : Prop :=
  ∃ f, SolvesDirichlet κ A B g f ∧ ∀ f', SolvesDirichlet κ A B g f' → EqOn f' f (A ∪ B)

/-- For bounded measurable data the exit value solves the Dirichlet problem, for any boundary
set disjoint from `A`. -/
theorem exitValue_solvesDirichlet (hA : MeasurableSet A) {B : Set V} (hB : Disjoint A B)
    {g : V → ℝ} (hg : Measurable g) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ v, |g v| ≤ C) :
    SolvesDirichlet κ A B g (exitValue κ A g) := by
  refine ⟨fun a ha => ⟨?_, (exitValue_eq_integral κ hA hg hC0 hC ha).symm⟩, fun b hb => ?_⟩
  · exact (integrable_const C).mono' (measurable_exitValue κ hA hg).aestronglyMeasurable
      (ae_of_all _ fun b => by simpa [Real.norm_eq_abs] using abs_exitValue_le κ hC0 hC b)
  · exact exitValue_of_not_mem κ hA hg (Set.disjoint_right.mp hB hb)

/-- Uniqueness identifies every solution with the exit value. -/
theorem eqOn_exitValue_of_unique (hA : MeasurableSet A) {B : Set V} (hB : Disjoint A B)
    {g : V → ℝ} (hg : Measurable g) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ v, |g v| ≤ C)
    (hu : HasUniqueDirichletSolution κ A B g) {f : V → ℝ} (hf : SolvesDirichlet κ A B g f) :
    EqOn f (exitValue κ A g) (A ∪ B) := by
  obtain ⟨f₀, -, huniq⟩ := hu
  intro x hx
  rw [huniq f hf hx, huniq _ (exitValue_solvesDirichlet κ hA hB hg hC0 hC) hx]

/-! ### Uniqueness forces exit -/

/-- The probability that the chain never exits `A`. -/
noncomputable def survival (A : Set V) (a : V) : ℝ :=
  (law κ a).real {ω | exitTime A ω = ⊤}

lemma measurableSet_exitTime_eq_top (hA : MeasurableSet A) :
    MeasurableSet {ω : ℕ → V | exitTime A ω = ⊤} :=
  (measurable_exitTime hA) (measurableSet_singleton ⊤)

lemma survival_nonneg (a : V) : 0 ≤ survival κ A a := measureReal_nonneg

lemma survival_le_one (a : V) : survival κ A a ≤ 1 := by
  rw [survival]
  exact measureReal_le_one

lemma measurable_survival (hA : MeasurableSet A) : Measurable (survival κ A) := by
  have h := (Kernel.measurable_coe (pathKernel κ) (measurableSet_exitTime_eq_top hA)).ennreal_toReal
  simp only [pathKernel_apply] at h
  exact h

lemma survival_of_not_mem (hA : MeasurableSet A) {a : V} (ha : a ∉ A) : survival κ A a = 0 := by
  have hae := law_ae_start_not_mem κ hA ha
  rw [survival, measureReal_eq_zero_iff]
  apply measure_mono_null _ (ae_iff.mp hae)
  intro ω hω
  exact not_not.mpr ((exitTime_eq_top_iff A ω).mp hω 0)

/-- First-step identity for the probability of never exiting. -/
lemma survival_eq_integral (hA : MeasurableSet A) {a : V} (ha : a ∈ A) :
    survival κ A a = ∫ b, survival κ A b ∂κ a := by
  let F : (ℕ → V) → ℝ := {ω | exitTime A ω = ⊤}.indicator 1
  have hF : Measurable F := measurable_one.indicator (measurableSet_exitTime_eq_top hA)
  have hint (b : V) : ∫ ω, F ω ∂law κ b = survival κ A b :=
    integral_indicator_one (measurableSet_exitTime_eq_top hA)
  have hae : ∀ᵐ ω ∂law κ a, F (walkShift 1 ω) = F ω := by
    filter_upwards [law_ae_start_mem κ hA ha] with ω hω
    have hiff := exitTime_eq_top_iff_walkShift_one (A := A) hω
    simp only [F]
    by_cases h : exitTime A ω = ⊤
    · rw [Set.indicator_of_mem (show walkShift 1 ω ∈ {ω | exitTime A ω = ⊤} from hiff.mp h),
        Set.indicator_of_mem (show ω ∈ {ω | exitTime A ω = ⊤} from h), Pi.one_apply, Pi.one_apply]
    · rw [Set.indicator_of_notMem
          (show walkShift 1 ω ∉ {ω | exitTime A ω = ⊤} from fun h' => h (hiff.mpr h')),
        Set.indicator_of_notMem (show ω ∉ {ω | exitTime A ω = ⊤} from h)]
  rw [← hint, ← integral_congr_ae hae, integral_walkShift_one κ a hF
    (C := 1) (fun ω => by simp only [F, Set.indicator]; split_ifs <;> simp)]
  simp_rw [hint]

/-- If a Dirichlet problem on `A` with boundary set `B` (disjoint from `A`) has a unique
solution, the chain started in `A ∪ B` exits `A` almost surely. -/
theorem survival_eq_zero_of_unique (hA : MeasurableSet A) {B : Set V} (hB : Disjoint A B)
    {g : V → ℝ} (hu : HasUniqueDirichletSolution κ A B g) {a : V} (ha : a ∈ A ∪ B) :
    survival κ A a = 0 := by
  obtain ⟨f, hf, huniq⟩ := hu
  have hsol : SolvesDirichlet κ A B g (f + survival κ A) := by
    refine ⟨fun x hx => ⟨?_, ?_⟩, fun b hb => ?_⟩
    · exact (hf.1 x hx).1.add ((integrable_const (1 : ℝ)).mono'
        (measurable_survival κ hA).aestronglyMeasurable (ae_of_all _ fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg (survival_nonneg κ y)]
          exact survival_le_one κ y))
    · rw [Pi.add_apply, ← (hf.1 x hx).2, survival_eq_integral κ hA hx, ← integral_add (hf.1 x hx).1]
      · rfl
      · exact (integrable_const (1 : ℝ)).mono'
          (measurable_survival κ hA).aestronglyMeasurable (ae_of_all _ fun y => by
            rw [Real.norm_eq_abs, abs_of_nonneg (survival_nonneg κ y)]
            exact survival_le_one κ y)
    · rw [Pi.add_apply, survival_of_not_mem κ hA (Set.disjoint_right.mp hB hb), add_zero]
      exact hf.2 b hb
  have h := huniq _ hsol ha
  simpa using h

/-- If every solution of a Dirichlet problem with bounded measurable data stays within `η` of a
fixed function on `A`, the chain started in `A` exits `A` almost surely: the exit value is a
solution, and so is the exit value plus any multiple of the probability of never exiting. -/
theorem survival_eq_zero_of_forall_solution_bounded (hA : MeasurableSet A) {B : Set V}
    (hB : Disjoint A B) {g : V → ℝ} (hg : Measurable g) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ v, |g v| ≤ C) {h : V → ℝ} {η : ℝ}
    (hconv : ∀ f, SolvesDirichlet κ A B g f → ∀ a ∈ A, |f a - h a| ≤ η) {a : V} (ha : a ∈ A) :
    survival κ A a = 0 := by
  have hsint : ∀ x, Integrable (survival κ A) (κ x) := fun x =>
    (integrable_const (1 : ℝ)).mono' (measurable_survival κ hA).aestronglyMeasurable
      (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (survival_nonneg κ y)]
        exact survival_le_one κ y)
  have hsol0 := exitValue_solvesDirichlet κ hA hB hg hC0 hC
  have hsol : ∀ c : ℝ, SolvesDirichlet κ A B g (exitValue κ A g + c • survival κ A) := by
    intro c
    refine ⟨fun x hx => ⟨(hsol0.1 x hx).1.add ((hsint x).smul c), ?_⟩, fun b hb => ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [integral_add (hsol0.1 x hx).1 ((hsint x).const_mul c), integral_const_mul,
        (hsol0.1 x hx).2, ← survival_eq_integral κ hA hx]
    · rw [Pi.add_apply, Pi.smul_apply, survival_of_not_mem κ hA (Set.disjoint_right.mp hB hb),
        smul_zero, add_zero]
      exact hsol0.2 b hb
  by_contra hne
  have hpos : 0 < survival κ A a := lt_of_le_of_ne (survival_nonneg κ a) (Ne.symm hne)
  have h1 := hconv _ (hsol 0) a ha
  set c : ℝ := (2 * η + 1 + 2 * |exitValue κ A g a - h a|) / survival κ A a
  have h2 := hconv _ (hsol c) a ha
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_mul, add_zero] at h1 h2
  have hcs : c * survival κ A a = 2 * η + 1 + 2 * |exitValue κ A g a - h a| := by
    simp only [c]
    field_simp
  have hη : 0 ≤ η := (abs_nonneg _).trans h1
  have e : c * survival κ A a =
      (exitValue κ A g a + c * survival κ A a - h a) - (exitValue κ A g a - h a) := by ring
  have h3 : c * survival κ A a ≤ η + η := by
    calc c * survival κ A a ≤ |c * survival κ A a| := le_abs_self _
      _ = |(exitValue κ A g a + c * survival κ A a - h a) - (exitValue κ A g a - h a)| := by
          rw [← e]
      _ ≤ |exitValue κ A g a + c * survival κ A a - h a| + |exitValue κ A g a - h a| :=
          abs_sub _ _
      _ ≤ η + η := add_le_add h2 h1
  linarith [abs_nonneg (exitValue κ A g a - h a)]

end SpherePackings.MarkovChain
