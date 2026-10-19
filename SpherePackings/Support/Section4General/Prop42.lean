-- Built on Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne (commit cf73d6e).
import SpherePackings.Support.Section4General.AssumptionD
import SpherePackings.General.LevyProkhorovTest
import BouRabeeGwynne.Section4BrownianBallHarmonicMeasure
import BouRabeeGwynne.HarmonicPolynomialApproximation

/-!
# Proposition 4.2: convergence of harmonic measure

`rw-spheres.tex:1511-1516` (label `prop:convergence-of-harmonic-measure`): under Assumption D, the
discrete harmonic measure of a ball seen from `x^n` converges to the Brownian harmonic measure seen
from `x`, in the Lévy–Prokhorov metric, uniformly over the points `x` of the ball, for every ball
whose closure lies in `B_δ(D)` (the balls Assumption D speaks about).

The proof follows the paper: for a continuous test function `f` take a harmonic polynomial `P`
close to `f` near the sphere (in place of the paper's Poisson extension to a larger ball), apply
(4.2) to the function equal to `P` near the closed ball and to `f` elsewhere, and use (4.1) and the
Brownian identity `E[P(B_τ)] = P(x)`.  The Lévy–Prokhorov bound follows from finitely many such
test functions.
-/

open MeasureTheory Metric Filter Set
open BouRabeeGwynne

namespace SpherePackings

variable {d : ℕ}

/-- The function equal to `P` on `O` and to `f` elsewhere. -/
noncomputable def patch (O : Set (Euc d)) (p f : Euc d → ℝ) : Euc d → ℝ :=
  open Classical in O.piecewise p f

lemma patch_eq_left {O : Set (Euc d)} {p f : Euc d → ℝ} {x : Euc d} (hx : x ∈ O) :
    patch O p f x = p x := by
  classical
  simp [patch, Set.piecewise_eq_of_mem _ _ _ hx]

lemma patch_eq_right {O : Set (Euc d)} {p f : Euc d → ℝ} {x : Euc d} (hx : x ∉ O) :
    patch O p f x = f x := by
  classical
  simp [patch, Set.piecewise_eq_of_notMem _ _ _ hx]

lemma measurable_patch {O : Set (Euc d)} (hO : IsOpen O) {p f : Euc d → ℝ} (hp : Measurable p)
    (hf : Measurable f) : Measurable (patch O p f) := by
  classical
  exact hp.piecewise hO.measurableSet hf

lemma isHarmonicOn_patch {O : Set (Euc d)} (hO : IsOpen O) {p f : Euc d → ℝ}
    (hp : IsHarmonicOn p O) : IsHarmonicOn (patch O p f) O := by
  refine ⟨hp.1.congr fun x hx => patch_eq_left hx, fun x hx => ?_⟩
  have hlocal : patch O p f =ᶠ[nhds x] p := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact patch_eq_left hy
  rw [(InnerProductSpace.laplacian_congr_nhds hlocal).eq_of_nhds]
  exact hp.2 x hx

/-- A point outside the open ball but within `ρ` of the closed ball is within `ρ` of the sphere. -/
lemma mem_cthickening_sphere_of_not_mem_ball {c y : Euc d} {r ρ : ℝ} (hr : 0 < r)
    (hy : y ∉ ball c r) (hyO : y ∈ thickening ρ (closedBall c r)) :
    y ∈ cthickening ρ (sphere c r) := by
  have hρ : 0 < ρ := by
    by_contra h
    simp [thickening_of_nonpos (not_lt.mp h)] at hyO
  rw [thickening_closedBall hρ hr.le, mem_ball] at hyO
  have hyc : r ≤ dist y c := not_lt.mp (by simpa [mem_ball] using hy)
  have hpos : 0 < dist y c := hr.trans_le hyc
  let z : Euc d := c + (r / dist y c) • (y - c)
  have hz : z ∈ sphere c r := by
    rw [mem_sphere, dist_eq_norm]
    simp only [z, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hr,
      abs_of_pos hpos, ← dist_eq_norm]
    field_simp
  apply mem_cthickening_of_dist_le y z ρ _ hz
  have hyz : y - z = (1 - r / dist y c) • (y - c) := by
    simp only [z, sub_smul, one_smul]
    abel
  rw [dist_eq_norm, hyz, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by rw [sub_nonneg, div_le_one hpos]; exact hyc), ← dist_eq_norm,
    sub_mul, one_mul, div_mul_cancel₀ _ hpos.ne']
  linarith

/-- The core estimate: for a bounded continuous `f` there is `η' > 0` such that eventually, for
every point `x` of the ball and every vertex `a` within `η'` of `x`, the exit mean of `f` from `a`
is within `ε` of the Brownian one from `x`. -/
theorem prop42_test_core (hd : 1 ≤ d) (W : ℕ → NearestNeighbourWalk d)
    (near : ∀ n, Euc d → (W n).V)
    {D : Set (Euc d)} {δ : ℝ} (hAD : AssumptionD W near D δ) {c : Euc d} {r : ℝ} (hr : 0 < r)
    (hB : closedBall c r ⊆ cthickening δ D) {μ : Measure (BrownianPath d)}
    (hμ : IsStandardBrownianLaw μ) {f : Euc d → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ x, |f x| ≤ M) {ε : ℝ} (hε : 0 < ε) :
    ∃ η' > 0, (∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ z ∈ closedBall c r,
        dist ((near n z : Euc d)) z ≤ η) ∧
      ∀ᶠ n in atTop, ∀ x ∈ ball c r, ∀ a : (W n).V, dist (a : Euc d) x ≤ η' →
      |∫ y, f y ∂(W n).harmonicMeasure (ball c r) a -
        ∫ y, f y ∂(brownianSpatialHarmonicMeasure (ball c r) isOpen_ball μ hμ x :
          Measure (Euc d))| ≤ ε := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨P, hP, ρ, hρ, hclose⟩ := exists_harmonic_polynomial_near_sphere_collar hd c hr f hf hε4
  let p : Euc d → ℝ := polynomialEval P
  have hpc : Continuous p := (contDiff_polynomialEval P (n := 0)).continuous
  have hpH : ∀ U, IsHarmonicOn p U := isHarmonicOn_polynomialEval_of_laplacian_eq_zero P hP
  let O : Set (Euc d) := thickening ρ (closedBall c r)
  have hO : IsOpen O := isOpen_thickening
  let hC : Euc d → ℝ := patch O p f
  -- the closed ball, the set `B` of Assumption D
  have hBeq : closedBall c r ∩ cthickening δ D = closedBall c r := inter_eq_left.mpr hB
  have hcD : c ∈ cthickening δ D := hB (mem_closedBall_self hr.le)
  obtain ⟨-, -, hAD'⟩ := hAD
  obtain ⟨hnear, hdir⟩ := hAD' r hr c hcD
  rw [hBeq] at hnear hdir
  have hBO : closedBall c r ⊆ O := self_subset_thickening hρ _
  have hconv := hdir hC ⟨O, hO, hBO, isHarmonicOn_patch hO (hpH O)⟩
  -- a bound for the patched function
  let K : Set (Euc d) := closedBall c (ρ + r)
  have hK : IsCompact K := isCompact_closedBall c (ρ + r)
  have hOK : O ⊆ K := by
    intro y hy
    rw [show O = thickening ρ (closedBall c r) from rfl, thickening_closedBall hρ hr.le] at hy
    exact ball_subset_closedBall hy
  obtain ⟨Cp, hCp⟩ := hK.exists_bound_of_continuousOn hpc.continuousOn
  have hM0 : 0 ≤ M := (abs_nonneg (f c)).trans (hM c)
  have hCbound : ∀ y, |hC y| ≤ max Cp M := by
    intro y
    by_cases hy : y ∈ O
    · rw [show hC y = p y from patch_eq_left hy]
      exact (show |p y| ≤ Cp by simpa [Real.norm_eq_abs] using hCp y (hOK hy)).trans
        (le_max_left _ _)
    · rw [show hC y = f y from patch_eq_right hy]
      exact (hM y).trans (le_max_right _ _)
  have hC0 : 0 ≤ max Cp M := hM0.trans (le_max_right _ _)
  have hCmeas : Measurable hC := measurable_patch hO hpc.measurable hf.measurable
  -- uniform continuity of the polynomial on `K`
  obtain ⟨η₁, hη₁, hunif⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hpc.continuousOn) (ε / 4) hε4
  let η' := min (ρ / 2) (η₁ / 2)
  have hη' : 0 < η' := lt_min (by positivity) (by positivity)
  -- the vertex sets of the open and of the closed ball agree
  have hinner : ∀ n, (W n).inner (ball c r) = (W n).inner (closedBall c r) := by
    intro n
    ext v
    simp [NearestNeighbourWalk.inner, interior_closedBall c hr.ne', isOpen_ball.interior_eq]
  refine ⟨η', hη', hnear, ?_⟩
  filter_upwards [hconv (ε / 4) hε4] with n hcv
  intro x hx a hxa
  have haO : (a : Euc d) ∈ O := by
    rw [mem_thickening_iff]
    exact ⟨x, ball_subset_closedBall hx, hxa.trans_lt ((min_le_left _ _).trans_lt (by linarith))⟩
  have hap : hC a = p a := patch_eq_left haO
  -- (iii) continuity of the polynomial
  have hiii : |p a - p x| ≤ ε / 4 := by
    have h := hunif a (hOK haO) x (closedBall_subset_closedBall (by linarith)
      (ball_subset_closedBall hx)) (hxa.trans_lt ((min_le_right _ _).trans_lt (by linarith)))
    rw [Real.dist_eq] at h
    exact h.le
  -- (iv) the Brownian identity
  have hiv : |(∫ y, f y ∂(brownianSpatialHarmonicMeasure (ball c r) isOpen_ball μ hμ x :
      Measure (Euc d))) - p x| ≤ ε / 4 := by
    apply abs_integral_brownianSpatialHarmonicMeasure_sub_le hd hμ isOpen_ball isBounded_ball hf
      hpc ⟨univ, isOpen_univ, subset_univ _, hpH univ⟩ _ hx
    intro y hy
    have hy' : y ∈ cthickening ρ (sphere c r) :=
      self_subset_cthickening _ (frontier_ball_subset_sphere hy)
    rw [abs_sub_comm]
    exact (hclose y hy').le
  -- (ii) Assumption D (4.2) for the exit value
  have hsol := MarkovChain.exitValue_solvesDirichlet (W n).kernel
    ((W n).measurableSet_inner (closedBall c r)) ((W n).disjoint_inner_boundary (closedBall c r))
    (hCmeas.comp measurable_subtype_coe) hC0
    (fun v => hCbound v)
  have hii : |MarkovChain.exitValue (W n).kernel ((W n).inner (ball c r)) (fun v => hC v) a -
      hC a| ≤ ε / 4 := by
    rw [hinner n]
    by_cases ha : a ∈ (W n).inner (closedBall c r)
    · exact hcv _ hsol a ha
    · rw [MarkovChain.exitValue_of_not_mem (W n).kernel ((W n).measurableSet_inner _)
        (g := fun v => hC v) (hCmeas.comp measurable_subtype_coe) ha]
      simp [hε4.le]
  -- (i) the harmonic measure is carried outside the ball, where `hC` is close to `f`
  have hcarried : ∀ᵐ y ∂(W n).harmonicMeasure (ball c r) a, y ∉ ball c r := by
    have h := (W n).harmonicMeasure_inner_null (ball c r) a
    rw [isOpen_ball.interior_eq] at h
    rw [ae_iff]
    simp only [not_not, Set.ofPred_mem_eq]
    exact h
  have hclose' : ∀ y, y ∉ ball c r → |f y - hC y| ≤ ε / 4 := by
    intro y hy
    by_cases hyO : y ∈ O
    · rw [show hC y = p y from patch_eq_left hyO, abs_sub_comm]
      exact (hclose y (mem_cthickening_sphere_of_not_mem_ball hr hy hyO)).le
    · rw [show hC y = f y from patch_eq_right hyO, sub_self, abs_zero]
      exact hε4.le
  have hfint : Integrable f ((W n).harmonicMeasure (ball c r) a) :=
    (integrable_const M).mono' hf.aestronglyMeasurable
      (ae_of_all _ fun y => by simpa [Real.norm_eq_abs] using hM y)
  have hCint : Integrable hC ((W n).harmonicMeasure (ball c r) a) :=
    (integrable_const (max Cp M)).mono' hCmeas.aestronglyMeasurable
      (ae_of_all _ fun y => by simpa [Real.norm_eq_abs] using hCbound y)
  have hi : |(∫ y, f y ∂(W n).harmonicMeasure (ball c r) a) -
      ∫ y, hC y ∂(W n).harmonicMeasure (ball c r) a| ≤ ε / 4 := by
    rw [← integral_sub hfint hCint]
    have h := norm_integral_le_of_norm_le_const (μ := (W n).harmonicMeasure (ball c r) a)
      (f := fun y => f y - hC y) (C := ε / 4)
      (by filter_upwards [hcarried] with y hy; simpa [Real.norm_eq_abs] using hclose' y hy)
    rw [Real.norm_eq_abs] at h
    refine h.trans ?_
    have hmass : ((W n).harmonicMeasure (ball c r) a).real univ ≤ 1 := by
      rw [measureReal_def]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one
        (by simpa using (W n).harmonicMeasure_univ_le_one (ball c r) a)
    nlinarith
  have heq := (W n).integral_harmonicMeasure (ball c r) a hCmeas
  rw [heq] at hi
  calc _ = |((∫ y, f y ∂(W n).harmonicMeasure (ball c r) a) -
          MarkovChain.exitValue (W n).kernel ((W n).inner (ball c r)) (fun v => hC v) a) +
        (MarkovChain.exitValue (W n).kernel ((W n).inner (ball c r)) (fun v => hC v) a - hC a) +
        (p a - p x) + (p x - ∫ y, f y ∂(brownianSpatialHarmonicMeasure (ball c r) isOpen_ball μ hμ x :
          Measure (Euc d)))| := by rw [hap]; ring_nf
    _ ≤ ε / 4 + ε / 4 + ε / 4 + ε / 4 := by
        rw [abs_sub_comm] at hiv
        have h1 := abs_le.mp hi
        have h2 := abs_le.mp hii
        have h3 := abs_le.mp hiii
        have h4 := abs_le.mp hiv
        exact abs_le.mpr ⟨by linarith, by linarith⟩
    _ = ε := by ring

/-- **Proposition 4.2, test-function form**, from the vertex `x^n`. -/
theorem prop42_test (hd : 1 ≤ d) (W : ℕ → NearestNeighbourWalk d) (near : ∀ n, Euc d → (W n).V)
    {D : Set (Euc d)} {δ : ℝ} (hAD : AssumptionD W near D δ) {c : Euc d} {r : ℝ} (hr : 0 < r)
    (hB : closedBall c r ⊆ cthickening δ D) {μ : Measure (BrownianPath d)}
    (hμ : IsStandardBrownianLaw μ) {f : Euc d → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ x, |f x| ≤ M) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x ∈ ball c r,
      |∫ y, f y ∂(W n).harmonicMeasure (ball c r) (near n x) -
        ∫ y, f y ∂(brownianSpatialHarmonicMeasure (ball c r) isOpen_ball μ hμ x :
          Measure (Euc d))| ≤ ε := by
  obtain ⟨η', hη', hnear, hcore⟩ := prop42_test_core hd W near hAD hr hB hμ hf hM hε
  filter_upwards [hnear η' hη', hcore] with n hn hc x hx
  exact hc x hx (near n x) (hn x (ball_subset_closedBall hx))

/-- **Proposition 4.2, test-function form**, from any vertex in the ball. -/
theorem prop42_test_vertex (hd : 1 ≤ d) (W : ℕ → NearestNeighbourWalk d)
    (near : ∀ n, Euc d → (W n).V)
    {D : Set (Euc d)} {δ : ℝ} (hAD : AssumptionD W near D δ) {c : Euc d} {r : ℝ} (hr : 0 < r)
    (hB : closedBall c r ⊆ cthickening δ D) {μ : Measure (BrownianPath d)}
    (hμ : IsStandardBrownianLaw μ) {f : Euc d → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ x, |f x| ≤ M) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ a : (W n).V, (a : Euc d) ∈ ball c r →
      |∫ y, f y ∂(W n).harmonicMeasure (ball c r) a -
        ∫ y, f y ∂(brownianSpatialHarmonicMeasure (ball c r) isOpen_ball μ hμ a :
          Measure (Euc d))| ≤ ε := by
  obtain ⟨η', hη', -, hcore⟩ := prop42_test_core hd W near hAD hr hB hμ hf hM hε
  filter_upwards [hcore] with n hc a ha
  exact hc a ha a (by rw [dist_self]; exact hη'.le)

/-- **Proposition 4.2** (`prop:convergence-of-harmonic-measure`): under Assumption D, for every ball
whose closure lies in `B_δ(D)` (in particular the unit ball, when its closure lies in `B_δ(D)`), the discrete harmonic measure
seen from `x^n` converges to the Brownian harmonic measure seen from `x` in the Lévy–Prokhorov
metric, uniformly over the points `x` of the ball. -/
theorem prop42_general (hd : 1 ≤ d) (W : ℕ → NearestNeighbourWalk d)
    (near : ∀ n, Euc d → (W n).V) {D : Set (Euc d)} {δ : ℝ} (hAD : AssumptionD W near D δ)
    {c : Euc d} {r : ℝ} (hr : 0 < r) (hB : closedBall c r ⊆ cthickening δ D)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) :
    ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ x ∈ ball c r,
      levyProkhorovEDist ((W n).harmonicMeasure (ball c r) (near n x))
        (brownianSpatialHarmonicMeasure (ball c r) isOpen_ball μ hμ x : Measure (Euc d)) ≤
        ENNReal.ofReal η := by
  intro η hη
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hS : IsCompact (sphere c r) := isCompact_sphere c r
  have hSne : (sphere c r).Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
  obtain ⟨ι, hι, g, hgc, hgb, hLP⟩ :=
    exists_test_family_levyProkhorov hS hSne (ρ := η / 4) (by positivity)
  have := hι
  have hall : ∀ᶠ n in atTop, ∀ i, ∀ x ∈ ball c r,
      |∫ y, g i y ∂(W n).harmonicMeasure (ball c r) (near n x) -
        ∫ y, g i y ∂(brownianSpatialHarmonicMeasure (ball c r) isOpen_ball μ hμ x :
          Measure (Euc d))| ≤ η / 4 := by
    rw [Filter.eventually_all]
    intro i
    exact prop42_test hd W near hAD hr hB hμ (hgc i) (M := 1)
      (fun x => by rw [abs_of_nonneg (hgb i x).1]; exact (hgb i x).2) (by positivity)
  filter_upwards [hall] with n hn x hx
  rw [levyProkhorovEDist_comm]
  have hconc : (brownianSpatialHarmonicMeasure (ball c r) isOpen_ball μ hμ x : Measure (Euc d))
      (sphere c r)ᶜ = 0 := by
    have h := brownianSpatialHarmonicMeasure_ae_mem_frontier hd hμ isOpen_ball isBounded_ball hx
    rw [ae_iff] at h
    exact measure_mono_null (fun y hy hy' => hy (frontier_ball_subset_sphere hy')) h
  have h := hLP _ _ (θ := η / 4) (by positivity) hconc (fun i => hn i x hx)
  calc _ ≤ _ := h
    _ = ENNReal.ofReal η := by congr 1; ring

/-- **Proposition 4.2** from any vertex of the ball: eventually, for every vertex `a` of the ball,
the discrete harmonic measure seen from `a` is within `η` of the Brownian one seen from `a`. -/
theorem prop42_vertex (hd : 1 ≤ d) (W : ℕ → NearestNeighbourWalk d)
    (near : ∀ n, Euc d → (W n).V) {D : Set (Euc d)} {δ : ℝ} (hAD : AssumptionD W near D δ)
    {c : Euc d} {r : ℝ} (hr : 0 < r) (hB : closedBall c r ⊆ cthickening δ D)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) :
    ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ a : (W n).V, (a : Euc d) ∈ ball c r →
      levyProkhorovEDist ((W n).harmonicMeasure (ball c r) a)
        (brownianSpatialHarmonicMeasure (ball c r) isOpen_ball μ hμ a : Measure (Euc d)) ≤
        ENNReal.ofReal η := by
  intro η hη
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hS : IsCompact (sphere c r) := isCompact_sphere c r
  have hSne : (sphere c r).Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
  obtain ⟨ι, hι, g, hgc, hgb, hLP⟩ :=
    exists_test_family_levyProkhorov hS hSne (ρ := η / 4) (by positivity)
  have := hι
  have hall : ∀ᶠ n in atTop, ∀ i, ∀ a : (W n).V, (a : Euc d) ∈ ball c r →
      |∫ y, g i y ∂(W n).harmonicMeasure (ball c r) a -
        ∫ y, g i y ∂(brownianSpatialHarmonicMeasure (ball c r) isOpen_ball μ hμ a :
          Measure (Euc d))| ≤ η / 4 := by
    rw [Filter.eventually_all]
    intro i
    exact prop42_test_vertex hd W near hAD hr hB hμ (hgc i) (M := 1)
      (fun x => by rw [abs_of_nonneg (hgb i x).1]; exact (hgb i x).2) (by positivity)
  filter_upwards [hall] with n hn a ha
  rw [levyProkhorovEDist_comm]
  have hconc : (brownianSpatialHarmonicMeasure (ball c r) isOpen_ball μ hμ a : Measure (Euc d))
      (sphere c r)ᶜ = 0 := by
    have h := brownianSpatialHarmonicMeasure_ae_mem_frontier hd hμ isOpen_ball isBounded_ball ha
    rw [ae_iff] at h
    exact measure_mono_null (fun y hy hy' => hy (frontier_ball_subset_sphere hy')) h
  have h := hLP _ _ (θ := η / 4) (by positivity) hconc (fun i => hn i a ha)
  calc _ ≤ _ := h
    _ = ENNReal.ofReal η := by congr 1; ring

end SpherePackings
