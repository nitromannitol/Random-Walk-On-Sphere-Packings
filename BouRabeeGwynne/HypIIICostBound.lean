module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/HypIIICostBound.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.HypIIICostSeries

@[expose] public section

/-! Every finite corrected-iteration cost is bounded by its convergent series. -/

open scoped BigOperators

namespace BouRabeeGwynne

theorem hypIIICost_summable {A M ε K r : ℝ} (δ : ℕ → ℝ)
    (hA : 0 ≤ A) (hM : 0 ≤ M) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hr : 0 ≤ r) (hr1 : r < 1)
    (hδ : ∀ i, 0 ≤ δ i) (hmesh : ∀ i, δ i ≤ ε)
    (hgeom : ∀ i, δ i ≤ K * r ^ i) :
    Summable (fun i => A * M * δ i + Real.sqrt (ε * δ i) + 2 * M * δ i ^ 2) := by
  let b : ℕ → ℝ := fun i =>
    ((A * M + 2 * M * ε) * K) * r ^ i +
      Real.sqrt (ε * K) * (Real.sqrt r) ^ i
  have hroot : Real.sqrt r < 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt hr hr1
  have hsum : Summable b :=
    ((summable_geometric_of_lt_one hr hr1).mul_left ((A * M + 2 * M * ε) * K)).add
      ((summable_geometric_of_lt_one (Real.sqrt_nonneg r) hroot).mul_left
        (Real.sqrt (ε * K)))
  have hrootpow : ∀ i : ℕ, Real.sqrt (r ^ i) = (Real.sqrt r) ^ i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg hr i), ih, pow_succ]
  apply Summable.of_nonneg_of_le (fun i => by have hi := hδ i; positivity) _ hsum
  intro i
  have hsquare : δ i ^ 2 ≤ ε * δ i := by
    nlinarith [mul_le_mul_of_nonneg_right (hmesh i) (hδ i)]
  have hmain := mul_le_mul_of_nonneg_left (hgeom i) (mul_nonneg hA hM)
  have hcorrection : 2 * M * δ i ^ 2 ≤ 2 * M * ε * (K * r ^ i) := by
    calc
      _ ≤ 2 * M * (ε * δ i) := mul_le_mul_of_nonneg_left hsquare (by positivity)
      _ = 2 * M * ε * δ i := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hgeom i) (by positivity)
  have hcutoff := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hgeom i) hε)
  rw [← mul_assoc, Real.sqrt_mul (mul_nonneg hε hK), hrootpow] at hcutoff
  dsimp only [b]
  nlinarith

/-- The sufficient Taylor constant six is absorbed by replacing `M` by `3M`
in the already checked cost series. -/
theorem finite_corrected_cost_le_hypIIICost {A M ε K r : ℝ} (δ : ℕ → ℝ)
    (hA : 0 ≤ A) (hM : 0 ≤ M) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hr : 0 ≤ r) (hr1 : r < 1)
    (hδ : ∀ i, 0 ≤ δ i) (hmesh : ∀ i, δ i ≤ ε)
    (hgeom : ∀ i, δ i ≤ K * r ^ i) (n : ℕ) :
    6 * M * ε ^ 2 + ∑ i ∈ Finset.range n,
      (A * M * δ i + Real.sqrt (ε * δ i) + 6 * M * δ i ^ 2) ≤
      hypIIICost A (3 * M) ε δ := by
  have hsum := hypIIICost_summable (M := 3 * M) δ hA (by positivity) hε hK
    hr hr1 hδ hmesh hgeom
  have hfinite : (∑ i ∈ Finset.range n,
      (A * M * δ i + Real.sqrt (ε * δ i) + 6 * M * δ i ^ 2)) ≤
      ∑ i ∈ Finset.range n,
      (A * (3 * M) * δ i + Real.sqrt (ε * δ i) + 2 * (3 * M) * δ i ^ 2) := by
    apply Finset.sum_le_sum
    intro i _
    have hi := hδ i
    have hp : 0 ≤ A * M * δ i := by positivity
    nlinarith
  have htsum := hsum.sum_le_tsum (Finset.range n)
    (fun i _ => by have hi := hδ i; positivity)
  unfold hypIIICost
  have hinit : 6 * M * ε ^ 2 = 2 * (3 * M) * ε ^ 2 := by ring
  rw [hinit]
  exact add_le_add le_rfl (hfinite.trans htsum)

end BouRabeeGwynne
