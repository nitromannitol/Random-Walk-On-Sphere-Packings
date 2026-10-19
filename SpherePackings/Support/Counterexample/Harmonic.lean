import SpherePackings.Support.Counterexample.Tangency

/-!
# Neighbours in the packing of Theorem 6.1 and the harmonic level function

Every sphere touches finitely many others (at most `2(k+3)+4`), and `levelValue` is harmonic for
simple random walk on the tangency graph: the sum of `levelValue b - levelValue a` over the
neighbours `b` of `a` vanishes.  Big spheres off the middle plane have one neighbour on each
adjacent level; a big middle sphere has one big neighbour on level `-1` (difference `-4`) and four
small middle neighbours (difference `+1` each); a small middle sphere has one big neighbour
(difference `-1`) and one small neighbour on the next level (difference `+1`).
-/

namespace SpherePackings.Counterexample

variable {k : ℕ}

/-- The neighbours of a sphere in the tangency graph. -/
def nbrs (a : Idx k) : Set (Idx k) := {b | (packing k).Tangent a b}

open scoped Classical

/-- The sign `±1` of a unit step, indexed by a `Bool`. -/
private def sgn (b : Bool) : ℤ := if b then 1 else -1

private lemma sgn_sq (b : Bool) : sgn b ^ 2 = 1 := by cases b <;> simp [sgn]

private lemma sgn_ne_zero (b : Bool) : sgn b ≠ 0 := by cases b <;> simp [sgn]

/-- A unit step determines its coordinate and its sign. -/
private lemma single_sgn_inj {n : ℕ} {i j : Fin n} {b c : Bool}
    (h : (Pi.single i (sgn b) : Fin n → ℤ) = Pi.single j (sgn c)) : i = j ∧ b = c := by
  by_cases hij : i = j
  · subst hij
    have h1 : sgn b = sgn c := by simpa using congrFun h i
    refine ⟨rfl, ?_⟩
    cases b <;> cases c <;> simp_all [sgn]
  · have h1 := congrFun h i
    simp [hij] at h1
    exact absurd h1 (sgn_ne_zero b)

/-- The squares of the coordinates of a unit step add up to one. -/
private lemma sum_sq_sub_single {n : ℕ} (x : Fin n → ℤ) (i : Fin n) (b : Bool) :
    ∑ j, (x j - (x + (Pi.single i (sgn b) : Fin n → ℤ)) j) ^ 2 = 1 := by
  have h : ∀ j, (x j - (x + (Pi.single i (sgn b) : Fin n → ℤ)) j) ^ 2 =
      (Pi.single i (sgn b) : Fin n → ℤ) j ^ 2 := by
    intro j
    rw [Pi.add_apply]
    ring
  simp only [h]
  rw [Finset.sum_eq_single i]
  · simp [sgn_sq]
  · intro j _ hj
    simp [hj]
  · intro h'
    exact absurd (Finset.mem_univ i) h'

/-- Integer vectors at squared distance one differ by a unit step. -/
private lemma exists_single_of_sum_sq {n : ℕ} {x x' : Fin n → ℤ}
    (h : ∑ j, (x j - x' j) ^ 2 = 1) :
    ∃ (i : Fin n) (b : Bool), x' = x + (Pi.single i (sgn b) : Fin n → ℤ) := by
  have hne : ∑ j, (x j - x' j) ^ 2 ≠ 0 := by rw [h]; norm_num
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hle : (x i - x' i) ^ 2 ≤ ∑ j, (x j - x' j) ^ 2 :=
    Finset.single_le_sum (f := fun j => (x j - x' j) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  have hpos : 0 < (x i - x' i) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hi)
  have hone : (x i - x' i) ^ 2 = 1 := by linarith
  have hsplit : (x i - x' i) ^ 2 + ∑ j ∈ Finset.univ.erase i, (x j - x' j) ^ 2 =
      ∑ j, (x j - x' j) ^ 2 :=
    Finset.add_sum_erase Finset.univ (fun j => (x j - x' j) ^ 2) (Finset.mem_univ i)
  have hrest : ∑ j ∈ Finset.univ.erase i, (x j - x' j) ^ 2 = 0 := by linarith
  have hz : ∀ j ∈ Finset.univ.erase i, x j - x' j = 0 := by
    intro j hj
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (x j - x' j)).1 hrest j hj
    exact (pow_eq_zero_iff two_ne_zero).1 h0
  have hv : x i - x' i = 1 ∨ x i - x' i = -1 := by
    have h2 : (x i - x' i - 1) * (x i - x' i + 1) = 0 := by linear_combination hone
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  rcases hv with hv | hv
  · refine ⟨i, false, funext fun j => ?_⟩
    by_cases hj : j = i
    · subst hj
      simp [sgn]
      omega
    · have := hz j (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩)
      simp [hj]
      omega
  · refine ⟨i, true, funext fun j => ?_⟩
    by_cases hj : j = i
    · subst hj
      simp [sgn]
      omega
    · have := hz j (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩)
      simp [hj]
      omega

/-! The small spheres touching a big sphere `2x` with `x₀ = 0`. -/

/-- The offset `1` or `0` selected by a bit. -/
private def bitOff (b : Bool) : ℤ := if b then 1 else 0

private lemma bitOff_inj {b c : Bool} (h : bitOff b = bitOff c) : b = c := by
  cases b <;> cases c <;> simp_all [bitOff]

/-- The four small spheres touching `2x` (for `x₀ = 0`): coordinates `1, 2` are `2xⱼ - bit`. -/
private def touchY (x : Fin (k+3) → ℤ) (t : Bool × Bool) : Fin (k+3) → ℤ :=
  fun j => 2 * x j - (if j.val = 1 then bitOff t.1 else 0) - (if j.val = 2 then bitOff t.2 else 0)

private lemma val_one_fin : ((1 : Fin (k+3)) : ℕ) = 1 :=
  Nat.mod_eq_of_lt (show 1 < k + 3 by omega)

private lemma val_two_fin : ((2 : Fin (k+3)) : ℕ) = 2 :=
  Nat.mod_eq_of_lt (show 2 < k + 3 by omega)

private lemma touchY_zero (x : Fin (k+3) → ℤ) (t : Bool × Bool) :
    touchY x t 0 = 2 * x 0 := by
  simp [touchY]

private lemma touchY_one (x : Fin (k+3) → ℤ) (t : Bool × Bool) :
    touchY x t 1 = 2 * x 1 - bitOff t.1 := by
  simp [touchY]

private lemma touchY_two (x : Fin (k+3) → ℤ) (t : Bool × Bool) :
    touchY x t 2 = 2 * x 2 - bitOff t.2 := by
  have h1 : ¬ ((2 : Fin (k+3)).val = 1) := by
    rw [val_two_fin]
    omega
  unfold touchY
  rw [ite_eq_right h1, ite_eq_left val_two_fin]
  ring

private lemma touchY_of_three {x : Fin (k+3) → ℤ} {t : Bool × Bool} {j : Fin (k+3)}
    (hj : 3 ≤ j.val) : touchY x t j = 2 * x j := by
  have h1 : j.val ≠ 1 := by omega
  have h2 : j.val ≠ 2 := by omega
  simp [touchY, h1, h2]

private lemma touchY_mem {x : Fin (k+3) → ℤ} (h : x 0 = 0) (t : Bool × Bool) :
    0 ≤ touchY x t 0 ∧ ∀ j : Fin (k+3), 3 ≤ j.val → Even (touchY x t j) := by
  refine ⟨?_, fun j hj => ?_⟩
  · rw [touchY_zero, h]
    norm_num
  · rw [touchY_of_three hj]
    exact even_two_mul _

/-- Two integer vectors agreeing at `0`, `1`, `2` and at all `j ≥ 3` are equal. -/
private lemma fin_funext_three {f g : Fin (k+3) → ℤ} (h0 : f 0 = g 0) (h1 : f 1 = g 1)
    (h2 : f 2 = g 2) (h3 : ∀ j : Fin (k+3), 3 ≤ j.val → f j = g j) : f = g := by
  funext j
  by_cases hj0 : j = 0
  · rw [hj0]
    exact h0
  by_cases hj1 : j = 1
  · rw [hj1]
    exact h1
  by_cases hj2 : j = 2
  · rw [hj2]
    exact h2
  apply h3
  have e0 : j.val ≠ 0 := fun h => hj0 (Fin.ext (by simp [h]))
  have e1 : j.val ≠ 1 := fun h => hj1 (Fin.ext (by simp [h]))
  have e2 : j.val ≠ 2 := fun h => hj2 (Fin.ext (h.trans val_two_fin.symm))
  omega

/-- The big sphere `⌊(y+1)/2⌋` touching the small sphere `y` (for `y₀ = 0`). -/
private def halfUp (y : Fin (k+3) → ℤ) : Fin (k+3) → ℤ := fun j => (y j + 1) / 2

private lemma halfUp_zero {y : Fin (k+3) → ℤ} (h : y 0 = 0) : halfUp y 0 = 0 := by
  simp [halfUp, h]

private lemma halfUp_le {y : Fin (k+3) → ℤ} (h : y 0 = 0) : halfUp y 0 ≤ 0 :=
  (halfUp_zero h).le

/-! Candidate neighbours of a big sphere `x` (indexed by unit steps and by `Bool × Bool`). -/

/-- A candidate neighbour of the big sphere `x` is admissible: a unit step keeping the first
coordinate `≤ 0`, or (when `x₀ = 0`) one of the four touching small spheres. -/
private def bigPre (x : BigIdx k) : (Fin (k+3) × Bool) ⊕ (Bool × Bool) → Prop
  | .inl p => (x.1 + (Pi.single p.1 (sgn p.2) : Fin (k+3) → ℤ)) 0 ≤ 0
  | .inr _ => x.1 0 = 0

/-- The candidate neighbours of the big sphere `x`. -/
private noncomputable def bigStep (x : BigIdx k) : (Fin (k+3) × Bool) ⊕ (Bool × Bool) → Idx k
  | .inl p => if h : (x.1 + (Pi.single p.1 (sgn p.2) : Fin (k+3) → ℤ)) 0 ≤ 0 then
      .inl ⟨x.1 + (Pi.single p.1 (sgn p.2) : Fin (k+3) → ℤ), h⟩ else .inl x
  | .inr t => if h : x.1 0 = 0 then .inr ⟨touchY x.1 t, touchY_mem h t⟩ else .inl x

/-- The neighbours of the big sphere `x`. -/
private noncomputable def bigNbrs (x : BigIdx k) : Finset (Idx k) :=
  (Finset.univ.filter (bigPre x)).image (bigStep x)

/-! Candidate neighbours of a small sphere `y`. -/

/-- A candidate neighbour of the small sphere `y`: a unit step keeping `y` small, or (when
`y₀ = 0`) the big sphere touching it. -/
private def smallPre (y : SmallIdx k) : (Fin (k+3) × Bool) ⊕ Unit → Prop
  | .inl p => 0 ≤ (y.1 + (Pi.single p.1 (sgn p.2) : Fin (k+3) → ℤ)) 0 ∧
      ∀ j : Fin (k+3), 3 ≤ j.val → Even ((y.1 + (Pi.single p.1 (sgn p.2) : Fin (k+3) → ℤ)) j)
  | .inr _ => y.1 0 = 0

/-- The candidate neighbours of the small sphere `y`. -/
private noncomputable def smallStep (y : SmallIdx k) : (Fin (k+3) × Bool) ⊕ Unit → Idx k
  | .inl p => if h : 0 ≤ (y.1 + (Pi.single p.1 (sgn p.2) : Fin (k+3) → ℤ)) 0 ∧
      ∀ j : Fin (k+3), 3 ≤ j.val → Even ((y.1 + (Pi.single p.1 (sgn p.2) : Fin (k+3) → ℤ)) j) then
      .inr ⟨y.1 + (Pi.single p.1 (sgn p.2) : Fin (k+3) → ℤ), h⟩ else .inr y
  | .inr _ => if h : y.1 0 = 0 then .inl ⟨halfUp y.1, halfUp_le h⟩ else .inr y

/-- The neighbours of the small sphere `y`. -/
private noncomputable def smallNbrs (y : SmallIdx k) : Finset (Idx k) :=
  (Finset.univ.filter (smallPre y)).image (smallStep y)

/-! Evaluation of the candidate maps. -/

private lemma bigStep_inl {x : BigIdx k} {p : Fin (k+3) × Bool}
    (h : (x.1 + (Pi.single p.1 (sgn p.2) : Fin (k+3) → ℤ)) 0 ≤ 0) :
    bigStep x (.inl p) = .inl ⟨x.1 + (Pi.single p.1 (sgn p.2) : Fin (k+3) → ℤ), h⟩ := by
  rw [bigStep, dite_eq_left h]

private lemma bigStep_inr {x : BigIdx k} {t : Bool × Bool} (h : x.1 0 = 0) :
    bigStep x (.inr t) = .inr ⟨touchY x.1 t, touchY_mem h t⟩ := by
  rw [bigStep, dite_eq_left h]

private lemma smallStep_inl {y : SmallIdx k} {p : Fin (k+3) × Bool}
    (h : 0 ≤ (y.1 + (Pi.single p.1 (sgn p.2) : Fin (k+3) → ℤ)) 0 ∧
      ∀ j : Fin (k+3), 3 ≤ j.val → Even ((y.1 + (Pi.single p.1 (sgn p.2) : Fin (k+3) → ℤ)) j)) :
    smallStep y (.inl p) = .inr ⟨y.1 + (Pi.single p.1 (sgn p.2) : Fin (k+3) → ℤ), h⟩ := by
  rw [smallStep, dite_eq_left h]

private lemma smallStep_inr {y : SmallIdx k} {u : Unit} (h : y.1 0 = 0) :
    smallStep y (.inr u) = .inl ⟨halfUp y.1, halfUp_le h⟩ := by
  rw [smallStep, dite_eq_left h]

/-! Level differences of the candidate neighbours. -/

private lemma diffB_inl (x : BigIdx k) (p : Fin (k+3) × Bool) :
    (if bigPre x (.inl p) then levelValue k (bigStep x (.inl p)) - levelValue k (.inl x) else 0) =
      if (x.1 + (Pi.single p.1 (sgn p.2) : Fin (k+3) → ℤ)) 0 ≤ 0 then 4 * (Pi.single p.1 (sgn p.2) : Fin (k+3) → ℤ) 0 else 0 := by
  by_cases h : (x.1 + (Pi.single p.1 (sgn p.2) : Fin (k+3) → ℤ)) 0 ≤ 0
  · have hb : bigPre x (.inl p) := h
    rw [ite_eq_left hb, ite_eq_left h, bigStep_inl h]
    simp only [levelValue, Pi.add_apply]
    ring
  · have hb : ¬ bigPre x (.inl p) := h
    rw [ite_eq_right hb, ite_eq_right h]

private lemma diffB_inr (x : BigIdx k) (t : Bool × Bool) :
    (if bigPre x (.inr t) then levelValue k (bigStep x (.inr t)) - levelValue k (.inl x) else 0) =
      if x.1 0 = 0 then 1 else 0 := by
  by_cases h : x.1 0 = 0
  · have hb : bigPre x (.inr t) := h
    rw [ite_eq_left hb, ite_eq_left h, bigStep_inr h]
    simp only [levelValue, touchY_zero, h]
    norm_num
  · have hb : ¬ bigPre x (.inr t) := h
    rw [ite_eq_right hb, ite_eq_right h]

private lemma diffS_inl (y : SmallIdx k) (p : Fin (k+3) × Bool) :
    (if smallPre y (.inl p) then levelValue k (smallStep y (.inl p)) - levelValue k (.inr y)
      else 0) =
      if smallPre y (.inl p) then (Pi.single p.1 (sgn p.2) : Fin (k+3) → ℤ) 0 else 0 := by
  by_cases h : smallPre y (.inl p)
  · rw [ite_eq_left h, ite_eq_left h, smallStep_inl h]
    simp only [levelValue, Pi.add_apply]
    ring
  · rw [ite_eq_right h, ite_eq_right h]

private lemma diffS_inr (y : SmallIdx k) (u : Unit) :
    (if smallPre y (.inr u) then levelValue k (smallStep y (.inr u)) - levelValue k (.inr y)
      else 0) =
      if y.1 0 = 0 then -1 else 0 := by
  by_cases h : y.1 0 = 0
  · have hb : smallPre y (.inr u) := h
    rw [ite_eq_left hb, ite_eq_left h, smallStep_inr h]
    simp only [levelValue, halfUp_zero h, h]
    norm_num
  · have hb : ¬ smallPre y (.inr u) := h
    rw [ite_eq_right hb, ite_eq_right h]

/-- Unit steps in the first coordinate: `Pi.single (succ i) d` vanishes at `0`. -/
private lemma single_succ_zero (i : Fin (k+2)) (d : ℤ) :
    (Pi.single i.succ d : Fin (k+3) → ℤ) 0 = 0 := by
  have h : (0 : Fin (k+3)) ≠ i.succ := by
    intro h'
    have := congrArg Fin.val h'
    simp only [Fin.val_zero, Fin.val_succ] at this
    omega
  simp [h]

/-- Splitting off the coordinate `0` of a sum over `Fin (k+3)`. -/
private lemma sum_fin_three {M : Type*} [AddCommMonoid M] (f : Fin (k+3) → M) :
    ∑ i, f i = f 0 + ∑ i : Fin (k+2), f i.succ :=
  Fin.sum_univ_succ f

/-- The admissible small neighbours with first coordinate `0` are exactly the two unit steps
`±e₀` that keep `y₀ ≥ 0`. -/
private lemma smallPre_zero_iff (y : SmallIdx k) (b : Bool) :
    smallPre y (.inl (0, b)) ↔ 0 ≤ y.1 0 + sgn b := by
  have hev : ∀ j : Fin (k+3), 3 ≤ j.val → Even ((y.1 + (Pi.single (0 : Fin (k+3)) (sgn b) : Fin (k+3) → ℤ)) j) := by
    intro j hj
    have hj0 : j ≠ 0 := by
      rintro rfl
      simp at hj
    rw [Pi.add_apply, Pi.single_apply, ite_eq_right hj0, add_zero]
    exact y.2.2 j hj
  have h0 : (y.1 + (Pi.single (0 : Fin (k+3)) (sgn b) : Fin (k+3) → ℤ)) 0 = y.1 0 + sgn b := by
    simp
  show (0 ≤ (y.1 + (Pi.single (0 : Fin (k+3)) (sgn b) : Fin (k+3) → ℤ)) 0 ∧
    ∀ j : Fin (k+3), 3 ≤ j.val → Even ((y.1 + (Pi.single (0 : Fin (k+3)) (sgn b) : Fin (k+3) → ℤ)) j)) ↔ _
  rw [h0]
  exact ⟨fun h => h.1, fun h => ⟨h, hev⟩⟩

/-! Injectivity of the candidate maps on admissible candidates. -/

private lemma bigStep_injOn (x : BigIdx k) :
    Set.InjOn (bigStep x) ↑(Finset.univ.filter (bigPre x)) := by
  intro u hu v hv huv
  have hu' : bigPre x u := (Finset.mem_filter.1 (Finset.mem_coe.1 hu)).2
  have hv' : bigPre x v := (Finset.mem_filter.1 (Finset.mem_coe.1 hv)).2
  rcases u with p | t <;> rcases v with q | s
  · have hp : (x.1 + (Pi.single p.1 (sgn p.2) : Fin (k+3) → ℤ)) 0 ≤ 0 := hu'
    have hq : (x.1 + (Pi.single q.1 (sgn q.2) : Fin (k+3) → ℤ)) 0 ≤ 0 := hv'
    rw [bigStep_inl hp, bigStep_inl hq] at huv
    have h1 : x.1 + (Pi.single p.1 (sgn p.2) : Fin (k+3) → ℤ) = x.1 + (Pi.single q.1 (sgn q.2) : Fin (k+3) → ℤ) :=
      congrArg Subtype.val (Sum.inl_injective huv)
    obtain ⟨h2, h3⟩ := single_sgn_inj (add_left_cancel h1)
    exact congrArg Sum.inl (Prod.ext h2 h3)
  · have hp : (x.1 + (Pi.single p.1 (sgn p.2) : Fin (k+3) → ℤ)) 0 ≤ 0 := hu'
    rw [bigStep_inl hp, bigStep_inr hv'] at huv
    cases huv
  · have hq : (x.1 + (Pi.single q.1 (sgn q.2) : Fin (k+3) → ℤ)) 0 ≤ 0 := hv'
    rw [bigStep_inr hu', bigStep_inl hq] at huv
    cases huv
  · rw [bigStep_inr hu', bigStep_inr hv'] at huv
    have h1 : touchY x.1 t = touchY x.1 s := congrArg Subtype.val (Sum.inr_injective huv)
    have e1 : bitOff t.1 = bitOff s.1 := by
      have := congrFun h1 1
      rw [touchY_one, touchY_one] at this
      linarith
    have e2 : bitOff t.2 = bitOff s.2 := by
      have := congrFun h1 2
      rw [touchY_two, touchY_two] at this
      linarith
    exact congrArg Sum.inr (Prod.ext (bitOff_inj e1) (bitOff_inj e2))

private lemma smallStep_injOn (y : SmallIdx k) :
    Set.InjOn (smallStep y) ↑(Finset.univ.filter (smallPre y)) := by
  intro u hu v hv huv
  have hu' : smallPre y u := (Finset.mem_filter.1 (Finset.mem_coe.1 hu)).2
  have hv' : smallPre y v := (Finset.mem_filter.1 (Finset.mem_coe.1 hv)).2
  rcases u with p | a <;> rcases v with q | b
  · rw [smallStep_inl hu', smallStep_inl hv'] at huv
    have h1 : y.1 + (Pi.single p.1 (sgn p.2) : Fin (k+3) → ℤ) = y.1 + (Pi.single q.1 (sgn q.2) : Fin (k+3) → ℤ) :=
      congrArg Subtype.val (Sum.inr_injective huv)
    obtain ⟨h2, h3⟩ := single_sgn_inj (add_left_cancel h1)
    exact congrArg Sum.inl (Prod.ext h2 h3)
  · have hy : y.1 0 = 0 := hv'
    rw [smallStep_inl hu', smallStep_inr hy] at huv
    cases huv
  · have hy : y.1 0 = 0 := hu'
    rw [smallStep_inr hy, smallStep_inl hv'] at huv
    cases huv
  · rfl

/-! Sums of level differences over the candidate neighbours. -/

private lemma sum_big (x : BigIdx k) :
    ∑ u ∈ Finset.univ.filter (bigPre x), (levelValue k (bigStep x u) - levelValue k (.inl x)) = 0 := by
  have hx := x.2
  rw [Finset.sum_filter]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool, diffB_inl, diffB_inr]
  rw [sum_fin_three]
  simp only [single_succ_zero, mul_zero, ite_self, Finset.sum_const_zero, add_zero]
  simp [sgn]
  split_ifs <;> omega

private lemma sum_small (y : SmallIdx k) :
    ∑ u ∈ Finset.univ.filter (smallPre y),
      (levelValue k (smallStep y u) - levelValue k (.inr y)) = 0 := by
  have hy := y.2.1
  rw [Finset.sum_filter]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_unique,
    diffS_inl, diffS_inr]
  rw [sum_fin_three]
  simp only [single_succ_zero, ite_self, Finset.sum_const_zero, add_zero]
  simp [sgn, smallPre_zero_iff]
  split_ifs <;> omega

/-! Identification of the neighbour sets. -/

/-- Sums over a `Finset` image of an injective map, as sums over the `Finset` of a set. -/
private lemma sum_toFinset_eq {s : Set (Idx k)} (hs : s.Finite) {F : Finset (Idx k)}
    (hF : s = ↑F) (f : Idx k → ℤ) : ∑ b ∈ hs.toFinset, f b = ∑ b ∈ F, f b := by
  subst hF
  congr 1
  ext b
  simp

private lemma nbrs_inl_eq (x : BigIdx k) : nbrs (.inl x) = ↑(bigNbrs x) := by
  ext b
  constructor
  · intro hb
    rcases b with x' | y'
    · obtain ⟨i, c, hi⟩ := exists_single_of_sum_sq ((tangent_inl_inl x x').1 hb)
      have hp : (x.1 + (Pi.single i (sgn c) : Fin (k+3) → ℤ)) 0 ≤ 0 := by
        rw [← hi]
        exact x'.2
      refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨Sum.inl (i, c),
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hp⟩, ?_⟩)
      rw [bigStep_inl hp]
      congr 1
      exact Subtype.ext hi.symm
    · obtain ⟨hx0, hy0, h1, h2, h3⟩ := (tangent_inl_inr x y').1 hb
      obtain ⟨t1, ht1⟩ : ∃ t1 : Bool, y'.1 1 = 2 * x.1 1 - bitOff t1 := by
        rcases h1 with h | h
        · exact ⟨false, by simp [bitOff, h]⟩
        · exact ⟨true, by simp [bitOff, h]⟩
      obtain ⟨t2, ht2⟩ : ∃ t2 : Bool, y'.1 2 = 2 * x.1 2 - bitOff t2 := by
        rcases h2 with h | h
        · exact ⟨false, by simp [bitOff, h]⟩
        · exact ⟨true, by simp [bitOff, h]⟩
      have hy : touchY x.1 (t1, t2) = y'.1 := by
        refine fin_funext_three ?_ ?_ ?_ ?_
        · simp [touchY_zero, hx0, hy0]
        · rw [touchY_one]
          exact ht1.symm
        · rw [touchY_two]
          exact ht2.symm
        · intro j hj
          rw [touchY_of_three hj, h3 j hj]
      refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨Sum.inr (t1, t2),
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hx0⟩, ?_⟩)
      rw [bigStep_inr hx0]
      congr 1
      exact Subtype.ext hy
  · intro hb
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hb)
    have hu' : bigPre x u := (Finset.mem_filter.1 hu).2
    rcases u with p | t
    · have hp : (x.1 + (Pi.single p.1 (sgn p.2) : Fin (k+3) → ℤ)) 0 ≤ 0 := hu'
      rw [bigStep_inl hp]
      exact (tangent_inl_inl x ⟨x.1 + (Pi.single p.1 (sgn p.2) : Fin (k+3) → ℤ), hp⟩).2
        (sum_sq_sub_single x.1 p.1 p.2)
    · have ht : x.1 0 = 0 := hu'
      rw [bigStep_inr ht]
      refine (tangent_inl_inr x ⟨touchY x.1 t, touchY_mem ht t⟩).2 ⟨ht, ?_, ?_, ?_, ?_⟩
      · simp [touchY_zero, ht]
      · rcases t with ⟨t1, t2⟩
        cases t1 <;> simp [touchY_one, bitOff]
      · rcases t with ⟨t1, t2⟩
        cases t2 <;> simp [touchY_two, bitOff]
      · intro j hj
        exact touchY_of_three hj

private lemma nbrs_inr_eq (y : SmallIdx k) : nbrs (.inr y) = ↑(smallNbrs y) := by
  ext b
  constructor
  · intro hb
    rcases b with x' | y'
    · obtain ⟨hx0, hy0, h1, h2, h3⟩ := (tangent_inl_inr x' y).1 ((tangent_comm _ _).1 hb)
      refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨Sum.inr (),
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hy0⟩, ?_⟩)
      rw [smallStep_inr hy0]
      congr 1
      refine Subtype.ext (fin_funext_three ?_ ?_ ?_ ?_)
      · show halfUp y.1 0 = x'.1 0
        rw [halfUp_zero hy0, hx0]
      · show (y.1 1 + 1) / 2 = x'.1 1
        rcases h1 with h | h <;> omega
      · show (y.1 2 + 1) / 2 = x'.1 2
        rcases h2 with h | h <;> omega
      · intro j hj
        have := h3 j hj
        show (y.1 j + 1) / 2 = x'.1 j
        omega
    · obtain ⟨i, c, hi⟩ := exists_single_of_sum_sq ((tangent_inr_inr y y').1 hb)
      have hv : smallPre y (.inl (i, c)) := by
        show 0 ≤ (y.1 + (Pi.single i (sgn c) : Fin (k+3) → ℤ)) 0 ∧
          ∀ j : Fin (k+3), 3 ≤ j.val → Even ((y.1 + (Pi.single i (sgn c) : Fin (k+3) → ℤ)) j)
        rw [← hi]
        exact y'.2
      refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨Sum.inl (i, c),
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hv⟩, ?_⟩)
      rw [smallStep_inl hv]
      congr 1
      exact Subtype.ext hi.symm
  · intro hb
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hb)
    have hu' : smallPre y u := (Finset.mem_filter.1 hu).2
    rcases u with p | u
    · have hp : 0 ≤ (y.1 + (Pi.single p.1 (sgn p.2) : Fin (k+3) → ℤ)) 0 ∧
          ∀ j : Fin (k+3), 3 ≤ j.val → Even ((y.1 + (Pi.single p.1 (sgn p.2) : Fin (k+3) → ℤ)) j) := hu'
      rw [smallStep_inl hp]
      exact (tangent_inr_inr y _).2 (sum_sq_sub_single y.1 p.1 p.2)
    · have hy : y.1 0 = 0 := hu'
      rw [smallStep_inr hy]
      refine (tangent_comm _ _).1 ((tangent_inl_inr ⟨halfUp y.1, halfUp_le hy⟩ y).2
        ⟨halfUp_zero hy, hy, ?_, ?_, ?_⟩)
      · show y.1 1 = 2 * ((y.1 1 + 1) / 2) ∨ y.1 1 = 2 * ((y.1 1 + 1) / 2) - 1
        omega
      · show y.1 2 = 2 * ((y.1 2 + 1) / 2) ∨ y.1 2 = 2 * ((y.1 2 + 1) / 2) - 1
        omega
      · intro j hj
        obtain ⟨m, hm⟩ := y.2.2 j hj
        show y.1 j = 2 * ((y.1 j + 1) / 2)
        omega

theorem nbrs_finite (a : Idx k) : (nbrs a).Finite := by
  rcases a with x | y
  · rw [nbrs_inl_eq x]
    exact Finset.finite_toSet _
  · rw [nbrs_inr_eq y]
    exact Finset.finite_toSet _

theorem ncard_nbrs_le (a : Idx k) : (nbrs a).ncard ≤ 2 * (k + 3) + 4 := by
  rcases a with x | y
  · rw [nbrs_inl_eq x, Set.ncard_coe_finset]
    refine (Finset.card_image_le.trans (Finset.card_le_univ _)).trans ?_
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    omega
  · rw [nbrs_inr_eq y, Set.ncard_coe_finset]
    refine (Finset.card_image_le.trans (Finset.card_le_univ _)).trans ?_
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_unique,
      Fintype.card_bool]
    omega

/-- `levelValue` is harmonic for simple random walk on the tangency graph. -/
theorem sum_levelValue_sub_eq_zero (a : Idx k) :
    ∑ b ∈ (nbrs_finite a).toFinset, (levelValue k b - levelValue k a) = 0 := by
  rcases a with x | y
  · rw [sum_toFinset_eq (nbrs_finite _) (nbrs_inl_eq x), bigNbrs,
      Finset.sum_image (bigStep_injOn x)]
    exact sum_big x
  · rw [sum_toFinset_eq (nbrs_finite _) (nbrs_inr_eq y), smallNbrs,
      Finset.sum_image (smallStep_injOn y)]
    exact sum_small y

end SpherePackings.Counterexample
