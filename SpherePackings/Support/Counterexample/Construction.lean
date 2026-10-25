module

public import BouRabeeGwynne.PaperObjects

@[expose] public section

/-!
# The sphere packing of Theorem 6.1

Section 6 of the paper (`rw-spheres.tex:1775-1887`).  A *sphere packing* is a family of spheres
with disjoint open balls; its *tangency graph* joins two spheres when they touch.

The packing lives in dimension `k + 3`.  Big spheres of radius `1` sit at `2x` for `x ∈ ℤ^{k+3}` with
`x₀ ≤ 0`; small spheres of radius `1/2` sit at `(√7/2, 1/2, 1/2, 0, …, 0) + y` for `y ∈ ℤ^{k+3}` with
`y₀ ≥ 0` and `y_j` even for `j ≥ 3`.  For `k = 0` (dimension three) this is the paper's packing.  In
dimension at least four the paper allows every `y ∈ ℤ^d`, but then a small sphere with an odd
coordinate beyond the third touches no big sphere and the hitting-probability computation of the
paper fails; requiring those coordinates to be even restores it.

The level `x₀` of a big sphere and `y₀ + 1` of a small sphere change by one along the edges that
change them.  The function `levelValue`, equal to `4 x₀` on big spheres and `y₀ + 1` on small ones,
is harmonic for simple random walk: a big sphere at level `0` has one neighbour at level `-1`, four
at level `0` and four at level `1`.  This is the harmonic function behind the paper's computation
of the probability `2/3`.
-/

open Metric

namespace SpherePackings

open BouRabeeGwynne

/-- A sphere packing of `ℝ^d` (Section 1.2.1): spheres with centres `center i` and radii
`radius i > 0` whose open balls are pairwise disjoint. -/
structure SpherePacking (d : ℕ) where
  /-- The index set of the spheres. -/
  ι : Type
  /-- The centre of each sphere. -/
  center : ι → Euc d
  /-- The radius of each sphere. -/
  radius : ι → ℝ
  radius_pos : ∀ i, 0 < radius i
  disjoint : Pairwise fun i j => Disjoint (ball (center i) (radius i)) (ball (center j) (radius j))

namespace SpherePacking

variable {d : ℕ} (P : SpherePacking d)

/-- Adjacency in the tangency graph: two distinct spheres that touch. -/
def Tangent (i j : P.ι) : Prop :=
  i ≠ j ∧ dist (P.center i) (P.center j) = P.radius i + P.radius j

/-- The closed half-space bounded by the hyperplane tangent to the spheres `i` and `j` at their
contact point, on the side of sphere `i`. -/
def tangentHalfspace (i j : P.ι) : Set (Euc d) :=
  {x | inner ℝ (x - P.center i) (P.center j - P.center i) ≤
    P.radius i * dist (P.center i) (P.center j)}

/-- A sphere is *covered* (`rw-spheres.tex:331-333`: the hyperplanes tangent to it at its contact
points bound a bounded `d`-dimensional polytope containing its centre): the half-spaces of its
tangent hyperplanes, on its side, meet in a bounded set.  The intersection always contains the ball
of the sphere, and it is a polytope when the sphere has finitely many neighbours. -/
def Covered (i : P.ι) : Prop :=
  Bornology.IsBounded (⋂ j ∈ {j | P.Tangent i j}, P.tangentHalfspace i j)

end SpherePacking

namespace Counterexample

variable (k : ℕ)

/-- Big spheres: `x ∈ ℤ^{k+3}` with `x₀ ≤ 0`. -/
abbrev BigIdx := {x : Fin (k + 3) → ℤ // x 0 ≤ 0}

/-- Small spheres: `y ∈ ℤ^{k+3}` with `y₀ ≥ 0` and `y_j` even for `j ≥ 3`. -/
abbrev SmallIdx := {y : Fin (k + 3) → ℤ // 0 ≤ y 0 ∧ ∀ j : Fin (k + 3), 3 ≤ j.val → Even (y j)}

/-- All spheres of the packing. -/
abbrev Idx := BigIdx k ⊕ SmallIdx k

/-- The offset `(√7/2, 1/2, 1/2, 0, …, 0)` of the small spheres. -/
noncomputable def smallOffset : Euc (k + 3) :=
  WithLp.toLp 2 fun j => if j.val = 0 then Real.sqrt 7 / 2 else if j.val ≤ 2 then 1 / 2 else 0

/-- Centres: `2x` for a big sphere, `smallOffset + y` for a small one. -/
noncomputable def center : Idx k → Euc (k + 3)
  | .inl x => WithLp.toLp 2 fun j => 2 * (x.1 j : ℝ)
  | .inr y => smallOffset k + WithLp.toLp 2 fun j => (y.1 j : ℝ)

/-- Radii: `1` for big spheres, `1/2` for small ones. -/
noncomputable def radius : Idx k → ℝ
  | .inl _ => 1
  | .inr _ => 1 / 2

/-- The harmonic level function: `4 x₀` on a big sphere, `y₀ + 1` on a small one. -/
def levelValue : Idx k → ℤ
  | .inl x => 4 * x.1 0
  | .inr y => y.1 0 + 1

/-- The origin is the centre of the big sphere `x = 0`. -/
def origin : Idx k := .inl ⟨0, le_rfl⟩

end Counterexample

end SpherePackings
