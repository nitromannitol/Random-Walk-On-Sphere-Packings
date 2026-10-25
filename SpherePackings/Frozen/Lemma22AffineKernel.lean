module

/-
Lemma 2.2 of rw-spheres.tex, frozen.

Paper statement, `rw-spheres.tex:657-659` (label `lemma:linear-lie-in-kernel`): for every
`p ∈ ℝ^d` and `c ∈ ℝ`, the affine function `ℓ_p(x) = p ⬝ x + c` satisfies `Δ_a ℓ_p = 0`.

Corrected statement (`rw-spheres-corrected.tex`, Correction 4): at every vertex whose cell is
complete (finitely many neighbours, and every boundary point of the cell lies in the cell of a
neighbour).  The published identity is false at a cell with a facet shared with no other cell (two
unit squares: `ℓ(x) = x₁` has discrete Laplacian `1` at the left square).  Proved from leobon12's
polytope Gauss–Green identity.
-/
public import SpherePackings.Support.Section2.AffineKernel

@[expose] public section

open BouRabeeGwynne SpherePackings

-- FROZEN-STATEMENT-BEGIN
theorem SpherePackings.Frozen.lemma22_affine_kernel {d : ℕ} (hd : 1 ≤ d) (T : OrthogonalTiling d)
    (v : T.V) (hv : CompleteCell T v) (p : Euc d) (c : ℝ) :
    T.discreteLaplacian (fun w => inner ℝ p (T.pos w) + c) v hv.1 = 0
-- FROZEN-STATEMENT-END
:= SpherePackings.discreteLaplacian_affine_eq_zero_of_complete hd T v hv p c
