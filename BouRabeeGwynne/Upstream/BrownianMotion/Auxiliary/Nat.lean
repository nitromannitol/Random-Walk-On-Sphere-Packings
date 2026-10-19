-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/Upstream/BrownianMotion/Auxiliary/Nat.lean` at commit cf73d6e); unchanged apart from this header.
/-
Vendored from RemyDegenne/brownian-motion, commit
314f04a34ff75e18fd383917ae7fe7d77beb1b6f.
Adaptation: local import paths only. The original Apache-2.0 license and
authorship are retained; see Upstream/BrownianMotion/PROVENANCE.md.
-/
module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Ring.Abs

@[expose] public section

lemma pow_two_mul_abs {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] (n : ℕ) (a : α) :
    |a| ^ (2 * n) = a ^ (2 * n) :=
  Even.pow_abs ⟨n, two_mul n⟩ a

