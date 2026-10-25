module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/FiberCalculus.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.FiberEndpoints
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-! Fundamental theorem of calculus on the actual nonempty polytope fibers. -/

open MeasureTheory

namespace BouRabeeGwynne.ConvexPolytope

variable {d : ℕ} (P : ConvexPolytope d)

/-- Integrating a directional derivative along an actual cell fiber gives the
difference of the values at its two actual boundary endpoints. -/
theorem integral_fderiv_fiber_eq_sub
    {e : Euc d} (he : e ≠ 0) (y : Euc d)
    (hy : P.parallelConstraintsHold e y)
    (hbounds : P.lowerFiber e he y ≤ P.upperFiber e he y)
    {W : Set (Euc d)} (hW : IsOpen W) (hPW : P.carrier ⊆ W)
    {h : Euc d → ℝ} (hh : ContDiffOn ℝ 1 h W) :
    (∫ t in P.lowerFiber e he y..P.upperFiber e he y,
      (fderiv ℝ h (y + t • e)) e) =
      h (P.upperEndpoint e he y) - h (P.lowerEndpoint e he y) := by
  have hpath : Continuous (fun t : ℝ => y + t • e) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hpathW : Set.MapsTo (fun t : ℝ => y + t • e)
      (Set.Icc (P.lowerFiber e he y) (P.upperFiber e he y)) W := by
    intro t ht
    exact hPW ((P.mem_line_iff he y t).mpr ⟨hy, ht.1, ht.2⟩)
  have hcont : ContinuousOn (fun t : ℝ => (fderiv ℝ h (y + t • e)) e)
      (Set.Icc (P.lowerFiber e he y) (P.upperFiber e he y)) :=
    ((hh.continuousOn_fderiv_of_isOpen hW le_rfl).clm_apply continuousOn_const).comp
      hpath.continuousOn hpathW
  have hint : IntervalIntegrable (fun t : ℝ => (fderiv ℝ h (y + t • e)) e)
      MeasureTheory.volume (P.lowerFiber e he y) (P.upperFiber e he y) :=
    hcont.intervalIntegrable_of_Icc hbounds
  have hderiv : ∀ t ∈ Set.uIcc (P.lowerFiber e he y) (P.upperFiber e he y),
      HasDerivAt (fun t : ℝ => h (y + t • e)) ((fderiv ℝ h (y + t • e)) e) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (P.lowerFiber e he y) (P.upperFiber e he y) := by
      simpa only [Set.uIcc_of_le hbounds] using ht
    have hD := (hh.differentiableOn (by norm_num)).differentiableAt (hW.mem_nhds (hpathW ht'))
    have hline := ((ContinuousLinearMap.toSpanSingleton ℝ e).hasFDerivAt (x := t)).const_add y
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
      (hD.hasFDerivAt.comp t hline).hasDerivAt
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

end BouRabeeGwynne.ConvexPolytope
