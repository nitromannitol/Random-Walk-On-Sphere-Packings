module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/HarmonicCutoff.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.Harmonic
public import Mathlib.Geometry.Manifold.PartitionOfUnity

@[expose] public section

/-! Local harmonic functions have compactly supported C² extensions used
in the stopped Brownian Taylor argument. -/

open Set Function Filter
open scoped Topology

namespace BouRabeeGwynne

/-- Extend a C² function near a compact set by multiplying it by an actual
smooth cutoff. The resulting function agrees on an open neighborhood, so its
derivatives there agree as well. -/
theorem exists_contDiff_compactSupport_eq_near_compact {d : ℕ}
    {K W : Set (Euc d)} (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    {h : Euc d → ℝ} (hh : ContDiffOn ℝ 2 h W) :
    ∃ (g : Euc d → ℝ) (V : Set (Euc d)),
      IsOpen V ∧ K ⊆ V ∧ V ⊆ W ∧ ContDiff ℝ 2 g ∧
      HasCompactSupport g ∧ tsupport g ⊆ W ∧ EqOn g h V := by
  obtain ⟨L, hL, hKL, hLW⟩ := exists_compact_between hK hW hKW
  obtain ⟨O, hO, hLO, hOW, hOc⟩ :=
    exists_open_between_and_isCompact_closure hL hW hLW
  obtain ⟨χ, hχ, _, hχsupp, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := 2) hO hL.isClosed hLO
  let g : Euc d → ℝ := fun x => χ x * h x
  have hχcompact : HasCompactSupport χ := by
    simpa only [HasCompactSupport, tsupport, hχsupp] using hOc
  have hgsupport : tsupport g ⊆ W :=
    tsupport_mul_subset_left.trans (by simpa only [tsupport, hχsupp] using hOW)
  have hg : ContDiff ℝ 2 g := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ W
    · exact hχ.contDiffAt.mul (hh.contDiffAt (hW.mem_nhds hx))
    · have hxO : x ∈ (closure O)ᶜ := fun hmem => hx (hOW hmem)
      have heq : g =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxO] with y hy
        have hyO : y ∉ O := fun hy' => hy (subset_closure hy')
        have hχzero : χ y = 0 := by
          apply notMem_support.mp
          simpa only [hχsupp] using hyO
        exact mul_eq_zero_of_left hχzero _
      exact contDiffAt_const.congr_of_eventuallyEq heq
  refine ⟨g, interior L, isOpen_interior, hKL, interior_subset.trans hLW,
    hg, hχcompact.mul_right, hgsupport, ?_⟩
  intro x hx
  change χ x * h x = h x
  rw [(hχone x).mp (interior_subset hx), one_mul]

/-- The compactly supported extension is harmonic on a neighborhood of the
compact set, by locality of the genuine Euclidean Laplacian. -/
theorem IsHarmonicOn.exists_compactSupport_eq_near_compact {d : ℕ}
    {h : Euc d → ℝ} {K W : Set (Euc d)} (hh : IsHarmonicOn h W)
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ (g : Euc d → ℝ) (V : Set (Euc d)),
      IsOpen V ∧ K ⊆ V ∧ V ⊆ W ∧ ContDiff ℝ 2 g ∧
      HasCompactSupport g ∧ tsupport g ⊆ W ∧ EqOn g h V ∧ IsHarmonicOn g V := by
  obtain ⟨g, V, hV, hKV, hVW, hg, hgc, hgs, heq⟩ :=
    exists_contDiff_compactSupport_eq_near_compact hK hW hKW hh.contDiffOn
  refine ⟨g, V, hV, hKV, hVW, hg, hgc, hgs, heq, hg.contDiffOn, ?_⟩
  intro x hx
  have hlocal : g =ᶠ[𝓝 x] h := by
    filter_upwards [hV.mem_nhds hx] with y hy
    exact heq hy
  rw [(InnerProductSpace.laplacian_congr_nhds hlocal).eq_of_nhds]
  exact hh.laplacian_eq_zero (hVW hx)

end BouRabeeGwynne
