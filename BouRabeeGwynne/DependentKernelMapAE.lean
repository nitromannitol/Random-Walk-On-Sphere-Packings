module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/DependentKernelMapAE.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.DependentKernelMap

@[expose] public section

/-! A joint past-dependent map may intertwine transition rows almost surely;
the irrelevant invalid histories need not satisfy the row identity. -/

open MeasureTheory ProbabilityTheory Set

namespace BouRabeeGwynne

lemma compProd_map_dependent_of_kernel_map_ae
    {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D]
    (μ : Measure A) [SFinite μ] (κ : Kernel A B) [IsSFiniteKernel κ]
    (η : Kernel C D) [IsSFiniteKernel η]
    (f : A → C) (g : A → B → D) (hf : Measurable f)
    (hg : Measurable (fun p : A × B => g p.1 p.2))
    (hmap : ∀ᵐ a ∂μ, (κ a).map (g a) = η (f a)) :
    (μ ⊗ₘ κ).map (fun p => (f p.1, g p.1 p.2)) = μ.map f ⊗ₘ η := by
  have hp : Measurable (fun p : A × B => (f p.1, g p.1 p.2)) :=
    (hf.comp measurable_fst).prodMk hg
  ext s hs
  rw [Measure.map_apply hp hs, Measure.compProd_apply (hp hs),
    Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  apply lintegral_congr_ae
  filter_upwards [hmap] with a ha
  have hga : Measurable (g a) := hg.comp (measurable_const.prodMk measurable_id)
  rw [← ha, Measure.map_apply hga (measurable_prodMk_left hs)]
  rfl

end BouRabeeGwynne
