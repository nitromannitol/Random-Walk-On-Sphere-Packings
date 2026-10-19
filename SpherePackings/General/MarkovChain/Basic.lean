-- Adapted from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (files `BouRabeeGwynne/StoppedWalk.lean`, `WalkMemoryless.lean`, `WalkJointRestart.lean` and
-- `WalkStrongMarkov.lean` at commit cf73d6e): the walk of a finite conductance network is replaced
-- by the chain of an arbitrary Markov kernel on a measurable space.
import BouRabeeGwynne.WalkStrongMarkov

/-!
# The Markov chain of a Markov kernel

For a Markov kernel `κ` on a measurable space `V`, `law κ a` is the law on `ℕ → V` of the
time-homogeneous Markov chain with transition kernel `κ` started at `a` (Ionescu–Tulcea).  This
file proves its time-homogeneity, the Markov property at deterministic times and at stopping times,
and the first-step decomposition.  Nothing here depends on the paper.
-/

open MeasureTheory ProbabilityTheory Set Preorder
open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork

namespace SpherePackings.MarkovChain

variable {V : Type*} [MeasurableSpace V] (κ : Kernel V V) [IsMarkovKernel κ]

/-- At time `n` the next state depends only on the last state of the history. -/
noncomputable def historyKernel (n : ℕ) : Kernel (Finset.Iic n → V) V :=
  κ.comap (fun h ↦ h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _)

instance historyKernel_isMarkovKernel (n : ℕ) : IsMarkovKernel (historyKernel κ n) := by
  unfold historyKernel
  infer_instance

/-- The law of the chain started at `a`. -/
noncomputable def law (a : V) : Measure (ℕ → V) :=
  Kernel.trajMeasure (X := fun _ => V) (Measure.dirac a) (historyKernel κ)

instance law_isProbabilityMeasure (a : V) : IsProbabilityMeasure (law κ a) := by
  unfold law
  infer_instance

/-- The law of the chain as a kernel in the starting state. -/
noncomputable def pathKernel : Kernel V (ℕ → V) :=
  (Kernel.traj (X := fun _ => V) (historyKernel κ) 0).comap
    (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => V)).symm
    (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => V)).symm.measurable

lemma pathKernel_apply (a : V) : pathKernel κ a = law κ a := by
  rw [pathKernel, Kernel.comap_apply, law, Kernel.trajMeasure, Measure.map_dirac' (by fun_prop)]
  exact (Measure.dirac_bind (Kernel.measurable _) _).symm

instance pathKernel_isMarkovKernel : IsMarkovKernel (pathKernel κ) := by
  unfold pathKernel
  infer_instance

lemma law_initialHistory (a : V) :
    (law κ a).map (frestrictLe 0) = Measure.dirac (fun _ => a) := by
  rw [← pathKernel_apply, pathKernel, Kernel.comap_apply]
  rw [TrajectoryCoupling.prefix_at_start_traj (historyKernel κ) 0]
  congr 1

/-- Each finite future prefix of the continuation from a history has the law of a fresh chain
started from the last state of the history. -/
lemma continuation_shiftPrefix_law (n : ℕ) (h : Finset.Iic n → V) (k : ℕ) :
    ((Kernel.traj (X := fun _ => V) (historyKernel κ) n h).map
      (frestrictLe (n + k))).map (TrajectoryCoupling.shiftPrefix n k) =
      (law κ (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)).map (frestrictLe k) := by
  induction k with
  | zero =>
    change ((Kernel.traj (X := fun _ => V) (historyKernel κ) n h).map
      (frestrictLe n)).map (TrajectoryCoupling.shiftPrefix n 0) = _
    rw [TrajectoryCoupling.prefix_at_start_traj (historyKernel κ) n h,
      Measure.map_dirac' (TrajectoryCoupling.measurable_shiftPrefix n 0), law_initialHistory, TrajectoryCoupling.shiftPrefix_zero]
  | succ k ih =>
    change ((Kernel.traj (X := fun _ => V) (historyKernel κ) n h).map
      (frestrictLe (n + k + 1))).map (TrajectoryCoupling.shiftPrefix n (k + 1)) = _
    have htarget := TrajectoryCoupling.prefix_succ
      (Measure.dirac (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)) (historyKernel κ) k
    change (law κ (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)).map (frestrictLe (k + 1)) = _ at htarget
    have hmap (q : Finset.Iic (n + k) → V) :
        (historyKernel κ (n + k) q).map id = historyKernel κ k (TrajectoryCoupling.shiftPrefix n k q) := by
      rw [Measure.map_id]
      rfl
    rw [TrajectoryCoupling.prefix_succ_traj (historyKernel κ) n (n + k) (Nat.le_add_right _ _) h, htarget,
      Measure.map_map (TrajectoryCoupling.measurable_shiftPrefix n (k + 1)) (TrajectoryCoupling.measurable_append (n + k)),
      TrajectoryCoupling.shiftPrefix_append,
      ← Measure.map_map (TrajectoryCoupling.measurable_append k) ((TrajectoryCoupling.measurable_shiftPrefix n k).prodMap measurable_id),
      compProd_map_prod_of_kernel_map _ _ _ _ _ (TrajectoryCoupling.measurable_shiftPrefix n k) measurable_id hmap,
      ih]
    rfl

/-- The whole future after time `n` of the continuation from a history is a fresh chain started
from the last state of the history. -/
theorem continuation_walkShift_law (n : ℕ) (h : Finset.Iic n → V) :
    (Kernel.traj (X := fun _ => V) (historyKernel κ) n h).map (walkShift n) =
      law κ (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) := by
  apply TrajectoryCoupling.measure_eq_of_prefix_eq
  intro k
  rw [Measure.map_map (measurable_frestrictLe k) (measurable_walkShift n)]
  have heq : frestrictLe (π := fun _ : ℕ => V) k ∘ walkShift n =
      TrajectoryCoupling.shiftPrefix n k ∘ frestrictLe (π := fun _ : ℕ => V) (n + k) := rfl
  rw [heq, ← Measure.map_map (TrajectoryCoupling.measurable_shiftPrefix n k) (measurable_frestrictLe (n + k))]
  exact continuation_shiftPrefix_law κ n h k

/-- The future kernel from a finite history. -/
noncomputable def restartKernel (n : ℕ) : Kernel (Finset.Iic n → V) (ℕ → V) :=
  (pathKernel κ).comap (fun h => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _)

instance restartKernel_isMarkovKernel (n : ℕ) : IsMarkovKernel (restartKernel κ n) := by
  unfold restartKernel
  infer_instance

lemma continuation_map_walkShift (n : ℕ) :
    (Kernel.traj (X := fun _ => V) (historyKernel κ) n).map (walkShift n) = restartKernel κ n := by
  ext h : 1
  rw [Kernel.map_apply _ (measurable_walkShift n), restartKernel, Kernel.comap_apply,
    pathKernel_apply]
  exact continuation_walkShift_law κ n h

/-- The Markov property at a deterministic time: the joint law of the prefix up to time `n` and
of the whole future after time `n`. -/
theorem law_prefix_future (a : V) (n : ℕ) :
    (law κ a).map (frestrictLe n) ⊗ₘ restartKernel κ n =
      (law κ a).map (fun ω => (frestrictLe n ω, walkShift n ω)) := by
  rw [← continuation_map_walkShift κ n, Measure.compProd_map (measurable_walkShift n)]
  have hp := TrajectoryCoupling.prefix_compProd_traj (Measure.dirac a) (historyKernel κ) n
  change (law κ a).map (frestrictLe n) ⊗ₘ Kernel.traj (X := fun _ => V) (historyKernel κ) n = _
    at hp
  rw [hp, Measure.map_map (measurable_id.prodMap (measurable_walkShift n)) (by fun_prop)]
  rfl

/-- The state at time one has law `κ a`. -/
lemma law_map_eval_one (a : V) : (law κ a).map (fun ω => ω 1) = κ a := by
  have h := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ => V) (μ₀ := Measure.dirac a) (κ := historyKernel κ) (a := 0)
  have h2 := congrArg Measure.snd h
  rw [Measure.snd_compProd, Measure.snd_map_prodMk (measurable_frestrictLe 0)] at h2
  change (historyKernel κ 0) ∘ₘ ((law κ a).map (frestrictLe 0)) =
    (law κ a).map (fun x => x 1) at h2
  rw [← h2, law_initialHistory, Measure.dirac_bind (Kernel.measurable _)]
  · rfl
  · exact measurable_pi_apply _

lemma comp_comap_eq_comp_map {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] (η : Kernel Y Z) {f : X → Y} (hf : Measurable f) (μ : Measure X) :
    η.comap f hf ∘ₘ μ = η ∘ₘ μ.map f := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.measurable _).aemeasurable,
    Measure.bind_apply hs (Kernel.measurable _).aemeasurable,
    lintegral_map (Kernel.measurable_coe _ hs) hf]
  rfl

/-- The first-step decomposition: after one step the chain is a fresh chain started at the
state at time one. -/
theorem law_map_walkShift_one (a : V) :
    (law κ a).map (walkShift 1) = pathKernel κ ∘ₘ κ a := by
  have h := congrArg Measure.snd (law_prefix_future κ a 1)
  rw [Measure.snd_compProd, Measure.snd_map_prodMk (measurable_frestrictLe 1)] at h
  rw [← h, restartKernel, comp_comap_eq_comp_map,
    Measure.map_map (g := fun h : Finset.Iic 1 → V => h ⟨1, Finset.mem_Iic.mpr le_rfl⟩)
      (measurable_pi_apply _) (measurable_frestrictLe 1)]
  · congr 1
    exact law_map_eval_one κ a
  · exact measurable_walkShift 1

/-- First-step decomposition of an integral over the path after time one. -/
theorem lintegral_walkShift_one (a : V) {F : (ℕ → V) → ENNReal} (hF : Measurable F) :
    ∫⁻ ω, F (walkShift 1 ω) ∂law κ a = ∫⁻ b, ∫⁻ ω, F ω ∂law κ b ∂κ a := by
  rw [← lintegral_map hF (measurable_walkShift 1), law_map_walkShift_one,
    Measure.lintegral_bind (Kernel.aemeasurable _) hF.aemeasurable]
  simp_rw [pathKernel_apply]

theorem integral_walkShift_one (a : V) {F : (ℕ → V) → ℝ} (hF : Measurable F)
    {C : ℝ} (hC : ∀ ω, |F ω| ≤ C) :
    ∫ ω, F (walkShift 1 ω) ∂law κ a = ∫ b, ∫ ω, F ω ∂law κ b ∂κ a := by
  rw [← integral_map (measurable_walkShift 1).aemeasurable hF.aestronglyMeasurable,
    law_map_walkShift_one]
  have hcomp : pathKernel κ ∘ₘ κ a = (pathKernel κ ∘ₖ κ) a := (Kernel.comp_apply _ _ _).symm
  rw [hcomp, Kernel.integral_comp]
  · simp_rw [pathKernel_apply]
  · exact (integrable_const C).mono' hF.aestronglyMeasurable
      (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hC ω)

end SpherePackings.MarkovChain
