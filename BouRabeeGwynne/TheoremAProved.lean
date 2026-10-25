module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/TheoremAProved.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.TheoremAStatement
public import BouRabeeGwynne.TheoremAProcessLaws
public import BouRabeeGwynne.UniformStoppedWalkConvergence

@[expose] public section

/-! Theorem A with its approved statement unchanged: existence of the actual
process laws and uniform convergence of the stopped conductance walks. -/

open MeasureTheory
open scoped ENNReal Topology

namespace BouRabeeGwynne

theorem theoremA_proved : TheoremAStatement := by
  intro d hd G N U hU hUb hUD happrox hreg
  obtain ⟨μ, hμ, hBrownian⟩ :=
    exists_standardBrownianLaw_with_stopped_laws hd hU.isDomain.1 hUb
  obtain ⟨walkLaw, hwalk⟩ := N.exists_eventually_stoppedWalkLaws hd U hUb hUD happrox
  refine ⟨μ, hμ, hBrownian, walkLaw, ?_, ?_⟩
  · filter_upwards [hwalk] with n hn
    intro z _
    exact hn z
  · intro η hη
    filter_upwards [hwalk, N.eventually_stoppedWalkLaw_levyProkhorov_le hd
      hU.isDomain.1 hU.hasLipschitzBoundary hUb hUD happrox hreg hμ hη] with n hn hconv
    intro z hz
    exact hconv z hz (walkLaw n z) (hn z)

end BouRabeeGwynne
