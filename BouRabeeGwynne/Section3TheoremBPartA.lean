module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/Section3TheoremBPartA.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.Section3PlanarTarget
public import BouRabeeGwynne.Section3CaseIITarget
public import BouRabeeGwynne.Section3CaseIIITarget

@[expose] public section

/-! Theorem B(a) from the three actual geometric regularity cases. -/

namespace BouRabeeGwynne

/-- The approved Theorem B(a) statement, with actual tilings, continuum
harmonic functions and finite discrete Dirichlet solutions throughout. -/
theorem theoremB_part_a : TheoremBPartAStatement := by
  intro d G N U hC hd _hDomain hU hUD happrox hreg hh
  rcases hreg with hI | hII | hIII
  · have hd2 : d = 2 := hI
    subst d
    exact theoremB_part_a_planar G N U hC hU hUD happrox hh
  · exact theoremB_part_a_caseII hd G N U hC hU hUD happrox hII hh
  · exact theoremB_part_a_caseIII hd G N U hC hU hUD happrox hIII hh

end BouRabeeGwynne
