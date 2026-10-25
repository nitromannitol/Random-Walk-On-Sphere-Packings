import Lake

open Lake DSL

package «random-walk-on-sphere-packings» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "065356127b1dc0016f66b7283ce0ce2c4055aa55"

/-- The formalization of Theorem A and Theorem B(a) by leobon12
(https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne),
copied with an acknowledgment header in each file (and, in 13 walk files, `omit [Fintype V] in`
before declarations that do not use finiteness). -/
lean_lib «BouRabeeGwynne» where
  globs := #[.submodules `BouRabeeGwynne]

/-- The comparator audit surface.  Not a default target: `lake build SpherePackingsAudit`. -/
lean_lib «SpherePackingsAudit» where
  globs := #[.submodules `SpherePackingsAudit]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

@[default_target]
lean_lib «SpherePackings» where
  globs := #[.andSubmodules `SpherePackings]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.unusedVariables, true⟩,
    ⟨`linter.unusedSectionVars, true⟩,
    ⟨`linter.unusedSimpArgs, true⟩,
    ⟨`linter.unnecessarySimpa, true⟩,
    ⟨`linter.deprecated, true⟩
  ]
