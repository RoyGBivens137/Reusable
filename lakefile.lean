import Lake
open Lake DSL

package NCG where
  leanOptions := #[
    ⟨`linter.unnecessarySimpa, false⟩,
    ⟨`linter.unusedTactic, false⟩,
    ⟨`linter.flexible, false⟩,
    ⟨`linter.unnecessarySeqFocus, false⟩,
    ⟨`linter.unreachableTactic, false⟩,
    ⟨`linter.style.show, false⟩,
    ⟨`linter.unusedSimpArgs, false⟩,
    ⟨`linter.style.commandStart, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib FourierBochner

lean_lib SheafOfLocalMeans
