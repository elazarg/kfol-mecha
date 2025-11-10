import Lake
open Lake DSL

package «kfol-mecha» where
  moreLeanArgs := #["-Dlinter.missingDocs=false"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @
    "2521caa75cc243e9583e19a8b050d68961e622cf"

@[default_target]
lean_lib KFOL where
  roots := #[
    `KFOL,
    `KFOL.Core.Language,
    `KFOL.Core.BinderGame,
    `KFOL.Core.Assignment,
    `KFOL.Core.Observation,
    `KFOL.Core.Strategy,
    `KFOL.Core.Eval,
    `KFOL.Core.Permutation,
    `KFOL.Core.Forceability
  ]

lean_exe «kfol-mecha» where
  root := `Main
