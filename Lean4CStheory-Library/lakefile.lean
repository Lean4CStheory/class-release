import Lake
open Lake DSL

package «Lean4CStheory» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.24.0"

@[default_target]
lean_lib Lean4CStheory where
  srcDir := "src"
