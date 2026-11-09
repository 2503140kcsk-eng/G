import Lake
open Lake DSL

package G where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.36.0-rc2"

@[default_target]
lean_lib AlgebraicFieldClosure

-- The Comparator challenge is built separately and is not part of the
-- default library target. It fixes the expected proposition types.
lean_lib AlgebraicFieldClosureChallenge
