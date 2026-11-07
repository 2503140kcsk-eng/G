import Lake
open Lake DSL

package «G» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.36.0-rc2"

lean_lib AlgebraicClosure where
  srcDir := "lean"

lean_lib EPlusPi where
  srcDir := "lean"
