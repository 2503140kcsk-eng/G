import Lake
open Lake DSL

package «G» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.36.0-rc2"

@[default_target]
lean_lib AlgebraicClosure where
  srcDir := "lean"

@[default_target]
lean_lib HermiteLindemannBridge where
  srcDir := "lean"

@[default_target]
lean_lib EPlusPi where
  srcDir := "lean"

@[default_target]
lean_lib LindemannAlgebraicPart where
  srcDir := "lean"

@[default_target]
lean_lib LindemannBasic where
  srcDir := "lean"

@[default_target]
lean_lib SchanuelConditional where
  srcDir := "lean"

@[default_target]
lean_lib ProofAudit where
  srcDir := "lean"
