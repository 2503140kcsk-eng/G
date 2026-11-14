import Lake
open Lake DSL

package «G» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.36.0-rc2"

@[default_target]
lean_lib AlgebraicClosure where
  srcDir := "lean"

@[default_target]
lean_lib AlgebraicElements where
  srcDir := "lean"

@[default_target]
lean_lib AlgebraicFieldClosure where
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
lean_lib ApproximationCriteria where
  srcDir := "lean"

lean_lib ProofAuditDefs where
  srcDir := "lean"

@[default_target]
lean_lib MixedKernelQuotient where
  srcDir := "lean"

@[default_target]
lean_lib PairedApproximationCriteria where
  srcDir := "lean"

@[default_target]
lean_lib PolynomialApproximationDefs where
  srcDir := "lean"

@[default_target]
lean_lib SimultaneousPolynomialApproximation where
  srcDir := "lean"

@[default_target]
lean_lib ProofAuditApprox where
  srcDir := "lean"

@[default_target]
lean_lib CommonDenominatorApproximationDefs where
  srcDir := "lean"

@[default_target]
lean_lib CommonDenominatorApproximation where
  srcDir := "lean"

@[default_target]
lean_lib ProofAudit where
  srcDir := "lean"

-- The Comparator challenge intentionally contains sorry placeholders.
-- It is excluded from default builds and used only by the lake comparator command.
lean_lib ProofAuditChallenge where
  srcDir := "lean"
