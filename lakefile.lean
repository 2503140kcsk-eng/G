import Lake
open Lake DSL

package g

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "6526be50929d52688b64ed3fdc96be4d04507415"

lean_lib G where
  srcDir := "lean"
  roots := #[
    Lean.Name.mkSimple "EPlusPi",
    Lean.Name.mkSimple "MixedKernelQuotient",
    Lean.Name.mkSimple "ProofAudit"
  ]
