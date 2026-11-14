module
public import Mathlib

@[expose] public section

/-!
# Shared, Mathlib-only statement definition for Schanuel's conjecture

This file contains a proposition definition only: no axioms, theorems,
proof holes, project-specific imports, or non-Mathlib dependencies.
The independent Comparator Challenge and the solution both import this
same file so that the exact statement constant is shared without relying
on unfolding implementation-local aliases.
-/

namespace ProofAuditDefs

/-- Schanuel's conjecture in the standard transcendence-degree formulation. -/
def SchanuelConjecture : Prop :=
  ∀ (n : ℕ) (z : Fin n → ℂ),
    LinearIndependent ℚ z →
    (n : Cardinal) ≤ Algebra.trdeg ℚ
      (IntermediateField.adjoin ℚ
        (Set.range z ∪ Set.range (fun i : Fin n => Complex.exp (z i))))

end ProofAuditDefs
