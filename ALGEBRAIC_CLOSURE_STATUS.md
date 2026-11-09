# Algebraic elements and algebraic closure: formalization status

**Snapshot:** 2026-11-09  
**Lean toolchain:** leanprover/lean4:v4.36.0-rc2  
**Mathlib:** v4.36.0-rc2

## Scope and assumptions

Let K and E be fields and let E be a field extension of K. The algebraic elements are

A = {x in E | there exists p in K[X], p != 0, and p(x) = 0}.

The target field is the relative algebraic closure algebraicClosure K E, whose carrier is exactly A.

The hypothesis that the ambient field E is algebraically closed is kept explicit. If E is not algebraically closed, its relative algebraic closure need not itself be algebraically closed.

## Formal construction

G/AlgebraicElements.lean packages these results:

1. field_structure: the field structure inherited by the algebraic elements.
2. mem_iff: x belongs to algebraicClosure K E iff IsAlgebraic K x.
3. carrier_eq: the carrier is exactly the set of algebraic elements.
4. add_closed, neg_closed, sub_closed, mul_closed, inv_closed, div_closed, zpow_closed: closure under all field operations, including inversion and every integer power.
5. field_is_algebraic: the resulting intermediate field is algebraic over K.
6. maximality: an intermediate field L lies inside it iff L/K is algebraic.
7. Under IsAlgClosed E, isAlgClosure_of_algClosed_ambient identifies it as an algebraic closure; field_isAlgClosed, every_polynomial_splits, and exists_root expose algebraic closedness.
8. uniqueness_up_to_algEquiv: any two algebraic closures of the same base field are isomorphic over the base.

## Proof architecture

This is a proof-engineering contribution, not a claim of a new theorem in field theory.

The compact construction is:

- represent the carrier as an IntermediateField, which already packages the field operations;
- identify membership with algebraicity using mem_algebraicClosure_iff;
- transport each closure law through that equivalence;
- obtain algebraicity, maximality, algebraic closedness, polynomial splitting, and uniqueness from the corresponding mathlib constructions.

This is stronger and safer than independently rebuilding all field axioms from minimal-polynomial calculations: the kernel checks the transported statements, while the underlying mathlib declarations are the trusted proof dependencies.

## Trust and verification

- No project axiom, sorry, or admit is introduced.
- G/AxiomAudit.lean prints axiom dependencies for every exported theorem in this formalization.
- .github/workflows/lean.yml runs the Lean kernel build, nanoda with sorry disallowed, and the axiom audit.
- The allowlist is restricted to Lean's expected foundational axioms: propext, Classical.choice, and Quot.sound.
- The first successful Lake build compiled all project modules (4,086 Lake jobs). The explicit #print axioms output for each theorem listed at that revision contained only the three allowed foundational axioms.
- LeanChecker was tested, including with LEAN_NUM_THREADS=1 as recommended by lean-action for Mathlib-dependent projects, but the GitHub-hosted runner process exited with code 139. This independent checker is therefore not part of the required CI job. This is a runner/tool limitation observed in the run, not a Lean proof error.

A successful GitHub Actions run for the current head is still required to confirm nanoda and axiom-audit. The presence of the workflow alone is not a passing test.

## Tool and repository work allocation

| Resource | Assigned role | What it can establish |
|---|---|---|
| GitHub | versioned changes, branch/PR, CI logs | repository state and reproducible verification |
| Sider Scholar | academic discovery | source discovery, not kernel proof |
| Parallel Search | current documentation/source cross-check | locate and compare authoritative references |
| Context7 | version-matched Lean/mathlib API guidance | API details; not proof verification |
| Wolfram | symbolic and example-level checks | computational corroboration only |
| Macaulay2 | polynomial ideals, elimination and resultants | exploratory algebra |
| GAP | finite groups and Galois-group experiments | finite examples and group computations |
| SymPy | symbolic polynomials and resultants | exploratory counterexample/candidate discovery |
| SageMath | exact number fields, embeddings and minimal polynomials | independent computational experiments |
| Naproche | natural-language proof structuring | proof-plan checking, not Lean kernel verification |
| cvc5 | SMT checks of bounded algebraic identities | bounded checking, not universal field-theory proof |
| LeanDojo-v2 | premise retrieval and tactic exploration | proof-search suggestions, not a trusted kernel |
| mathlib4 | formal algebra and algebraic-closure library | primary reusable kernel-checked theorems |

The starred repositories above are those identified in the existing project context; this is not a live enumeration of every item in the account's GitHub Stars page.
