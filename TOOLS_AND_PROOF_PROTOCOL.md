# Tool roles and proof-integrity protocol

## Governing principle

Separate three jobs:

1. **Discovery:** find definitions, literature, API declarations, and known theorem statements.
2. **Experiment:** test examples, compute candidate minimal polynomials, and search for counterexamples.
3. **Proof:** establish the universal mathematical statements in Lean and have Lean's kernel check them.

Only the third stage certifies the theorems in this repository. Computer algebra, SMT solvers, search engines, and AI theorem-proving agents can suggest or test arguments, but their output is not accepted as a substitute for a kernel-checked proof.

The resource set below is the set of repositories and integrations named for this task; it is not a claim that every item in the user's entire GitHub Stars list has been enumerated.

## ChatGPT integrations

| Resource | Assigned responsibility | Limit |
|---|---|---|
| GitHub | Inspect this repository and upstream mathlib source, commit on an isolated branch, and run the pinned CI workflow. | Git hosting and CI status do not themselves certify a mathematical proof. |
| Sider Scholar | Discover algebra/field-theory references and cross-check standard terminology and theorem statements. | Search results are leads; source texts and exact hypotheses must be checked. |
| Wolfram | Calculate exact illustrative minimal polynomials and check symbolic transformations in sample number fields. | A finite collection of examples cannot prove a universal statement about every field extension. |
| Context7 | Retrieve current Lean 4 and mathlib documentation, avoiding stale theorem names and signatures. | Documentation helps construct proofs; Lean's elaborator and kernel make the final check. |
| Parallel Search | Independently search academic notes and current technical documentation, and cross-check the proof outline. | Web research is not a proof assistant and can misread or omit hypotheses. |

## User-specified GitHub repositories

| Repository | Assigned responsibility in this project | What it must not be used to claim |
|---|---|---|
| [Macaulay2](https://github.com/Macaulay2/M2) | Explore finitely generated commutative algebras, polynomial ideals, quotient constructions, and computational algebra examples that illuminate algebraic relations. | A Gröbner-basis or ideal computation does not establish the abstract field-extension theorem for all fields. |
| [GAP](https://github.com/gap-system/gap) | Test finite-field examples, finite groups of field automorphisms, and finite Galois-theoretic instances. | Finite examples do not settle arbitrary or infinite field extensions. |
| [SymPy](https://github.com/sympy/sympy) | Check polynomial reversal, rational polynomial identities, and sample minimal-polynomial calculations. | Symbolic simplification or a computed minimal polynomial is not a formal proof in Lean. |
| [SageMath](https://github.com/sagemath/sage) | Compare degrees, bases, and composita of concrete number fields; test the product-of-degrees bound on examples. | Numerical or computational number-field experiments do not prove the theorem for arbitrary base fields. |
| [Naproche](https://github.com/naproche/naproche) | Audit whether the written proof is logically explicit and whether its mathematical prose can be rendered in a proof-checking style. | Its natural-language checking workflow is not a replacement for the Lean kernel proof in this repository. |
| [cvc5](https://github.com/cvc5/cvc5) | Check selected polynomial equalities and bounded logical subproblems after they have been encoded in supported SMT theories. | An SMT result for an encoding is not automatically a theorem about all fields; the encoding and theory axioms would need a separate soundness argument. |
| [LeanDojo-v2](https://github.com/lean-dojo/LeanDojo-v2) | Search Lean/mathlib premises, retrieve related proof traces, and propose tactics or proof candidates if a local, free deployment is available. | An agent's generated tactic or proof candidate is untrusted until Lean elaborates it and the kernel accepts it. |
| [mathlib4](https://github.com/leanprover-community/mathlib4) | Supply the reusable field-theory results and exact APIs used by the formal development: inverse/power closure, finite-dimensional adjoin, and finite-generation/algebraicity results. | The library theorem names still need to be instantiated with the correct hypotheses; a citation to mathlib is not a substitute for the declarations in this project. |

## Comparator verification and trust boundary

The normal CI uses Lean's built-in `lake comparator --config=comparator.json --paranoid`, not the archived standalone Comparator application. The configuration compares the six theorem declarations in `AlgebraicFieldClosure` against the separately maintained statement module `AlgebraicFieldClosureChallenge`, enforces the allowlist `propext`, `Classical.choice`, and `Quot.sound`, and requests all checkers bundled with the pinned Lean toolchain.

This is a targeted theorem check. The challenge module, the Lake configuration, and their transitive imports are part of the trusted boundary. Mathlib is pinned to Lean-compatible version `v4.36.0-rc2` and is treated as a trusted dependency for this check. The procedure does not claim to independently replay every declaration in the full Mathlib import closure.

A separate `lake check --paranoid` full-closure audit is available as an opt-in manual workflow input. It is stronger in dependency coverage and more expensive. A complete verification report must state which of these scopes actually passed.

## Unified proof architecture

Let F be a field, E/F a field extension, and let α₁,...,αᵣ be algebraic over F. Write dᵢ for the degree of the minimal polynomial of αᵢ over F and define

\[
K_0=F,qquad K_i=K_{i-1}(\alpha_i).
\]

The minimal polynomial over F remains a nonzero polynomial over Kᵢ₋₁ with αᵢ as a root. Therefore

\[
[K_i:K_{i-1}]\le d_i.
\]

The tower law gives the explicit bound

\[
[F(\alpha_1,\ldots,\alpha_r):F]
 \le \prod_{i=1}^{r}d_i < \infty.
\]

Equivalently, the monomials

\[
\alpha_1^{e_1}\cdots\alpha_r^{e_r},
\qquad 0\le e_i<d_i,
\]

form a finite spanning family; they need not be linearly independent.

If an extension L/F has finite dimension N, then for every x in L the N+1 elements 1,x,...,xᴺ are linearly dependent. A nonzero polynomial over F therefore vanishes at x, proving that L/F is algebraic.

Finally, α⁻¹ (for α nonzero in the usual field convention) and αⁿ for n in ℤ (with α nonzero when n is negative) lie in F(α). They are consequently algebraic over F. The formal Lean file uses Lean's totalized field inverse, where 0⁻¹=0, and records the exact convention in its docstrings.

This construction is a unified proof certificate and formalization strategy, not a claim to have discovered new field theory. The individual theorems are classical. No separability assumption, primitive element theorem, or algebraic-closure assumption is used.

## Key mathlib declarations checked

- IsAlgebraic.inv_iff and IsAlgebraic.inv in Mathlib/RingTheory/Algebraic/Basic.
- IsAlgebraic.isIntegral, IsIntegral.pow, and IsIntegral.isAlgebraic for the natural-power proof.
- IntermediateField.adjoin.finiteDimensional and IntermediateField.finiteDimensional_adjoin in Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.
- IntermediateField.adjoin.finrank, identifying the dimension of a simple algebraic extension with the minimal-polynomial degree.
- IntermediateField.fg_top_iff, identifying finite generation as a field with Algebra.EssFiniteType.
- Algebra.finite_of_essFiniteType_of_isAlgebraic in Mathlib/FieldTheory/IntermediateField/Adjoin/Algebra.
- Algebra.IsAlgebraic.of_finite in Mathlib/RingTheory/Algebraic/Integral.

## Reproducibility and cost

The project pins Lean and mathlib to the same version and uses the public mathlib cache in GitHub Actions. No paid CAS, private theorem-proving service, or paid cloud solver is part of the proof dependency. Any optional local use of the listed open-source repositories is limited to freely available source releases and does not create a new proof dependency.
