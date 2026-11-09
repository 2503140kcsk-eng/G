# Algebraic elements and algebraic closure: formalization status

**Snapshot:** 2026-11-10 (JST)  
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

- No project axiom, `sorry`, or `admit` is introduced in the current source.
- `G/AxiomAudit.lean` contains `#print axioms` commands for all 17 exported declarations.
- The successful Lake build on commit `c7bd602` compiled both `G.AlgebraicElements` and `G.AxiomAudit`; the full workspace reported 4,086 successful build jobs.
- The explicit axiom output for all 17 declarations was exactly the allowed set: `propext`, `Classical.choice`, and `Quot.sound`.
- The previous `lean-action@v1` nanoda hook failed with `invalid digit found in string` after exporting a 1.63 GB / 28.76-million-line NDJSON file. The trace points to the action cloning `ammkrn/nanoda_lib` from its stale `debug` branch. Upstream `nanoda_lib` PR #7 ("Switch to ndjson parser") was merged to `master`; upstream lean-action issue #169 records the same incompatibility.
- The workflow has now been changed to run the normal build and dedicated `axiom-audit` first, then run `lake check --paranoid` as a separate step. This uses Lean 4.36's bundled, version-matched independent checkers (including nanoda) and ensures the axiom audit is not skipped when an external checker fails.
- The new workflow run #84 for commit `6c8f537` is in progress. It is **not yet a passing CI result**. The exact remaining acceptance condition is a successful `lake check --paranoid` run.
- LeanChecker was previously tested, including with `LEAN_NUM_THREADS=1`, but its process exited with code 139 on the GitHub-hosted runner. It is not used as a required separate step; the bundled paranoid checks are the replacement independent-check path.

The allowlist is deliberately restricted to Lean's expected foundational axioms: `propext`, `Classical.choice`, and `Quot.sound`. A clean `#print axioms` report is necessary but is not a substitute for the CI axiom-audit tool and independent kernel checking.

## Tool and repository work allocation

The public GitHub Stars API was inspected on 2026-11-10 JST. It returned 30 repositories (page 1); pages 2 and 3 were empty. The following assigns every observed starred repository a concrete role, while explicitly distinguishing direct proof dependencies from auxiliary or peripheral tools.

### Primary formal proof and independent proof-system cross-check

| Starred repository | Assigned role in this project | Boundary |
|---|---|---|
| [leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4) | Primary Lean library: IntermediateField, algebraicClosure, IsAlgebraic, IsAlgClosed, IsAlgClosure, and polynomial splitting | Trusted imported declarations; must pin exact revision |
| [google-deepmind/cryptids](https://github.com/google-deepmind/cryptids) | Mine examples of Lean definitions, proofs, and theorem organization | Not a dependency of the current module |
| [VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt) | Compare Lean proof scripts and formal proof organization | Not a replacement for kernel checking |
| [graph-theory-AI/graph-theory-rocq](https://github.com/graph-theory-AI/graph-theory-rocq) | Rocq cross-checking patterns and tactic/proof-structure comparison | The current theorem is field theory, not graph theory |
| [rocq-community/fourcolor](https://github.com/rocq-community/fourcolor) | Example of large-scale proof engineering and extraction boundaries | No direct algebraic-closure dependency |
| [math-comp/math-comp](https://github.com/math-comp/math-comp) | Independent algebraic hierarchy and field-structure comparison in Rocq | Cross-system validation only |
| [rocq-community/graph-theory](https://github.com/rocq-community/graph-theory) | General Rocq library organization and finite-structure examples | Peripheral to the field proof |
| [MizarSystem/MML](https://github.com/MizarSystem/MML) | Compare formal definitions of fields, algebraic extensions, and algebraic closure | Independent library; no shared kernel |
| [rocq-archive/zfc](https://github.com/rocq-archive/zfc) | Set-theoretic foundations and encodings for optional foundational comparisons | Not needed for the current field argument |
| [metamath/metamath-exe](https://github.com/metamath/metamath-exe) | Run/check Metamath proof databases if a foundational lemma is recast | Not used to verify Lean declarations |
| [metamath/set.mm](https://github.com/metamath/set.mm) | Independent set-theoretic and algebraic theorem reference | No Lean kernel integration |
| [isabelle-prover/mirror-isabelle](https://github.com/isabelle-prover/mirror-isabelle) | Isabelle/HOL algebra and proof-method comparison | Independent proof assistant |
| [isabelle-prover/mirror-afp-devel](https://github.com/isabelle-prover/mirror-afp-devel) | Search AFP for field-theoretic formalization patterns | Literature/code comparison, not a build dependency |
| [bbchallenge/bbchallenge-proofs](https://github.com/bbchallenge/bbchallenge-proofs) | Compare explicit proof audit and axiom discipline | Unrelated theorem domain |
| [jeff87654/busy-beaver](https://github.com/jeff87654/busy-beaver) | Compare proof artifact structure and axiom-free Rocq workflow | Unrelated theorem domain |

### Exact symbolic algebra and computational corroboration

| Starred repository | Assigned role in this project | Boundary |
|---|---|---|
| [Macaulay2/M2](https://github.com/Macaulay2/M2) | Ideals, quotient rings, elimination, resultants, and polynomial-system exploration | Experiments do not prove the universal theorem |
| [Singular/Singular](https://github.com/Singular/Singular) | Gröbner bases, polynomial ideals, and elimination as an independent algebra engine | No kernel-level proof |
| [flintlib/flint](https://github.com/flintlib/flint) | Fast exact integer/polynomial arithmetic for test instances | Computational support only |
| [sympy/sympy](https://github.com/sympy/sympy) | Minimal polynomials, exact algebraic numbers, resultants, and sanity tests | Does not prove general field closure |
| [sagemath/sage](https://github.com/sagemath/sage) | Number fields, embeddings, composita, minimal polynomials, and Galois groups | Independent computational corroboration |
| [gap-system/gap](https://github.com/gap-system/gap) | Finite fields, finite groups, and Galois-group example checking | Not central to an arbitrary field extension theorem |
| [emil79/flagmatic](https://github.com/emil79/flagmatic) | Optional flag-algebra experiments if combinatorial examples arise | Peripheral; not required here |
| [graphillion/graphillion](https://github.com/graphillion/graphillion) | Graph-set experiments only if an auxiliary finite combinatorial encoding is introduced | Not required for algebraic closure |
| [graph-theory-AI/graph-conjectures](https://github.com/graph-theory-AI/graph-conjectures) | Browse graph-theory formal conjecture workflows as a methodology reference | No direct role in the field proof |

### Proof search, natural-language formalization, and large-number utilities

| Starred repository | Assigned role in this project | Boundary |
|---|---|---|
| [lean-dojo/LeanDojo-v2](https://github.com/lean-dojo/LeanDojo-v2) | Premise retrieval, theorem matching, and tactic suggestion for Lean | Suggestions must be kernel-checked |
| [naproche/naproche](https://github.com/naproche/naproche) | Structure a readable natural-language proof plan and compare formal statements | Not a substitute for Lean checking |
| [cvc5/cvc5](https://github.com/cvc5/cvc5) | Check bounded first-order/algebraic side conditions and counterexample candidates | Cannot establish arbitrary-field algebraic closure by itself |
| [MeniRosenfeld/TransfiniteOrdinalCalculator](https://github.com/MeniRosenfeld/TransfiniteOrdinalCalculator) | Ordinal calculations for unrelated large-number research | No role in this field proof |
| [koteitan/basmat-2.x](https://github.com/koteitan/basmat-2.x) | Integer/matrix growth experiments for unrelated googology work | No role in this field proof |
| [hypcos/incremental-googology](https://github.com/hypcos/incremental-googology) | Large-number/ordinal game exploration | No role in this field proof |

### Installed research and development tools

| Tool | Assigned role | What it can establish |
|---|---|---|
| GitHub | Source changes, pinned dependencies, CI, PR history | Exact repository state and reproducible builds |
| Sider Scholar | Search papers on formal algebra and proof assistants | Literature discovery; this search did not surface a paper directly proving this specific result |
| Parallel Search/Fetch | Read current mathlib docs and CI documentation | Exact source/documentation cross-check |
| Context7 | Query current Lean/mathlib documentation | Useful for general API concepts; exact algebraic-closure queries returned no matching snippets in this session |
| Wolfram | Check concrete minimal polynomials, algebraic-number fields, and identities | Independent examples, not universal proof |

The project uses mathlib as its sole direct formal mathematics dependency. All other tools are assigned auxiliary roles and do not enter the trusted Lean dependency graph. The user's Star list is confirmed to contain 30 public repositories as of the retrieval snapshot; additional private or non-public starred repositories, if any, are not asserted here.
