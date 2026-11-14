# Tool allocation and proof-integrity protocol

**Project snapshot:** 2026-11-12 (JST)  
**Repository:** `2503140kcsk-eng/G`  
**Formal environment:** Lean `v4.36.0-rc2`; Mathlib `v4.36.0-rc2`; exact dependency revisions recorded in `lake-manifest.json`.

## 1. Governing rule: discovery, experiments, proof

The project separates three activities:

1. **Discovery:** locate literature, theorem statements, source declarations, and current API documentation.
2. **Experiment:** explore concrete examples, candidate identities, finite algebraic computations, and possible counterexamples.
3. **Proof:** establish universal statements in Lean and have the Lean kernel check them.

Only the third activity certifies a formal theorem. Web search, AI research, CAS, SMT solvers, tactic suggestions, and handwritten calculations are not proof substitutes.

## 2. Connected tools and plugin responsibilities

| Tool / integration | Assigned responsibility | Evidence boundary |
|---|---|---|
| GitHub | Inspect the exact repository and upstream source; commit changes on the isolated branch; execute pinned CI; retain logs and commits. | A green build certifies the declarations actually built, not the open mathematical target. |
| Sider Scholar | Discover academic sources and formalization literature for Lindemann–Weierstrass, Hermite–Lindemann, Schanuel, and related results. | Search hits are leads; inspect publication status and theorem hypotheses. |
| Wolfram | Check symbolic identities and exact finite examples; give independent mathematical context. | Numeric or symbolic computation cannot establish transcendence. |
| Context7 | Retrieve current Lean 4 / mathlib API documentation and version-sensitive signatures. | Documentation is guidance; the elaborator and kernel check Lean proof terms. |
| Parallel Search / Research | Independently audit the current literature status and cross-check technical or mathematical claims. | Research synthesis is not a proof; cite primary sources when possible. |

Other connected applications (for example design, project-management, messaging, analytics, cloud, or database connectors) have no relevant role in this pure number-theory formalization and are intentionally not used. No paid CAS or hosted theorem-prover is a proof dependency.

## 3. User-starred GitHub repositories: role and boundary

The following 30 public repositories were recorded in the project's GitHub Stars snapshot on 2026-11-10 JST. The snapshot reported 30 entries on page 1 and no further entries on pages 2–3. Private or otherwise inaccessible stars are not included or inferred.

### Direct formal proof and independent foundation comparisons

| Repository | Assigned role in this project | Boundary |
|---|---|---|
| [leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4) | Primary Lean mathematics library: algebraic extensions, intermediate fields, transcendence degree, polynomials, complex exponential analysis. | The only direct formal-mathematics package dependency; exact tag and commit are pinned. |
| [google-deepmind/cryptids](https://github.com/google-deepmind/cryptids) | Mine examples of Lean theorem organization, definitions, and proof engineering. | Reference only; not imported. |
| [VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt) | Compare proof scripting and formal proof decomposition. | Reference only; not a kernel substitute. |
| [graph-theory-AI/graph-theory-rocq](https://github.com/graph-theory-AI/graph-theory-rocq) | Compare Rocq proof organization and cross-assistant checking methods. | No direct graph-theoretic dependency in this number-theory proof. |
| [rocq-community/fourcolor](https://github.com/rocq-community/fourcolor) | Study large proof maintenance, modularity, and audit practices. | Methodology example only. |
| [math-comp/math-comp](https://github.com/math-comp/math-comp) | Independent comparison of algebraic hierarchy and field structures in Rocq. | No shared Lean kernel; cross-check only. |
| [rocq-community/graph-theory](https://github.com/rocq-community/graph-theory) | Reference for finite-structure formalization patterns. | Peripheral; no direct theorem input. |
| [MizarSystem/MML](https://github.com/MizarSystem/MML) | Compare formal definitions of algebraic numbers, fields, and extensions. | Independent proof system; no dependency. |
| [rocq-archive/zfc](https://github.com/rocq-archive/zfc) | Optional foundational encoding reference. | Not needed for the current proof. |
| [metamath/metamath-exe](https://github.com/metamath/metamath-exe) | Run/check Metamath proof databases if an elementary lemma is independently recast. | No role in Lean checking. |
| [metamath/set.mm](https://github.com/metamath/set.mm) | Independent theorem reference for foundational algebra. | Reference only. |
| [isabelle-prover/mirror-isabelle](https://github.com/isabelle-prover/mirror-isabelle) | Compare Isabelle/HOL formalization patterns and algebraic results. | Separate kernel and libraries. |
| [isabelle-prover/mirror-afp-devel](https://github.com/isabelle-prover/mirror-afp-devel) | Inspect Archive of Formal Proofs developments, especially transcendence formalizations. | Reference and blueprint only; no direct Lean import. |
| [bbchallenge/bbchallenge-proofs](https://github.com/bbchallenge/bbchallenge-proofs) | Compare explicit proof audit and reproducible proof artifacts. | Unrelated theorem domain; methodology only. |
| [jeff87654/busy-beaver](https://github.com/jeff87654/busy-beaver) | Compare proof artifact organization and independent checking practices. | Unrelated theorem domain; methodology only. |

### Exact computation and algebraic exploration

| Repository | Assigned role in this project | Boundary |
|---|---|---|
| [Macaulay2/M2](https://github.com/Macaulay2/M2) | Explore polynomial ideals, quotient algebras, elimination, and resultants in finite candidate constructions. | Computation cannot prove the universal transcendence claim. |
| [Singular/Singular](https://github.com/Singular/Singular) | Cross-check Gröbner-basis and polynomial-ideal calculations. | Finite algebraic calculations only. |
| [flintlib/flint](https://github.com/flintlib/flint) | Fast exact integer and polynomial arithmetic for test data. | Exact computation is not a universal proof. |
| [sympy/sympy](https://github.com/sympy/sympy) | Check polynomial identities, algebraic-number examples, and resultants. | Symbolic simplification is not a transcendence proof. |
| [sagemath/sage](https://github.com/sagemath/sage) | Explore concrete number fields, composita, embeddings, minimal polynomials, and Galois groups. | Experimental evidence only. |
| [gap-system/gap](https://github.com/gap-system/gap) | Explore finite groups, finite fields, and finite Galois examples. | Cannot decide arbitrary infinite extensions. |
| [emil79/flagmatic](https://github.com/emil79/flagmatic) | Optional flag-algebra experiments if a combinatorial auxiliary lemma emerges. | No current role in the proof. |
| [graphillion/graphillion](https://github.com/graphillion/graphillion) | Optional graph-set exploration if a finite combinatorial encoding is introduced. | No current role in the proof. |
| [graph-theory-AI/graph-conjectures](https://github.com/graph-theory-AI/graph-conjectures) | Reference for conjecture-management and experimental workflows. | No direct algebraic role. |

### Proof search and natural-language reasoning

| Repository | Assigned role in this project | Boundary |
|---|---|---|
| [lean-dojo/LeanDojo-v2](https://github.com/lean-dojo/LeanDojo-v2) | Retrieve candidate premises and proof traces; suggest tactic candidates. | Every suggestion must be elaborated and kernel-checked in the pinned environment. |
| [naproche/naproche](https://github.com/naproche/naproche) | Audit whether written arguments expose assumptions, quantifiers, and intermediate lemmas. | Does not replace Lean's kernel proof. |
| [cvc5/cvc5](https://github.com/cvc5/cvc5) | Check bounded first-order or polynomial side conditions and search for finite counterexamples. | Cannot prove the general transcendence statement or unrestricted field theorem. |
| [MeniRosenfeld/TransfiniteOrdinalCalculator](https://github.com/MeniRosenfeld/TransfiniteOrdinalCalculator) | Retained as an unrelated ordinal/large-number research resource. | No role in this field-theoretic proof. |
| [koteitan/basmat-2.x](https://github.com/koteitan/basmat-2.x) | Retained as an unrelated integer/matrix growth resource. | No role in this proof. |
| [hypcos/incremental-googology](https://github.com/hypcos/incremental-googology) | Retained as an unrelated large-number/ordinal exploration resource. | No role in this proof. |

## 4. Minimal formal dependency boundary

The Lean project has one direct mathematics dependency: Mathlib. The other named GitHub repositories and connected tools are auxiliary research, comparison, and experiment resources. They are deliberately not imported into the trusted proof graph.

The relevant proof chain in this project is:

`Mathlib analytic exponential estimate`
→ `LindemannAlgebraicPart.lean` + `LindemannBasic.lean`
→ `HermiteLindemannBridge.lean`
→ `AlgebraicClosure.lean` and `EPlusPi.lean`
→ `SchanuelConditional.lean`.

The analytic estimate alone is not the completed Lindemann–Weierstrass theorem; the algebraic argument in the vendored project module is also required. The individual transcendence proofs derive from this combined Lean development.

## 5. Formal theorem boundaries

The following are separate claims and must not be conflated:

- **Proved unconditionally:** (e) and (pi) are individually transcendental over (mathbb Q).
- **Proved unconditionally:** at least one of (e+pi) and (epi) is transcendental.
- **Proved conditionally:** Schanuel's conjecture implies algebraic independence of (e) and (pi), and therefore implies transcendence of (e+pi).
- **Not proved:** unconditional irrationality or transcendence of (e+pi). This remains an open target; its proposition is stated without an axiom, `sorry`, or fabricated theorem.

The project does not promote the conditional theorem into an unconditional theorem.

## 6. Reproducibility and audit policy

The exact Lean toolchain is recorded in `lean-toolchain`. Mathlib is fixed at `v4.36.0-rc2`; its concrete git revision and the revisions of all Lake dependencies are recorded in `lake-manifest.json`. CI must build the committed manifest and run the axiom checks. A green build certifies only the declarations and targets that the run actually checks.

The accepted standard-axiom allowlist is `propext`, `Classical.choice`, and `Quot.sound`. The relevant declarations also print their axiom dependencies in the build log. A clean log is not a claim that all transitive Mathlib declarations have been independently replayed.

No numerical approximation, symbolic experiment, theorem-search output, or conditional hypothesis is treated as an unconditional proof of (e+pi)'s transcendence.


## 8. Final import, audit, and licensing state (2026-11-12)

The files HermiteLindemannBridge.lean, EPlusPi.lean, and SchanuelConditional.lean no longer use the umbrella public import Mathlib. They import project modules plus focused Mathlib APIs. The Schanuel module explicitly imports the transcendence-basis and multivariate-polynomial interfaces required by its proof. The committed Lake manifest pins the Mathlib tag and all eight transitive packages by git revision; the workflow does not run lake update.

The CI library `ProofAudit` re-exports eight explicitly typed principal theorem statements. In addition to the six established e/π and Schanuel results, it now audits two general conditional approximation criteria: (1) an eventually nonzero sequence of integer linear forms whose values tend to zero forces irrationality; (2) super-polynomial decay relative to coefficient height forces the Liouville property and transcendence. The workflow sets `axiom-audit-root: ProofAudit`, so the audit follows those statements into their transitive project-proof dependencies. On 2026-11-12, push run #258 and PR run #259 both passed on commit `f38989247ec9fdcc3351def8adf53e2f216c12d4`. Each completed 6,137 Lake build jobs; the automated axiom audit accepted all eight declarations under the standard allowlist `propext`, `Classical.choice`, and `Quot.sound`. This is not an independent replay of every declaration in Mathlib's complete import closure.

- [Push CI #210](https://github.com/2503140kcsk-eng/G/actions/runs/43198316263)
- [PR CI #211](https://github.com/2503140kcsk-eng/G/actions/runs/43198324014)

The root LICENSE file is the exact Apache License 2.0 text from Mathlib tag v4.36.0-rc2. The vendored Lindemann proof sources retain their original copyright and author headers.

## 9. All connected integration namespaces: assigned roles

The following role matrix covers the connected app/tool namespaces visible in this workspace at the time of this project snapshot. A role assignment does not mean every integration was invoked or that it contributes a theorem to the trust base. The formal proof dependency remains Mathlib plus the Lean source in this repository.

| Connected integration | Assigned role for this project | Status / boundary |
|---|---|---|
| GitHub | Repository inspection, exact source changes, branch/PR management, Lake CI and action-log retrieval. | **Used**; source and CI evidence. |
| Sider Scholar | Search formal transcendence proofs and adjacent Lean/Isabelle developments; inspect arXiv metadata. | **Used**; literature discovery, not proof checking. |
| Wolfram | Check exact polynomial identities and illustrative algebraic calculations. | **Used**; for example, factor the quadratic with roots e and π. Symbolic output is not a transcendence proof. |
| Context7 | Retrieve Lean 4 and Mathlib API documentation and version-sensitive import guidance. | **Used**; documentation only, exact source and CI remain authoritative. |
| Parallel | Search and independently cross-check the open-problem status and Schanuel proof outline. | **Used**; research/search is not a kernel proof. |
| Tavily | Optional second-source web discovery or URL extraction if primary search snippets are insufficient. | Available; not required for the verified Lean proof. |
| Malwarebytes | Check suspicious dependency/release URLs or downloaded tools before running them. | Available; security hygiene only, not mathematical verification. |
| Notion | Store a longer project notebook, proof outline, or research decision log if the user requests workspace capture. | Available; no proof dependency. |
| Slack | Coordinate review notes or send a concise status summary if the user requests team communication. | Available; no proof dependency. |
| Asana | Track formalization milestones and review tasks if project management is requested. | Available; no proof dependency. |
| Atlassian Rovo | Search or maintain Jira/Confluence records if an external project specification or review process exists. | Available; no proof dependency. |
| Linear | Track technical issues, milestones, and CI failures if the user chooses Linear for project management. | Available; no proof dependency. |
| Adobe | Prepare polished diagrams or a paper/slide visual only if a presentation deliverable is requested. | Available; visual output is not a proof certificate. |
| Canva | Prepare a poster or presentation of the theorem architecture if requested. | Available; visual output is not a proof certificate. |
| Figma | Design a navigable proof-dependency map or project dashboard if requested. | Available; design layers are not proof terms. |
| Amplitude | Analyze product interaction analytics only if the project later has a user-facing application. | Not relevant to the current theorem-only repository. |
| PostHog | Analyze usage/telemetry only if a user-facing app or proof explorer is later built. | Not relevant to the current theorem-only repository. |
| Convex | Provide a reactive backend only if a separate collaborative proof dashboard is built. | Not relevant; not imported. |
| Neon | Host a Postgres database only if proof metadata/search history needs persistent storage. | Not relevant; not imported. |
| Supabase | Provide database/auth/storage only if a separate web application is built. | Not relevant; not imported. |
| Vercel | Deploy a future proof-explorer web front end. | Not relevant; no deployment is needed for Lean CI. |
| Automations | Remind the user about a review date or monitor a future event only if specifically requested. | Not used; scheduled work does not establish theorems. |
| Plugin Management | Discover/connect an additional service only when a concrete capability is missing. | Administrative only; no proof dependency. |

### Core file and utility tools (not app plugins)

The connected file/library functions can inspect or manage uploaded project artifacts on explicit request; no user library file is a dependency of this repository. Skills lookup is documentation discovery. User settings and reference-image functions have no role in this mathematical project. They are intentionally not used to invent or modify proof evidence.

### Free-scope and cost boundary

The proof itself is built from the open-source Lean toolchain, the pinned public Mathlib source, and the repository's GitHub Actions workflow. Macaulay2, GAP, SymPy, SageMath, Naproche, cvc5, and LeanDojo-v2 are treated as optional open-source auxiliary tools, not required paid proof services. The current verification does not depend on a paid CAS or a hosted commercial theorem prover.

One Parallel Research-mode request was used during the literature cross-check. The connector documentation distinguishes Research from Search and indicates that Research may require a connected account; I cannot see the user's billing/quota status, so I cannot guarantee that this specific request fell within a free allowance. No further Research-mode request is needed for the already completed formal build and axiom audit. Check the provider's usage page for any account-level charge or quota effect.



## 10. PR integration decision and verification boundary (2026-11-14)

PR #1 is the canonical Lake workspace and proof trunk. PR #2 and PR #3 are treated as source contributions, not as branch configurations to merge wholesale.

- **PR #2 contribution:** retain the general finite-extension results: finite algebraic generators give a finite-dimensional intermediate field; a finite-dimensional extension is algebraic; and finite-dimensionality is equivalent to essential finite type plus algebraicity. Its separate nested Lake workspace and CI command `lake update` are not copied, because they would undermine the requirement to consume PR #1's frozen root manifest. The degree-product estimate in the PR #2 exposition remains a hand proof, not a theorem exported by the integrated Lean module.
- **PR #3 contribution:** retain the Mathlib representation `algebraicClosure K E : IntermediateField K E` and its field operations, maximality, and algebraic-closure consequences. The code is placed in PR #1's existing `lean/` source tree and is built against PR #1's manifest. PR #3's manifest and CI file are not copied.
- **Overlap policy:** PR #3's inverse and integer-power closure cover the same broad operations as PR #2's inverse and integer-power declarations. The integrated finite-extension module therefore contains only the three distinct finite-dimensionality results, avoiding a second copy of the same closure lemmas.
- **Audit policy:** eight original theorem wrappers plus 16 relative-algebraic-closure theorems and three finite-extension theorems are exposed under `ProofAudit`. The axiom audit examines 33 declarations under that root, including the inherited field-structure wrapper and their transitive project-proof dependencies. The solution side has no proof holes or custom axioms. The Challenge contains exactly 27 intentional `sorry` specifications, none imported by the solution.
- **Trusted statement boundary:** `ProofAuditChallenge.lean` imports Mathlib and `ProofAuditDefs.lean`. The latter imports Mathlib only and defines just the standard Schanuel proposition. Challenge and Solution share that exact definition; it contains no proofs, axioms, or holes. All other theorem types are stated directly in Mathlib vocabulary. The Comparator therefore checks 27 theorem names against an independently authored statement module, while the only non-Mathlib statement constant is a short reviewed proposition definition.
- **Reproducibility:** `lake-manifest.json` is left byte-for-byte unchanged at blob SHA `5625e0bc21b731d5737a903c674bf4b6fb0e018c`. CI verifies this hash and `lean-toolchain`, runs the warning-failing build, source scan, and axiom audit, then runs Lake Comparator in paranoid mode. No dependency update command is part of the workflow.

### Integrated CI evidence — 2026-11-14

PR Run #309 on commit `3f9aa564d97244c513c9f44faa757e24d488c347` completed successfully: [GitHub Actions Run #309](https://github.com/2503140kcsk-eng/G/actions/runs/43534926824). The frozen-manifest check, implementation-source proof-hole/custom-axiom scan, default `lake build --wfail`, sandbox setup, 27-statement Comparator, and paranoid checker stage all passed. The axiom audit checked 33 declarations and allowed only `propext`, `Classical.choice`, and `Quot.sound`. The Lean paranoid kernel, Lean default kernel, lean4lean, nanoda, con-leche, and con-ron all accepted the solution; con-leche and con-ron each verified 57,722 declarations.

### Evidence status for the source PRs

PR #2 had a successful targeted Comparator run on its then-current commit, but its workflow refreshed dependencies with `lake update`; that run is not evidence for the frozen PR #1 environment. PR #3's axiom audit and first two independent checker stages succeeded, but its earlier runner was shut down while nanoda was running; its full paranoid run did not complete. The successful integrated PR #1 Run #309 is the evidence for the combined tree.

The named starred repositories keep the roles in section 3: Mathlib4 is the only direct mathematical package dependency; Macaulay2, GAP, SymPy, SageMath, cvc5, Naproche, and LeanDojo-v2 are auxiliary exploration or proof-search resources, not trusted proof dependencies. Their software was not executed by merely consulting their GitHub sources. The connected-tool roles and free-scope boundaries remain in section 9.



## 11. Common-denominator fusion continuation (2026-11-14)

The branch **research/common-denominator-fusion-2026-11-14** adds a formal, conditional bridge for combining two independent rational approximations into a single integer linear form in their sum.

| Resource | Specific work in this continuation | Verification boundary |
|---|---|---|
| GitHub | Added the fusion definitions and Lean theorem, wired the theorem into ProofAudit, ProofAuditChallenge, lakefile.lean, and comparator.json; preserved the frozen manifest. | Push run #368 passed in full. No change was made to main and no claim of an unconditional e + π result is made. |
| Sider Scholar | Retrieved the arXiv record for Yu's 2026 preprint on e + π irrationality obstructions and searched Hermite–Padé literature. | Literature discovery only. The broad OpenAlex query was noisy; it is not treated as mathematical evidence. |
| Wolfram | Checked finite exact examples related to the growth of cross-multiplied denominators. | Finite symbolic checks only; the lacunary-series obstruction in the research note is a separate written estimate. |
| Context7 | Resolved the Mathlib v4.36.0-rc2 library identifier. The documentation endpoint returned no matching entries for the targeted lemma queries. | The exact squeeze_zero and abs_add_le APIs were instead located in the pinned Mathlib source through GitHub search and verified by CI. |
| Parallel | Retrieved the arXiv preprint and a 2006 Hermite–Padé lecture-note source for independent context. | Source extraction and synthesis only; not a proof dependency. |
| User-starred algebra/computation repositories | M2, GAP, SymPy, Sage, Naproche, cvc5, LeanDojo-v2, and Mathlib retain the roles from section 3. | Their software is not imported as a trusted proof dependency. Mathlib remains the sole direct mathematical package dependency. |

### Formal and CI result

For integers \(p,s\) and natural denominators \(q,r\), the exact identity
\[
(qr)(x+y)-(rp+qs)=r(qx-p)+q(ry-s)
\]
is proved in CommonDenominatorApproximation.lean. The cross-weighted triangle bound and the conditional irrationality theorem are also proved. The new statement is the 30th theorem contract in comparator.json.

On commit 6f49702caca4abded88e8e4463e2cc29261430ee, GitHub Actions run #368 passed. The implementation's own #print axioms output for the new public wrapper contains only propext, Classical.choice, and Quot.sound. The automated axiom-audit reported 39 declarations under ProofAudit, all within the same allowlist. The Comparator paranoid phase was accepted by the Lean paranoid kernel, lean4lean (57,995 declarations), nanoda, con-leche (57,994 declarations), con-ron (57,994 declarations), and Lean's default kernel.

The mathematical limitation is explicit: two separate limits \(q_nx-p_n\to0\) and \(r_ny-s_n\to0\) do not imply the cross-weighted limit. A lacunary-series counterexample and its proof are recorded in COMMON_DENOMINATOR_FUSION_AUDIT_2026-11-14.md. Thus this continuation supplies a precise conditional bridge, not the missing construction for \(x=e,y=\pi\).
