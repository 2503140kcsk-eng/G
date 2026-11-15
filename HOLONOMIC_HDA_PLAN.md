# Holonomic–Determinantal–Asymptotic (HDA) research plan

**Date:** 2026-11-15 (JST)  
**Work branch:** research/holonomic-hda-chebyshev-2026-11-15  
**Formal base:** PR #1 proof trunk, commit a1491dbb4b9e6542b14d271de0cf7a4d1876a593  
**Toolchain:** Lean v4.36.0-rc2; Mathlib v4.36.0-rc2; the existing frozen Lake manifest is retained.

## 1. Objective and acceptance contract

Explore hypergeometric-type and holonomic polynomial families and produce kernel-checked Lean proofs of three linked results:

1. **Coefficient recurrence:** a closed, finite-order recurrence for coefficients a(n,k).
2. **Determinant invariant:** a Casoratian / fundamental-matrix determinant identity derived from the same recurrence.
3. **Analytic limit:** a rigorously stated and proved limit, with all nonzero and domain conditions explicit.

A result counts as complete only if it is a Lean theorem in the implementation module, compiles under the pinned toolchain, has no sorry, admit, or custom axiom, and its axiom dependencies are audited. Symbolic computation, numerical agreement, search results, and a handwritten derivation are not proof certificates.

## 2. HDA method: a reusable construction

Let P_n(x) be a polynomial family satisfying a recurrence of order r
\[
  \sum_{j=0}^{r} p_j(n,x)P_{n+j}(x)=0,
  \qquad p_j\in K[n,x].
\]
The family is holonomic in the index when such a nonzero polynomial-coefficient recurrence exists. A coefficient is hypergeometric in its indices when its adjacent-term ratio is rational wherever the ratio is defined.

The HDA pipeline is:

- **H — recurrence extraction:** prove the polynomial recurrence and apply the coefficient map Polynomial.coeff; prove boundary cases separately rather than hiding them in a negative-index convention.
- **D — determinant transport:** write the recurrence as a first-order state transition. For two solutions, derive the Casoratian multiplier from the determinant of the transition matrix. For a second-order recurrence y(n+2)=a(n)y(n+1)+b(n)y(n), the Casoratian satisfies W(n+1)=-b(n)W(n). If b(n)=-1, it is constant.
- **A — asymptotic transport:** use an exact special-function identity to reduce the polynomial limit to a standard analytic limit (for example, sin(z)/z→1); use Tendsto composition, multiplication, division, and eventual non-vanishing with explicit hypotheses.
- **Audit:** export the three theorem families in a dedicated audit module; inspect #print axioms; run the pinned Lake build and the repository's paranoid checker.

This is a reusable proof architecture, not a claim that every holonomic family has a constant determinant or a finite limit. In general, the determinant is multiplied by the recurrence's trailing coefficient, and the asymptotic normalization must be chosen for the family and regime.

## 3. First candidate: Chebyshev T and U

Mathlib already defines Polynomial.Chebyshev.T and .U over arbitrary commutative rings and proves their shared recurrence:
\[
T_{n+2}=2XT_{n+1}-T_n,\qquad
U_{n+2}=2XU_{n+1}-U_n.
\]
It also contains the real trigonometric evaluation identities
\[
T_n(\cos\theta)=\cos(n\theta),\qquad
U_n(\cos\theta)\sin\theta=\sin((n+1)\theta).
\]
This sharply reduces the trusted project code: the family and trigonometric identities are imported from the pinned Mathlib revision; this project proves the coefficient and determinant consequences and the scaled limit.

### 3.1 Coefficient recurrence

Define t(n,k)=[X^k]T_n(X), u(n,k)=[X^k]U_n(X). For k≥1,
\[
t_{n+2,k}=2t_{n+1,k-1}-t_{n,k},\qquad
u_{n+2,k}=2u_{n+1,k-1}-u_{n,k}.
\]
For the boundary coefficient,
\[
t_{n+2,0}=-t_{n,0},\qquad u_{n+2,0}=-u_{n,0}.
\]
The Lean implementation uses the pinned Polynomial coefficient API to extract these equations.

### 3.2 Determinant invariant

Set W_n=T_{n+1}U_n-T_nU_{n+1}. Direct substitution into the shared recurrence gives W_{n+1}=W_n, and the initial values give W_0=-X. Thus
\[
\boxed{W_n=-X\quad(n\in\mathbb N).}
\]
Equivalently, the determinant of the adjacent-state matrix
\[
\begin{pmatrix}T_n&T_{n+1}\\U_n&U_{n+1}\end{pmatrix}
\]
is X, independent of n. The implementation initially spells out the 2-by-2 determinant as ad-bc; a subsequent audit should also connect it explicitly to Matrix.det so the matrix-library representation and scalar formula are not conflated.

### 3.3 Analytic limit

For fixed t≠0, use theta_n=t/(n+1). The trigonometric identity gives
\[
U_n(\cos\theta_n)\sin\theta_n=\sin t.
\]
Since sin(z)/z→1 as z→0,
\[
(n+1)\sin\theta_n
=t\frac{\sin\theta_n}{\theta_n}\longrightarrow t.
\]
Therefore
\[
\boxed{
\lim_{n\to\infty}
\frac{U_n(\cos(t/(n+1)))}{n+1}
=\frac{\sin t}{t}
\quad(t\ne0).
}
\]
The point t=0 is a separate boundary case; the continuous extension of the right side is 1. It must be formalized as a separate theorem rather than silently dividing by zero.

The Lean file lean/HolonomicChebyshev.lean contains the first implementation attempt, including coefficient recurrences, the Casoratian identity, the explicit 2-by-2 determinant formula, and the Mehler–Heine-type limit. Its status is **written, awaiting CI compilation and proof audit**; it must not be described as fully verified until CI passes.

## 4. Candidate-family search order

| Priority | Family | Why it is useful | Main formal risk |
|---|---|---|---|
| 1 | Chebyshev T,U | Shared recurrence, exact trigonometric identities, clean constant Casoratian, direct Mathlib support | Limit proof and explicit Matrix.det bridge |
| 2 | Hermite | Hypergeometric coefficients, derivative relation, Gaussian analysis, Mathlib already has coefficient recurrence results | Normalization and scaled Hermite limit |
| 3 | Laguerre | Confluent hypergeometric representation; useful Mehler–Heine/Bessel limits | Gamma/Pochhammer coefficient bookkeeping |
| 4 | Gegenbauer | Natural limit to Hermite; generating-function route | Parameter-dependent normalization |
| 5 | Jacobi | Broad Askey-scheme connections and limits to Laguerre | Two-parameter asymptotics |
| 6 | Charlier / Krawtchouk / Meixner | Discrete orthogonal polynomials; finite/discrete analogues | Parameter and support boundary cases |

The Askey-scheme asymptotic paper by Temme and López explains how generating functions yield limits among Meixner–Pollaczek, Jacobi, Meixner, Krawtchouk, Laguerre, and Hermite families. Petkovšek's work on hypergeometric solutions of polynomial-coefficient recurrences supplies the algorithmic recurrence-search viewpoint. These are discovery references, not formal proof dependencies.

## 5. Roles for connected tools and plugins

The mathematical trust base remains the pinned Lean toolchain, Mathlib, and source modules in this repository. All other tools are assigned bounded discovery or experiment roles.

| Tool / plugin | HDA task | What it cannot certify |
|---|---|---|
| GitHub | Inspect exact Mathlib/repository source, maintain the isolated branch, run CI, preserve reviewable commits | A commit or green CI cannot validate a theorem that was not built |
| Sider Scholar | Search primary papers on holonomic recurrences, orthogonal polynomials, determinant identities, and asymptotics | Search ranking is not proof or peer review |
| Wolfram | Generate candidate recurrences, verify low-degree examples, compare generating functions and determinant values | Numerical/symbolic output does not prove universal identities or limits |
| Context7 | Find version-matched Mathlib API and Lean documentation | Documentation is not the kernel |
| Parallel Search | Independently cross-check literature, theorem statements, and source URLs | Search synthesis is not proof |
| Tavily | Optional independent web discovery/fetch if a primary source is inaccessible | Not a proof dependency |
| Malwarebytes | Check release/download URLs before running auxiliary binaries | Security scanning does not validate mathematics |
| Notion | Store a research notebook or literature matrix only if a durable workspace artifact is requested | Not part of the proof graph |
| Slack | Share a review summary only if team communication is requested | Not part of the proof graph |
| Asana | Track milestones/review tasks if project management is requested | Not part of the proof graph |
| Atlassian Rovo | Find Jira/Confluence specs only if this project is tracked there | Not part of the proof graph |
| Linear | Track formalization issues and CI failures if selected for issue management | Not part of the proof graph |
| Adobe / Canva / Figma | Create a paper figure or dependency diagram if a presentation is requested | Visual artifacts are not proof terms |
| Amplitude / PostHog | Only relevant if a user-facing proof explorer later collects usage telemetry | No role in the current theorem-only repository |
| Convex / Neon / Supabase | Only relevant to a future collaborative proof explorer or metadata service | No role in the current theorem-only repository |
| Vercel | Deploy a future proof-explorer front end | No role in Lean kernel checking |
| Automations | Schedule a future review/check only if requested | Scheduling is not mathematical evidence |
| Plugin Management | Discover a missing connector when a concrete task requires it | Administrative only |

## 6. Roles for the recorded starred repositories

The following allocation uses the 30-public-repository Stars snapshot recorded in TOOLS_AND_PROOF_PROTOCOL.md (2026-11-10). It does not infer private or inaccessible stars.

### Direct proof and formal-method comparisons
- leanprover-community/mathlib4: sole direct mathematical dependency; polynomial, matrix, topology, trigonometric, and asymptotic APIs.
- google-deepmind/cryptids: Lean theorem-organization patterns.
- VladimirReshetnikov/ProveIt: proof decomposition and formal proof scripting patterns.
- graph-theory-AI/graph-theory-rocq: compare independent Rocq encodings for recurrence state machines and finite matrices.
- rocq-community/fourcolor: large-proof modularity and audit patterns.
- math-comp/math-comp: independent algebraic hierarchy and matrix determinant comparison.
- rocq-community/graph-theory: finite transition-system representation patterns.
- MizarSystem/MML: compare definitions of polynomial sequences and determinant identities.
- rocq-archive/zfc: foundational reference only; no direct role.
- metamath/metamath-exe: independently check elementary algebra lemmas if recast in Metamath.
- metamath/set.mm: reference for elementary algebra and determinant identities.
- isabelle-prover/mirror-isabelle: compare recurrence and matrix formalizations.
- isabelle-prover/mirror-afp-devel: inspect AFP orthogonal-polynomial or asymptotic entries.
- bbchallenge/bbchallenge-proofs: reproducible proof artifact/audit patterns.
- jeff87654/busy-beaver: proof organization and independent-checking patterns.

### Symbolic, algebraic, and exact computation
- Macaulay2/M2: elimination ideals, resultants, quotient rings, and parameter constraints in candidate polynomial identities.
- Singular/Singular: independent Gröbner-basis/resultant cross-checks.
- flintlib/flint: fast exact integer and polynomial arithmetic for generated test cases.
- sympy/sympy: derive coefficient recurrences, simplify generating functions, and test candidate determinant formulas.
- sagemath/sage: exact algebraic fields, polynomial roots, and asymptotic/numeric experiments with precision controls.
- gap-system/gap: finite-field and finite-group examples for recurrence monodromy; exploratory only.
- emil79/flagmatic: optional only if a finite combinatorial inequality enters a later proof.
- graphillion/graphillion: optional finite-state/path enumeration if recurrence certificates are encoded as automata.
- graph-theory-AI/graph-conjectures: conjecture management and finite counterexample exploration.
- koteitan/basmat-2.x: optional matrix-growth experiment only if a later family has nontrivial transfer-matrix growth.
- hypcos/incremental-googology: no direct role unless a growth-rate side question arises.
- MeniRosenfeld/TransfiniteOrdinalCalculator: no direct role in this polynomial-analysis project.

### Proof search and argument audit
- lean-dojo/LeanDojo-v2: find Mathlib premises and candidate proof traces; every suggestion must compile and pass the kernel.
- naproche/naproche: audit written arguments for hidden hypotheses, index shifts, and boundary cases.
- cvc5/cvc5: bounded algebraic side conditions and finite counterexample search; not a substitute for induction or real analysis.

All repositories other than Mathlib are references or auxiliary experiments; they are not imported as trusted proof dependencies.

## 7. Work sequence and gates

1. **Gate H0 — compile the first module.** Resolve all Lean errors without weakening theorem statements or introducing axioms.
2. **Gate H1 — coefficient layer.** Add explicit boundary cases, degree/leading-coefficient facts, and a generic coefficient-extraction lemma for second-order recurrences.
3. **Gate D1 — determinant layer.** Prove the generic Casoratian multiplier theorem for y(n+2)=a(n)y(n+1)+b(n)y(n), then specialize to Chebyshev; connect the hand-written 2x2 determinant to Matrix.det.
4. **Gate A1 — analytic layer.** Prove the t≠0 limit; separately prove the t=0 continuous extension and a uniform-on-compact variant if Mathlib supports the chosen route.
5. **Gate G1 — generalization.** Add Hermite as the second family, then Laguerre/Gegenbauer/Jacobi only after a clear formalization route is identified.
6. **Gate Q — audit.** Run pinned lake build --wfail, source scan for proof holes/custom axioms, #print axioms, and the existing paranoid Comparator workflow. Do not modify the frozen manifest or run lake update.
7. **Gate R — review.** Open a draft PR only after CI has run; mark ready only after all three required proof layers and audit pass.

## 8. Current progress and explicit limitations

- A new isolated branch has been created from the current PR #1 proof trunk.
- lean/HolonomicChebyshev.lean has been added.
- lakefile.lean has been updated to include the new library.
- The implementation has **not yet been compiled in the repository's pinned CI**. The code is therefore a proof attempt, not a verified theorem package.
- The 2x2 determinant is currently represented by the explicit formula ad-bc; a bridge to Mathlib's Matrix.det remains a required audit task.
- The analytic limit's zero-angle case is intentionally excluded by t≠0; it requires a separate theorem.
- No new third-party dependency was added and the existing Lake manifest was not changed.

## 9. Literature and source entry points

- Marko Petkovšek, “Hypergeometric solutions of linear recurrences with polynomial coefficients” (1992): https://www.sciencedirect.com/science/article/pii/0747717192900386
- N. M. Temme and J. L. López, “The Askey scheme for hypergeometric orthogonal polynomials viewed from asymptotic analysis” (2001): https://ir.cwi.nl/pub/23/0023D.pdf
- Mathlib Polynomial.Chebyshev: https://github.com/leanprover-community/mathlib4/blob/v4.36.0-rc2/Mathlib/RingTheory/Polynomial/Chebyshev.lean
- Mathlib trigonometric Chebyshev identities: https://github.com/leanprover-community/mathlib4/blob/v4.36.0-rc2/Mathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Basic.lean
- Mathlib polynomial coefficient API: https://github.com/leanprover-community/mathlib4/blob/v4.36.0-rc2/Mathlib/Algebra/Polynomial/Coeff.lean
- Mathlib real sine limit source: https://github.com/leanprover-community/mathlib4/blob/v4.36.0-rc2/Mathlib/Analysis/SpecialFunctions/Trigonometric/Deriv.lean

These sources guide theorem selection and API use. The actual proof remains the Lean source compiled against the exact pinned manifest.
