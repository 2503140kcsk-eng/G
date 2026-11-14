# Research roadmap: paired determinant certificates for e + pi

Snapshot: 2026-11-14 (JST)  
Base: PR #1 proof trunk, commit a1491dbb4b9e6542b14d271de0cf7a4d1876a593  
Research branch: research/paired-determinant-certificate-2026-11-14  
Status: paired criterion source added; branch CI is pending / must be green before formal verification is claimed.  
Target: unconditional irrationality of e + pi. Transcendence is a later, strictly stronger target.

> This document does not claim that e + pi has been proved irrational or transcendental. It identifies a fully proved mathematical criterion, separates it from the missing approximation construction, and assigns work to the available research resources.

## 1. Repository state

PR #1, “Formalize e and pi transcendence with audited e+pi consequences”, is open and targets main. Its head is the branch formalize-algebraic-number-closure at a1491dbb4b9e6542b14d271de0cf7a4d1876a593. The latest observed PR and push workflows on that head, runs #339 and #338, both succeeded on 2026-11-14. The PR is not merged; its work must not be described as already present on main.

The PR branch reports:
- Lean toolchain leanprover/lean4:v4.36.0-rc2.
- Mathlib v4.36.0-rc2 with exact dependency revisions in lake-manifest.json.
- Frozen manifest verification; CI does not run lake update.
- lake build --wfail, a source scan for proof holes/custom axioms, project axiom audit, and paranoid theorem-contract comparison.
- The project axiom allowlist is propext, Classical.choice, and Quot.sound.
- The audit is limited to the declared project theorem wrappers and their dependencies; it is not an independent replay of every declaration in Mathlib's full import closure.

Links:
- PR #1: https://github.com/2503140kcsk-eng/G/pull/1
- Latest successful PR run #339: https://github.com/2503140kcsk-eng/G/actions/runs/43546714053
- Latest successful push run #338: https://github.com/2503140kcsk-eng/G/actions/runs/43546708018

### Already formalized on PR #1

1. Individual transcendence of e and pi via the project's Hermite-Lindemann development.
2. The unconditional disjunction: at least one of e+pi and e*pi is transcendental.
3. A Schanuel-conditional theorem implying transcendence of e+pi. Schanuel's conjecture is a theorem hypothesis, not an unconditional axiom.
4. A one-form irrationality criterion: an eventually nonzero integer linear form sequence tending to zero proves irrationality.
5. A stronger super-polynomial coefficient-height criterion implying the Liouville property and hence transcendence.
6. The exact mixed polynomial-integral identity and a formal quotient factorization through the endpoint-signature map.
7. Relative algebraic closure and finite-extension results.

The open unconditional target is deliberately not proved by these results.

## 2. The known mixed integral and its obstruction

For P in Z[X], define
\[
S_P(X)=\sum_{j=0}^{\deg P}(-1)^jP^{(j)}(X),\quad
A(P)=S_P(1),\quad C(P)=S_P(0).
\]
The alternating derivative sum telescopes:
\[
S_P'(X)+S_P(X)=P(X).
\]
Consequently,
\[
\int_0^1P(x)e^x\,dx=A(P)e-C(P).
\]
Together with
\[
4\int_0^1\frac{dx}{1+x^2}=\pi,
\]
this gives the exact identity
\[
\boxed{
\int_0^1\left(P(x)e^x+\frac{4A(P)}{1+x^2}\right)dx
=A(P)(e+\pi)-C(P).
}\tag{1}
\]

This identity is already present in Runlong Yu's 2026 preprint arXiv:2606.17303; it is not claimed as a new discovery.

The PR #1 module MixedKernelQuotient.lean formalizes the endpoint signature map and an explicit section:
\[
(a,c)\longmapsto (a-c)X+a.
\]
Therefore P maps onto every pair in Z^2 already in degree at most one. Merely writing an arbitrary integer linear form as an integral does not generate a special approximation. A useful sequence must have additional structure—orthogonality, recurrence, divisibility, positivity, or a determinant invariant—that forces the integral to be small.

A second important warning: degree growth alone does not help. The degree-lifting construction in PRIMITIVE_DENOMINATOR_STANDARD_2026-11-14.md shows that arbitrary endpoint pairs can be represented by polynomials of prescribed growing degree. What matters is a uniform asymptotic estimate after integerization and primitive reduction.

The symmetric endpoint-vanishing family P_n(X)=X^n(1-X)^n has been rigorously rejected: its endpoint content is n!, and its primitive linear forms diverge in absolute value. The small exponential integral is overwhelmed by the pi coefficient.

## 3. New fully proved mathematical criterion: paired determinant

For integer sequences A_n,C_n define
\[
L_n(x)=A_nx-C_n,\qquad
\Delta_n=A_nC_{n+1}-A_{n+1}C_n.
\]

### Theorem

If
\[
\Delta_n\ne0\quad\text{eventually}
\]
and
\[
|L_n(x)|+|L_{n+1}(x)|\longrightarrow0,
\]
then x is irrational.

### Proof

Suppose x=p/q with p,q integers and q nonzero. Choose a sufficiently large n with Delta_n nonzero. The two adjacent forms cannot both vanish: if A_n x=C_n and A_{n+1}x=C_{n+1}, then
\[
\Delta_n=A_n(A_{n+1}x)-A_{n+1}(A_nx)=0,
\]
a contradiction.

Thus at least one member of the pair is nonzero. Choose that member, say ax-c. Then
\[
ax-c=\frac{ap-cq}{q}.
\]
The numerator is an integer and is nonzero, so
\[
|ax-c|\ge\frac1{|q|}.
\]
But the selected term is bounded above by
\[
|L_n(x)|+|L_{n+1}(x)|,
\]
which tends to zero. Contradiction. Therefore x is irrational. QED.

This is stronger as a certificate format than asking that every L_n be nonzero: it is enough for each adjacent pair to contain a nonzero member, which follows from the determinant condition.

### Gram-square identity

For real x and A_1^2+A_2^2>0,
\[
\begin{aligned}
&(A_1x-C_1)^2+(A_2x-C_2)^2
-\frac{(A_1C_2-A_2C_1)^2}{A_1^2+A_2^2}\\
&=\frac{\big(A_1C_1+A_2C_2-(A_1^2+A_2^2)x\big)^2}
{A_1^2+A_2^2}\ge0.
\end{aligned}
\]
Wolfram's symbolic evaluator reduced the difference to exactly this square. The identity is elementary by expansion. For rational x=p/q, the stronger discrete statement
\[
L_n(x)^2+L_{n+1}(x)^2\ge q^{-2}
\]
follows because the two integer numerators cannot both vanish.

### Mixed-kernel specialization

For integer polynomials P_n, set
\[
A_n=A(P_n),\quad C_n=C(P_n),\quad
L_n=\int_0^1K_{P_n}(x)\,dx.
\]
It is enough to construct a family satisfying
\[
A_nC_{n+1}-A_{n+1}C_n\ne0
\quad\text{eventually}
\]
and
\[
|L_n|+|L_{n+1}|\longrightarrow0.
\]
Then the paired theorem yields e+pi irrational.

If g_n=gcd(|A_n|,|C_n|), primitive reduction gives
\[
\Delta_n^{\rm prim}=\frac{\Delta_n}{g_ng_{n+1}},
\]
so determinant nonvanishing survives. The primitive error is divided by g_n and therefore cannot become larger for an integer-coefficient construction. For rational-coefficient constructions, denominator clearing must be recorded before primitive reduction.

The paired criterion has been added on the current isolated research branch in lean/PairedApproximationCriteria.lean, with a wrapper in ProofAudit, a matching statement in ProofAuditChallenge, and an entry in comparator.json. The first CI attempt found a Lean simplification error in conditional selection. A correction has been pushed; do not claim this addition is verified until the latest branch CI, axiom audit, and Comparator all pass.

Research branch:
https://github.com/2503140kcsk-eng/G/tree/research/paired-determinant-certificate-2026-11-14

## 4. The missing problem

The missing theorem is not the determinant inequality or the rational lower bound. It is the existence of a degree-continuing arithmetic-analytic family with:
- integer endpoint coefficients;
- an eventually nonzero adjacent determinant;
- rigorous smallness of the primitive errors;
- explicit control of all denominator and coefficient growth.

A successful sequence of numerical near-approximants is not enough. Nor is an exact integral identity by itself. The same construction must generate arithmetic independence and analytic decay.

## 5. Research workstreams

### A. Mixed orthogonality and kernel design

Construct polynomial families satisfying nontrivial moment or orthogonality constraints for the coupled weights e^x and (1+x^2)^(-1). Explore whether multiple orthogonal polynomials or Rodrigues-type constructions can force cancellation in
\[
K_P(x)=P(x)e^x+\frac{4A(P)}{1+x^2}.
\]
The constraints must be additional to endpoint signature, because that map is surjective. Seek a sign or norm estimate for the kernel and a recurrence for endpoint coefficients.

Acceptance gate: exact integer coefficients, a proven determinant recurrence, and a uniform error bound that survives primitive reduction.

### B. Simultaneous Hermite-Pade with common denominators

Study simultaneous approximation of e^z and the arctangent representation
\[
\pi=16\arctan(1/5)-4\arctan(1/239).
\]
Do not simply add unrelated good approximations to e and pi. Seek a common orthogonality system and a common denominator that yield two adjacent independent endpoint pairs.

Acceptance gate: exact rational functions or polynomial recurrences, denominator bounds, a determinant formula, and a remainder estimate after clearing denominators and gcd reduction.

### C. Holonomic recurrences

Search for hypergeometric or holonomic polynomial families whose integrals obey integer-coefficient recurrences. Prove the determinant is nonzero through a recurrence invariant, then prove decay analytically.

Acceptance gate: a proved recurrence, initial conditions, a determinant invariant, and an asymptotic bound.

### D. Factorial-tail route

Yu's preprint gives exact arithmetic conditions forced by the rationality of e+pi, including a ceiling recurrence and factorial-divisibility criteria. Explore whether an independent analytic estimate contradicts one of these conditions for infinitely many indices. Do not infer failure from finite decimals or from the continued fraction of pi alone.

Acceptance gate: an unconditional infinite-index contradiction derived from an independent theorem.

### E. Transcendence upgrade

Only after an irrationality certificate is obtained, test whether its primitive error is smaller than every fixed inverse power of the primitive coefficient height. That stronger condition is already supported by the Liouville criterion in ApproximationCriteria.lean. Do not conflate the irrationality target with this stronger target.

## 6. Tool and plugin allocation

### Connected integrations actually relevant to this problem

| Resource | Responsibility | Deliverable and boundary |
|---|---|---|
| GitHub | Inspect exact repository state, manage isolated branches, commit research artifacts, and run pinned CI / axiom audit / Comparator. | Green CI certifies only the exact source and declarations built. |
| Sider Scholar | Discover papers on Hermite-Lindemann, Hermite-Pade, multiple orthogonal polynomials, Beukers integrals, and formalization. | Search hits are leads. The targeted search in this session was noisy and the direct arXiv record call hit rate limiting, so primary sources were checked independently. |
| Wolfram | Verify symbolic identities, exact finite recurrences, gcd tables, and high-precision candidate ledgers. | Finite computations are corroboration, never proof of a limit or nonvanishing. |
| Context7 | Retrieve current Lean/Mathlib APIs for polynomial derivatives, interval integrals, filters, irrationality, and algebraic extensions. | The pinned Lean elaborator and kernel—not documentation—decide validity. |
| Parallel Search | Independently check research status and discover primary references for Apéry, Beukers, orthogonality, and simultaneous Padé approaches. | Read-only search helps source discovery; it is not a proof assistant. |

Other available connected applications for design, project management, messaging, databases, analytics, deployment, and office work have no material role in a pure number-theory formalization and are intentionally not invoked. No paid CAS or hosted proof service is made a project dependency.

### Public GitHub Stars snapshot

The PR #1 branch records 30 public starred repositories on 2026-11-10 JST in TOOLS_AND_PROOF_PROTOCOL.md. The live starred endpoint was not accessible through the read-only connector in this session; therefore this is the recorded public snapshot, not a freshly verified live list.

| Repository | Assigned role |
|---|---|
| leanprover-community/mathlib4 | The only direct formal-mathematics dependency: field theory, polynomial calculus, integrals, filters, and transcendence, pinned to an exact revision. |
| google-deepmind/cryptids | Study Lean theorem organization and proof-engineering patterns. |
| VladimirReshetnikov/ProveIt | Compare reusable proof scripting and decomposition. |
| graph-theory-AI/graph-theory-rocq | Compare Rocq theorem organization and independent-assistant checking. |
| rocq-community/fourcolor | Study modular proof maintenance. |
| math-comp/math-comp | Compare field and algebraic hierarchy in an independent prover. |
| rocq-community/graph-theory | Reference finite-structure encodings only if a discrete auxiliary lemma emerges. |
| MizarSystem/MML | Compare formal definitions of algebraic numbers and field extensions. |
| rocq-archive/zfc | Optional foundations reference; no current dependency. |
| metamath/metamath-exe | Independently check a small foundational lemma if useful. |
| metamath/set.mm | Reference source for elementary algebra statements. |
| isabelle-prover/mirror-isabelle | Compare Isabelle/HOL theorem formulations. |
| isabelle-prover/mirror-afp-devel | Inspect AFP transcendence formalizations as porting blueprints. |
| bbchallenge/bbchallenge-proofs | Borrow reproducible proof-artifact and verification-report practices. |
| jeff87654/busy-beaver | Compare independent proof-audit organization; domain otherwise unrelated. |
| Macaulay2/M2 | Explore polynomial ideals, syzygies, elimination, and exact coefficient constraints in finite candidate families. |
| Singular/Singular | Cross-check Groebner bases and elimination. |
| flintlib/flint | Fast exact integer, gcd, factorial, and polynomial arithmetic. |
| sympy/sympy | Symbolically derive endpoint sums, recurrences, and finite identities. |
| sagemath/sage | Explore exact rational approximants, recurrences, embeddings, and LLL candidate generation. |
| gap-system/gap | Explore finite Galois groups and finite-field examples only. |
| emil79/flagmatic | Optional flag-algebra experiments if a combinatorial positivity constraint appears. |
| graphillion/graphillion | Optional finite graph-set computations if a combinatorial model appears. |
| graph-theory-AI/graph-conjectures | Track experimental sub-conjectures and counterexample protocols. |
| lean-dojo/LeanDojo-v2 | Retrieve tactic suggestions and proof traces; all suggestions must be checked in the pinned Lean kernel. |
| naproche/naproche | Audit written proofs for hidden assumptions, quantifiers, and missing intermediate claims. |
| cvc5/cvc5 | Check bounded polynomial identities, determinant side conditions, and finite counterexamples. |
| MeniRosenfeld/TransfiniteOrdinalCalculator | Retain as unrelated ordinal work; no role in this proof. |
| koteitan/basmat-2.x | Retain as unrelated integer/matrix growth work; no role in this proof. |
| hypcos/incremental-googology | Retain as unrelated large-number research; no role in this proof. |

Only Mathlib is imported as a direct mathematical package. CAS systems, LLMs, SMT solvers, and alternate proof assistants are discovery, experiment, or independent-review resources; their outputs do not enter the trusted Lean proof graph.

## 7. Execution order and gates

1. Freeze the exact PR #1 baseline and lockfile. Keep research work on isolated branches; do not overwrite the canonical proof trunk.
2. Validate the paired theorem. Require warning-free build, axiom audit within propext / Classical.choice / Quot.sound, and exact statement acceptance by Comparator in paranoid mode.
3. Prove analytic sublemmas before expanding the search space: endpoint recurrences, signs, moment orthogonality, and determinant recurrences.
4. Generate candidates only inside a proved structure. Use Sage, FLINT, SymPy, Macaulay2, GAP, or cvc5 for exact finite calculations and bounded searches.
5. Maintain a candidate ledger: degree, raw coefficients, clearing denominator, gcd/content, primitive pair, coefficient height, exact error identity, rigorous bounds, determinant, and continued-fraction-shadow classification.
6. Reject any family whose primitive errors do not tend to zero. Formalize the entire infinite argument, then rerun the pinned full CI and paranoid comparator.
7. Attempt transcendence only after irrationality; verify height-relative super-polynomial decay.

## 8. Stop rules

Reject a proposed mechanism if it relies on:
- decimal evidence for nonzero or small values;
- a small integral before multiplying by the integer coefficient or clearing denominators;
- finitely many low-degree cases extrapolated to all degrees;
- degree growth that merely re-encodes a chosen rational approximation;
- an individual nonvanishing claim inferred from a determinant that only proves pairwise non-simultaneous vanishing;
- Schanuel's conjecture reported as unconditional;
- a Lean sorry, custom axiom, native proof placeholder, or CAS output treated as proof.

## 9. Literature boundary

- Runlong Yu, “Tail Criteria, No-Go Audits, and Apéry-Type Certificate Obstructions for the Irrationality of e+pi,” arXiv:2606.17303 (2026 preprint): https://arxiv.org/abs/2606.17303
- F. Beukers, “Legendre Polynomials in Irrationality Proofs” (1980): https://doi.org/10.1017/S0004972700006742
- “Orthogonality and irrationality”: https://people.tamu.edu/~terdelyi/papers-online/zeta.pdf
- “Simultaneous Pade approximants to the Euler, exponential and logarithmic functions”: https://numdam.org/item/10.5802/jtnb.914.pdf
- Helen Joyce, “Mathematical mysteries: Transcendental meditation” (2002): https://plus.maths.org/content/mathematical-mysteries-transcendental-meditation

These references provide tools and context. None proves the irrationality of e+pi.
