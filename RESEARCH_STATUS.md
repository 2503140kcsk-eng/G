# Research status and formalization plan

**Snapshot date:** 2026-11-07  
**Question:** Is e + π transcendental?

## 1. Status

**Open / unknown in the literature checked.** Available sources explicitly state that the transcendence of e + π has not been proved. Even the weaker statement that e + π is irrational remains open in the June 2026 preprint cited below. Thus a complete proof of transcendence would also resolve the irrationality question, but no such proof was found.

This is a literature-status conclusion, not a mathematical proof that no proof exists anywhere. A newly published result after the checked sources could change the status.

## 2. Established facts and the exact gap

- e is transcendental (Hermite, 1873).
- π is transcendental (Lindemann, 1882).
- e^π is transcendental (Gelfond–Schneider theorem).
- It is not known whether e + π is irrational, let alone transcendental.
- At least one of e + π and eπ is transcendental.

For the last statement, suppose both s=e+π and p=eπ were algebraic. Then e and π are roots of X²-sX+p. Since the algebraic numbers form a field and every root of a polynomial over an algebraic extension of Q is algebraic over Q, both e and π would be algebraic, contradiction.

**Important:** this proves a disjunction, not that the sum is transcendental. It is invalid to infer that a sum of two transcendental numbers must be transcendental.

## 3. Why familiar theorems do not close the gap

- Lindemann–Weierstrass controls linear independence of exponentials of algebraic numbers. The summand π is not an exponential of an algebraic number in a way that lets the theorem directly classify e + π.
- Gelfond–Schneider proves transcendence of values a^b for algebraic a≠0,1 and irrational algebraic b. Its standard application gives e^π, not e + π.
- Baker's theorem on linear forms in logarithms of algebraic numbers does not immediately apply to the additive combination e + π.
- Schanuel's conjecture would imply algebraic independence of e and π, and hence transcendence of e + π. But Schanuel's conjecture is unproved; using it gives only a conditional theorem.

A conditional implication must be labelled conditional and must not be reported as an unconditional proof.

## 4. Formalization plan

### Layer A — exact definitions

Define the target as exp(1)+π in R. Define algebraicity/transcendence by polynomial roots over Q, or reuse the exact Mathlib predicate after checking its current source/API.

### Layer B — basic algebraic lemmas

Formalize:
1. If x,y are algebraic over Q, then x+y and xy are algebraic.
2. If s,p are algebraic, then every root of X²-sX+p is algebraic.
3. Consequently, if e and π are both transcendental, then at least one of e+π, eπ is transcendental.

The third lemma is a valuable unconditional theorem that can be proved without solving the open problem.

### Layer C — classical transcendence inputs

Import or formalize the Hermite and Lindemann results only if they are available in the selected Lean library or independently verified in the project. Do not assert that Mathlib contains these theorems until the exact declaration and import path have been checked.

### Layer D — unresolved target

State the target as a proposition/conjecture, not as an axiom and not as a theorem with sorry. It must remain unproved until a genuine argument is found.

### Layer E — audit

Run the pinned Lean/mathlib build, #print axioms for every claimed theorem, and search for sorry, admit, custom axioms, and theorem declarations that merely restate the target.

## 5. Research directions (not claimed proofs)

1. Investigate whether a new irrationality measure or a sequence of nonzero integer linear forms A_n(e+π)+B_n tending to zero can be constructed with denominators and errors satisfying a genuine contradiction criterion.
2. Test whether a mixed Hermite–Padé construction can produce integer forms A_n(e+π)+B_n→0 while keeping coefficient growth below analytic decay. The 2026 preprint reports obstructions for several bounded low-complexity families; this does not rule out all constructions.
3. Study conditional consequences of Schanuel's conjecture separately from unconditional work.
4. Compare the Lean development with existing formalizations of Hermite–Lindemann and Gelfond–Schneider in other proof assistants. Porting a theorem is substantial work and does not itself solve the sum problem.

## 6. Literature

- MathWorld, [Transcendental Number](https://mathworld.wolfram.com/TranscendentalNumber.html).
- Plus Maths, [Mathematical mysteries: Transcendental meditation](https://plus.maths.org/os/issue21/xfile/index).
- Quanta Magazine, [How Math Achieved Transcendence](https://www.quantamagazine.org/recounting-the-history-of-maths-transcendental-numbers-20230627/).
- Runlong Yu, [Tail Criteria, No-Go Audits, and Apéry-Type Certificate Obstructions for the Irrationality of e+π](https://arxiv.org/abs/2606.17303), arXiv:2606.17303 (2026, preprint).
- [A formalization of the Gelfond–Schneider theorem](https://arxiv.org/html/2603.24823) (2026, preprint).
- Archive of Formal Proofs, [The Hermite–Lindemann–Weierstraß Transcendence Theorem](https://devel.isa-afp.org/entries/Hermite_Lindemann.html) (Isabelle/HOL, not Lean/mathlib).

## 7. Tool roles and limits

- Sider Scholar: academic discovery; results must be individually inspected for relevance and publication status.
- Parallel Search/Research: current literature cross-check.
- Wolfram: symbolic/numeric corroboration only; numerical computation cannot prove transcendence.
- Context7: current Lean/mathlib API documentation.
- Lean/mathlib: kernel-checked formal proofs of the lemmas actually established.
- Macaulay2, GAP, SymPy, SageMath, cvc5, LeanDojo: exploratory algebra, symbolic experiments, search, and proof-assistance. None can turn an unproved number-theoretic conjecture into a theorem by computation alone.

The GitHub repository access confirms write permission. This status document deliberately does not claim that the open target has been solved.
