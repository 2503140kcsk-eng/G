# The Transcendence Status of e + π

> **Research status (2026-11-07): OPEN. No proof of the transcendence of e + π is known in the sources checked.**

This repository investigates the arithmetic nature of
\[
e+\pi=\exp(1)+\pi.
\]

## Main conclusion

The transcendence of e + π is **not currently established**. The separate transcendence of e and π, and the transcendence of e^π, do not imply the transcendence of their sum.

A useful unconditional fact is:

\[
\boxed{\text{At least one of }e+\pi\text{ and }e\pi\text{ is transcendental.}}
\]

Proof: if both were algebraic, then e and π would be roots of
\[
X^2-(e+\pi)X+e\pi,
\]
a nonzero polynomial over the algebraic numbers. Hence both would be algebraic, contradicting the Hermite and Lindemann theorems. This does **not** decide which of the sum and product is transcendental.

## Scope and honesty policy

- Formalize definitions and established implications.
- Keep the target statement explicitly marked **open**.
- Do not use axiom, sorry, fabricated lemma, or numerical experiment as a proof.
- A formal theorem is complete only when Lean's kernel checks it and #print axioms shows no unintended assumptions.
- Numerical approximations, symbolic simplification, and bounded searches cannot decide algebraicity.

## Repository map

- RESEARCH_STATUS.md: literature audit, theorem boundaries, and research plan.
- lean/: Lean formalization workspace (to be bootstrapped against a pinned mathlib revision).

## Sources checked

1. Eric W. Weisstein, [Transcendental Number, Wolfram MathWorld](https://mathworld.wolfram.com/TranscendentalNumber.html): explicitly lists e + π and eπ as unresolved individually, while at least one is transcendental.
2. Helen Joyce, [Mathematical mysteries: Transcendental meditation](https://plus.maths.org/os/issue21/xfile/index) (2002): explains the same sum/product argument and the Gelfond–Schneider result for e^π.
3. David S. Richeson, [How Math Achieved Transcendence](https://www.quantamagazine.org/recounting-the-history-of-maths-transcendental-numbers-20230627/) (2023): lists e + π among open classification problems.
4. Runlong Yu, [arXiv:2606.17303](https://arxiv.org/abs/2606.17303) (15 June 2026, preprint): concerns the still-open irrationality of e + π and audits certain Apéry-type approaches. It is not a proof of transcendence.
5. [A formalization of the Gelfond–Schneider theorem](https://arxiv.org/html/2603.24823) (2026): formalizes a major nearby theorem, but does not establish transcendence of e + π.

These references support the status assessment, not a proof. The arXiv items are preprints, not automatically peer-reviewed results.
