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
- lean/EPlusPi.lean: exact target definition, intentionally without a theorem asserting it.
- ALGEBRAIC_FIELD_CLOSURE_PROOF.md: complete hand proofs of inverse closure, integer powers, finite-dimensionality, the degree bound, and the finite-generation criterion.
- lean/AlgebraicFieldClosure.lean: Lean formalization of the corresponding statements.
- lean/AlgebraicFieldClosureChallenge.lean and lean/comparator.json: separately maintained theorem-statement baseline and Comparator configuration for the six field-theory declarations.
- lean/lean-toolchain and lean/lakefile.lean: pinned Lean/mathlib project configuration.
- .github/workflows/lean.yml: pinned Lean build and targeted multi-kernel Comparator audit on relevant pull requests; the full transitive-dependency audit is an opt-in manual run.
- TOOLS_AND_PROOF_PROTOCOL.md: roles for the named tools and repositories, their trust boundaries, and the unified proof architecture.

The algebraic-closure file proves standard field-theory results that form infrastructure for the main project. GitHub Actions Run #58 (2026-11-09, commit `315b2f2`) passed the warning-free Lean build, a downstream-import audit that checks the six exported theorem axiom sets, and the targeted Comparator multi-kernel audit. The check uses a separate statement baseline and explicit standard-axiom allowlist. Mathlib is pinned and treated as a trusted dependency for this targeted check; the full dependency-closure audit is a separate, stronger manual option. The field-theory results do **not** prove that e + π is transcendental.

## Sources checked

1. Eric W. Weisstein, [Transcendental Number, Wolfram MathWorld](https://mathworld.wolfram.com/TranscendentalNumber.html): explicitly lists e + π and eπ as unresolved individually, while at least one is transcendental.
2. Helen Joyce, [Mathematical mysteries: Transcendental meditation](https://plus.maths.org/os/issue21/xfile/index) (2002): explains the same sum/product argument and the Gelfond–Schneider result for e^π.
3. David S. Richeson, [How Math Achieved Transcendence](https://www.quantamagazine.org/recounting-the-history-of-maths-transcendental-numbers-20230627/) (2023): lists e + π among open classification problems.
4. Runlong Yu, [arXiv:2606.17303](https://arxiv.org/abs/2606.17303) (15 June 2026, preprint): concerns the still-open irrationality of e + π and audits certain Apéry-type approaches. It is not a proof of transcendence.
5. [A formalization of the Gelfond–Schneider theorem](https://arxiv.org/html/2603.24823) (2026): formalizes a major nearby theorem, but does not establish transcendence of e + π.

These references support the status assessment, not a proof. The arXiv items are preprints, not automatically peer-reviewed results.
