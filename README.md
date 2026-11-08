# The Transcendence Status of e + π

> **Research status (2026-11-07): OPEN. No proof of the transcendence of e + π is known in the sources checked.**

This repository investigates the arithmetic nature of e + π = exp(1) + π.

## Main conclusion

The transcendence of e + π is **not currently established**. The separate transcendence of e and π, and the transcendence of e^π, do not imply the transcendence of their sum.

A useful unconditional fact is that at least one of e + π and eπ is transcendental. If both were algebraic, e and π would be roots of X² - (e + π)X + eπ, a nonzero polynomial over the algebraic numbers, contradicting the transcendence of e and π. This does **not** decide which of the sum and product is transcendental.

## Scope and honesty policy

- Formalize definitions and established implications.
- Keep the target statement explicitly marked **open**.
- Do not use axiom, sorry, fabricated lemma, or numerical experiment as a proof.
- A formal theorem is complete only when Lean's kernel checks it and #print axioms shows no unintended assumptions.
- Numerical approximations, symbolic simplification, and bounded searches cannot decide algebraicity.

## Repository map

- RESEARCH_STATUS.md: literature audit, theorem boundaries, and research plan.
- lean/EPlusPi.lean: exact target definition, intentionally without a theorem asserting it.
- lean/AlgebraicFieldClosure.lean: formal lemmas for inverse closure, integer powers, finite sets of algebraic generators, and the finite-generation/algebraicity criterion for finite extensions.
- lean/lean-toolchain and lean/lakefile.lean: pinned Lean/mathlib project configuration.
- .github/workflows/lean.yml: automatic Lean build and axiom audit on relevant pushes and pull requests.
- TOOLS_AND_PROOF_PROTOCOL.md: the role assignment for each named integration/repository, tool trust boundaries, and the unified proof architecture.

The algebraic-closure file proves standard field-theory results that form infrastructure for the main project. It does **not** prove that e + π is transcendental.

## Sources checked

1. Eric W. Weisstein, [Transcendental Number, Wolfram MathWorld](https://mathworld.wolfram.com/TranscendentalNumber.html).
2. Helen Joyce, [Mathematical mysteries: Transcendental meditation](https://plus.maths.org/os/issue21/xfile/index) (2002).
3. David S. Richeson, [How Math Achieved Transcendence](https://www.quantamagazine.org/recounting-the-history-of-maths-transcendental-numbers-20230627/) (2023).
4. Runlong Yu, [arXiv:2606.17303](https://arxiv.org/abs/2606.17303) (2026, preprint), on the irrationality of e + π.
5. [A formalization of the Gelfond–Schneider theorem](https://arxiv.org/html/2603.24823) (2026).

These references support the status assessment, not a proof. The arXiv items are preprints, not automatically peer-reviewed results.
