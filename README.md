# The Transcendence Status of e + π

> **Research status (2026-11-11): the unconditional transcendence of (e+pi) remains open; even its irrationality is not known.**

This repository formalizes established transcendence results and implications surrounding

[
e+pi=exp(1)+pi.
]

It does **not** claim to solve the open irrationality or transcendence problem for (e+pi).

## What is now formally proved

The Lean workspace contains a kernel-checked development of the following results.

1. **Individual transcendence.** `Complex.transcendental_e` proves that (e=exp(1)), viewed in (mathbb C), is transcendental. `Real.transcendental_pi` proves that (pi) is transcendental. `HermiteLindemannBridge.transcendental_e` and `HermiteLindemannBridge.transcendental_pi` provide the corresponding results over (mathbb Q).
2. **Algebraic closure lemmas.** Algebraic elements are closed under addition and multiplication; a root of a nonzero polynomial whose coefficients are algebraic over the base field is algebraic over that field.
3. **An unconditional disjunction.**
   [
   oxed{	ext{At least one of }e+pi	ext{ and }epi	ext{ is transcendental.}}
   ]
   If both were algebraic, (e) and (pi) would be roots of (X^2-(e+pi)X+epi), a polynomial over the algebraic numbers, contradicting their individual transcendence.
4. **A conditional theorem.** `SchanuelConditional.transcendental_ePlusPi_of_schanuel` proves that Schanuel's conjecture implies (e+pi) is transcendental. The conjecture is an explicit hypothesis to this theorem, not an axiom added to Lean's environment.

The conditional proof applies Schanuel's conjecture to (1) and (ipi), obtains algebraic independence of (e) and (ipi), transfers this through the algebraic extension (mathbb Q(i)/mathbb Q), and derives a contradiction from any assumed algebraicity of (e+pi). This is a conditional implication, not an unconditional solution.

## What is not proved

The proposition `EPlusPiTranscendental` records the desired unconditional statement. No theorem in this repository proves it. It is not introduced as an axiom and is not hidden behind `sorry`, `admit`, or an unsound placeholder.

Separate transcendence of (e) and (pi), as well as transcendence of (e^pi), does not by itself establish the transcendence—or even irrationality—of (e+pi).

## Reproducible Lean environment

- Lean toolchain: `leanprover/lean4:v4.36.0-rc2`
- Mathlib tag: `v4.36.0-rc2`
- Concrete Mathlib and transitive dependency revisions: `lake-manifest.json`
- Direct formal mathematics dependency: Mathlib only.
- CI uses the committed lockfile; it does not refresh dependencies as part of verification.

From the repository root, after installing the pinned Lean toolchain:

```sh
lake exe cache get
lake build
```

The CI workflow also runs the configured axiom audit. In the successful 2026-11-11 build logs, the relevant declarations in `AlgebraicClosure`, `HermiteLindemannBridge`, `EPlusPi`, and `SchanuelConditional` reported only `propext`, `Classical.choice`, and `Quot.sound`. The automated `axiom-audit` action specifically audited the 13 declarations in `AlgebraicClosure`; it did not independently audit every imported Mathlib declaration.

See [TOOLS_AND_PROOF_PROTOCOL.md](TOOLS_AND_PROOF_PROTOCOL.md) for role assignments for the recorded public GitHub Stars set, connected tools, the formal dependency boundary, and the proof-integrity policy.

## Literature and formalization references

- Runlong Yu, [Tail Criteria, No-Go Audits, and Apéry-Type Certificate Obstructions for the Irrationality of e+π](https://arxiv.org/abs/2606.17303), arXiv:2606.17303 (15 June 2026, preprint). It studies necessary conditions and bounded candidate approaches; it is not a proof of irrationality.
- Eric W. Weisstein, [Transcendental Number, Wolfram MathWorld](https://mathworld.wolfram.com/TranscendentalNumber.html), which records the unresolved status of (e+pi) and (epi) individually and the disjunction result.
- Helen Joyce, [Mathematical mysteries: Transcendental meditation](https://plus.maths.org/os/issue21/xfile/index) (2002), for the sum/product argument and the Gelfond–Schneider context.
- Archive of Formal Proofs, [The Transcendence of e](https://devel.isa-afp.org/entries/E_Transcendental.html) and [The Hermite–Lindemann–Weierstraß Transcendence Theorem](https://isa-afp.org/entries/Hermite_Lindemann.html). These are Isabelle/HOL formalizations, not Lean modules imported by this repository.
- [A formalization of the Gelfond–Schneider theorem](https://arxiv.org/html/2603.24823) (2026 preprint), a nearby formalization result that does not establish the transcendence of (e+pi).

The cited sources support the research-status assessment and formalization context; they do not prove the open target.
