# The Transcendence Status of e + π

> **Research status (2026-11-12): the unconditional transcendence of $e+\pi$ remains open; even its irrationality is not known.**

This repository formalizes established transcendence results and implications surrounding

$$e+\pi=\exp(1)+\pi.$$

It does **not** claim to solve the open irrationality or transcendence problem for $e+\pi$.

## What is formally proved

The Lean workspace contains a kernel-checked development of these results.

1. **Individual transcendence.** **Complex.transcendental_e** proves that $e=\exp(1)$, viewed in $\mathbb C$, is transcendental over $\mathbb Z$. **Real.transcendental_pi** proves that $\pi$ is transcendental over $\mathbb Z$. The bridge theorems **HermiteLindemannBridge.transcendental_e** and **HermiteLindemannBridge.transcendental_pi** derive the corresponding results over $\mathbb Q$.
2. **Algebraic closure.** Algebraic elements are closed under addition and multiplication. A root of a nonzero polynomial whose coefficients are algebraic over the base field is algebraic over that field.
3. **An unconditional disjunction.**
   $$\boxed{\text{At least one of }e+\pi\text{ and }e\pi\text{ is transcendental.}$$
   If both were algebraic, $e$ and $\pi$ would be roots of $X^2-(e+\pi)X+e\pi$, a polynomial over the algebraic numbers, contradicting their individual transcendence.
4. **A conditional theorem.** **SchanuelConditional.transcendental_ePlusPi_of_schanuel** proves that Schanuel's conjecture implies $e+\pi$ is transcendental. The conjecture is an explicit hypothesis to this theorem, not an axiom added to Lean's environment.

The conditional proof applies Schanuel's conjecture to $1$ and $i\pi$, obtains algebraic independence of $e$ and $i\pi$, transfers this through the algebraic extension $\mathbb Q(i)/\mathbb Q$, and derives a contradiction from any assumed algebraicity of $e+\pi$. This is a conditional implication, not an unconditional solution.

## What is not proved

The proposition **EPlusPiTranscendental** records the desired unconditional statement. No theorem in this repository proves it. It is not introduced as an axiom and is not hidden behind sorry, admit, or an unsound placeholder.

Separate transcendence of $e$ and $\pi$, as well as transcendence of $e^\pi$, does not by itself establish the transcendence—or even irrationality—of $e+\pi$.

## Reproducible Lean environment

- Lean toolchain: leanprover/lean4:v4.36.0-rc2
- Mathlib tag: v4.36.0-rc2
- Concrete Mathlib and eight transitive dependency revisions: lake-manifest.json
- Direct formal mathematics dependency: Mathlib only.
- CI uses the committed lockfile and **does not run lake update**.

From the repository root, after installing the pinned Lean toolchain, run lake exe cache get and lake build.

### Latest verified CI

On 2026-11-12, both push run #210 and PR run #211 succeeded on commit bd3336f71729581a0a4484e04703878f2acaa1a7.

- All 6,126 Lake build jobs completed.
- ProofAudit compiled.
- axiom-audit audited six explicitly typed principal theorem wrappers under the ProofAudit root.
- All audited declarations and their transitive proof dependencies stayed within propext, Classical.choice, and Quot.sound.
- The relevant axiom output for the individual transcendence, unconditional disjunction, and conditional Schanuel theorems showed only those same standard axioms.
- No sorryAx, admitAx, project-specific axiom, or Lean linter warning was reported.

The six audited entry points cover the complex e result, real π result, rational-base e result, rational-base π result, unconditional sum/product disjunction, and Schanuel-conditional e+π theorem. This is a project-proof dependency audit, **not** an independent replay of every declaration in Mathlib's entire transitive import closure.

[Successful push CI #210](https://github.com/2503140kcsk-eng/G/actions/runs/43198316263) · [Successful PR CI #211](https://github.com/2503140kcsk-eng/G/actions/runs/43198324014)

## Import minimization and source attribution

The umbrella public import Mathlib was removed from HermiteLindemannBridge.lean, EPlusPi.lean, and SchanuelConditional.lean. These files now use explicit project imports and focused Mathlib imports. In particular, the Schanuel module imports the transcendence-basis and multivariate-polynomial APIs it actually uses. The resulting workspace was rebuilt successfully under the pinned revision.

The vendored Lindemann–Weierstrass algebraic proof files retain their source copyright and author headers. The repository includes the exact Apache License 2.0 text from the pinned Mathlib release in LICENSE.

See [TOOLS_AND_PROOF_PROTOCOL.md](TOOLS_AND_PROOF_PROTOCOL.md) for role assignments for all recorded public GitHub Stars, connected integrations, the formal dependency boundary, and the proof-integrity policy.

## Literature and formalization references

- Runlong Yu, [Tail Criteria, No-Go Audits, and Apéry-Type Certificate Obstructions for the Irrationality of e+π](https://arxiv.org/abs/2606.17303), arXiv:2606.17303 (15 June 2026, preprint). It studies necessary conditions and bounded candidate approaches; it is not a proof of irrationality.
- Eric W. Weisstein, [Transcendental Number, Wolfram MathWorld](https://mathworld.wolfram.com/TranscendentalNumber.html).
- Eric W. Weisstein, [Schanuel's Conjecture, Wolfram MathWorld](https://mathworld.wolfram.com/SchanuelsConjecture.html).
- Helen Joyce, [Mathematical mysteries: Transcendental meditation](https://plus.maths.org/os/issue21/xfile/index) (2002).
- Archive of Formal Proofs, [The Transcendence of e](https://devel.isa-afp.org/entries/E_Transcendental.html) and [The Hermite–Lindemann–Weierstraß Transcendence Theorem](https://isa-afp.org/entries/Hermite_Lindemann.html). These are Isabelle/HOL formalizations, not Lean modules imported by this repository.
- Michail Karatarakis and Freek Wiedijk, [A formalization of the Gelfond–Schneider theorem](https://arxiv.org/abs/2603.24823) (2026 preprint), an adjacent Lean formalization that does not establish the transcendence of $e+\pi$.

The cited sources support the research-status assessment and formalization context; they do not prove the open target.
