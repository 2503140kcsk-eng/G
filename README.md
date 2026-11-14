# The Transcendence Status of e + π

> **Research status (2026-11-14): the unconditional transcendence of $e+\pi$ remains open; even its irrationality is not known.**

This repository formalizes established transcendence results and implications surrounding

$$e+\pi=\exp(1)+\pi.$$

It does **not** claim to solve the open irrationality or transcendence problem for $e+\pi$.

## What is formally proved

The Lean workspace contains a kernel-checked development of these results.

1. **Individual transcendence.** **Complex.transcendental_e** proves that $e=\exp(1)$, viewed in $\mathbb C$, is transcendental over $\mathbb Z$. **Real.transcendental_pi** proves that $\pi$ is transcendental over $\mathbb Z$. The bridge theorems **HermiteLindemannBridge.transcendental_e** and **HermiteLindemannBridge.transcendental_pi** derive the corresponding results over $\mathbb Q$.
2. **Algebraic closure.** Algebraic elements are closed under addition and multiplication. A root of a nonzero polynomial whose coefficients are algebraic over the base field is algebraic over that field.
3. **An unconditional disjunction.**
   $\boxed{\text{At least one of }e+\pi\text{ and }e\pi\text{ is transcendental.}}$
   If both were algebraic, $e$ and $\pi$ would be roots of $X^2-(e+\pi)X+e\pi$, a polynomial over the algebraic numbers, contradicting their individual transcendence.
4. **A conditional theorem.** **SchanuelConditional.transcendental_ePlusPi_of_schanuel** proves that Schanuel's conjecture implies $e+\pi$ is transcendental. The conjecture is an explicit hypothesis to this theorem, not an axiom added to Lean's environment.

The conditional proof applies Schanuel's conjecture to $1$ and $i\pi$, obtains algebraic independence of $e$ and $i\pi$, transfers this through the algebraic extension $\mathbb Q(i)/\mathbb Q$, and derives a contradiction from any assumed algebraicity of $e+\pi$. This is a conditional implication, not an unconditional solution.

5. **Generic integer-linear-form criteria.** In `ApproximationCriteria.lean`, an eventually nonzero sequence of integer linear forms whose values tend to zero is proved to imply irrationality of its target real number. A stronger hypothesis—decay faster than every fixed inverse power of coefficient height—implies the Liouville property and hence transcendence. These are conditional criteria; the repository does not construct such a sequence for $e+\pi$.

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

On 2026-11-12, push run #258 and PR run #259 both succeeded on commit `f38989247ec9fdcc3351def8adf53e2f216c12d4`.

- All 6,137 Lake build jobs completed successfully.
- `ProofAudit` compiled, and `axiom-audit` audited eight explicitly typed theorem wrappers.
- All audited declarations and their transitive project-proof dependencies stayed within the allowlist `propext`, `Classical.choice`, and `Quot.sound`.
- The two new generic approximation criteria were included in the transitive audit; no `sorryAx`, `admitAx`, or project-specific axiom was reported.
- No Lean compiler or linter warning appeared in the build output. GitHub Actions emitted a separate Node.js 20 deprecation notice from `actions/checkout`.

The eight audited entry points cover the complex e result, real π result, rational-base e result, rational-base π result, unconditional sum/product disjunction, Schanuel-conditional e+π theorem, super-polynomial integer-linear-form criterion for transcendence, and nonzero-linear-forms-to-irrationality certificate. This is a project-proof dependency audit, **not** an independent replay of every declaration in Mathlib's entire transitive import closure.

[Successful push CI #258](https://github.com/2503140kcsk-eng/G/actions/runs/43239896375) · [Successful PR CI #259](https://github.com/2503140kcsk-eng/G/actions/runs/43239908647)

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


## Latest research continuation — 2026-11-14

The mixed-kernel direction has a new exact audit in [MIXED_KERNEL_AUDIT_2026-11-14.md](MIXED_KERNEL_AUDIT_2026-11-14.md). It proves that the degree-one map (P\mapsto(A(P),C(P))) already realizes every integer pair, and that the symmetric endpoint-vanishing choice (P_n(x)=x^n(1-x)^n) gives linear forms whose absolute values grow factorially rather than tend to zero. It also records why the factorial-tail divisibility condition is not a shortcut to irrationality. These are rigorous obstructions to specific approaches, not a proof of the open target.


## Integrated algebraic foundation — 2026-11-14

PR #1 remains the canonical proof workspace. Two reusable developments have been added without changing the dependency lockfile:

- `AlgebraicElements.lean` represents the elements of an extension field algebraic over its base as Mathlib's relative algebraic closure `algebraicClosure K E : IntermediateField K E`. Membership is equivalent to `IsAlgebraic K`; field operations therefore give closure under addition, subtraction, negation, multiplication, inverse, division, and integer powers. The module also records algebraicity and maximality of the relative closure, and its algebraic-closure properties when the ambient field is algebraically closed.
- `AlgebraicFieldClosure.lean` formalizes that a finite set of algebraic elements generates a finite-dimensional intermediate field, that elements of a finite-dimensional extension are algebraic, and that finite-dimensionality is equivalent to essential finite type plus algebraicity.

The PR #2 hand-written exposition also gives a product bound for the degree of a finitely generated extension using the tower law and a finite monomial spanning family. **That degree-product bound is not currently an exported Lean theorem in this integration**; the formal declarations above do not claim it.

### Expanded proof audit and theorem-contract check

`ProofAudit` now contains 27 typed theorem wrappers: the original eight principal e/π and approximation statements, 16 theorem results from the relative algebraic-closure module, and three finite-extension results. It also includes a wrapper definition for the inherited field structure. CI's project axiom audit is rooted at `ProofAudit`.

`ProofAuditChallenge.lean` and the root `comparator.json` provide a separate specification for those 27 theorem statements. The challenge file intentionally contains `sorry` placeholders, as required by Lake Comparator; it is not imported by the solution or by `ProofAudit`, and is excluded from default build targets. The solution side must match every challenge theorem type and satisfy the explicit allowlist `propext`, `Classical.choice`, and `Quot.sound`. The comparator is configured with `--paranoid` so the pinned toolchain's available independent checkers are invoked as well as Lean's kernel.

The workflow also checks the exact Git blob hash of `lake-manifest.json` and the Lean toolchain string before building. It does not run `lake update`. The committed manifest blob is `5625e0bc21b731d5737a903c674bf4b6fb0e018c`; the PR #1 integration did not edit it.

`ProofAuditDefs.lean` is the sole shared statement-definition module. It imports Mathlib only and contains one transparent proposition definition: Schanuel's conjecture in its standard transcendence-degree form. Both Challenge and Solution import this same reviewed definition, avoiding a mismatch caused by unfolding the implementation's local alias through hidden `Complex.exp` internals. It contains no theorem proof, axiom, or proof hole. The Challenge otherwise uses Mathlib vocabulary; its 27 `sorry` placeholders are specifications only and are not imported by `ProofAudit` or any solution module.

### Latest verified CI — 2026-11-14

PR Run #309 on commit `3f9aa564d97244c513c9f44faa757e24d488c347` succeeded: [GitHub Actions Run #309](https://github.com/2503140kcsk-eng/G/actions/runs/43534926824).

- The frozen manifest and pinned Lean toolchain checks passed.
- The implementation-source scan found no `sorry`, `admit`, custom `axiom`, `sorryAx`, `admitAx`, or native proof placeholder.
- The default workspace passed `lake build --wfail`.
- The project axiom audit examined 33 declarations under `ProofAudit`; every declaration stayed within `propext`, `Classical.choice`, and `Quot.sound`.
- Comparator accepted all 27 public theorem statements. Its paranoid run was accepted by the Lean paranoid kernel, Lean's default kernel, lean4lean, nanoda, con-leche, and con-ron. con-leche and con-ron each accepted 57,722 declarations.
- The 27 theorem names in `ProofAudit`, `ProofAuditChallenge`, and `comparator.json` match exactly.

The audit still does not independently replay Mathlib's entire transitive import closure; Mathlib remains the pinned trusted mathematical library. This integration proves the stated field-theory and transcendence consequences, but does **not** establish unconditional irrationality or transcendence of `e + π`. That target remains explicitly open and is not represented as a proved theorem.



## Latest research continuation — common-denominator fusion (2026-11-14)

A new independent research branch, **research/common-denominator-fusion-2026-11-14**, formalizes an exact way to combine separate rational approximations \(p_n/q_n\approx x\) and \(s_n/r_n\approx y\) into an integer linear form:
\[
(q_nr_n)(x+y)-(r_np_n+q_ns_n)
=r_n(q_nx-p_n)+q_n(r_ny-s_n).
\]
Consequently the fused form is small only when the **cross-weighted errors**
\[
r_n|q_nx-p_n|+q_n|r_ny-s_n|
\]
tend to zero, and it must also be eventually nonzero. The sufficient implication from these hypotheses to irrationality of \(x+y\) is formalized and added as the 30th Comparator contract.

A lacunary-series example in [COMMON_DENOMINATOR_FUSION_AUDIT_2026-11-14.md](COMMON_DENOMINATOR_FUSION_AUDIT_2026-11-14.md) shows why separate errors tending to zero do not suffice: multiplying by the opposite denominators can make the fused error diverge. This is an obstruction to naive approximation fusion, not a result about the actual values of e and π.

CI push run #368 succeeded on commit 6f49702caca4abded88e8e4463e2cc29261430ee: [GitHub Actions run #368](https://github.com/2503140kcsk-eng/G/actions/runs/43586720392). The pinned build, warning-free build, axiom audit, 30-contract Comparator, Lean paranoid kernel, lean4lean, nanoda, con-leche, con-ron, and Lean default kernel all passed. The implementation still does **not** construct a cross-weighted error sequence for e and π; unconditional irrationality or transcendence of e + π remains unproved.
