# Common-Denominator Fusion and the Cross-Weighted Error Criterion

**Date:** 2026-11-14  
**Branch:** research/common-denominator-fusion-2026-11-14  
**Verified Lean commit:** 6f49702caca4abded88e8e4463e2cc29261430ee  
**Status:** The general fusion identity, absolute-error bound, and conditional irrationality theorem are kernel-checked. No approximating sequence for e and π satisfying the hypotheses has been constructed.

## 1. Exact fusion identity

Let \(x,y\in\mathbb R\), \(q,r\in\mathbb N\), and \(p,s\in\mathbb Z\). Put
\[
A=qr,\qquad B=-(rp+qs).
\]
Then
\[
A(x+y)+B=r(qx-p)+q(ry-s).
\tag{1}
\]
In particular,
\[
|A(x+y)+B|\le r|qx-p|+q|ry-s|.
\tag{2}
\]

The right-hand side is the **cross-weighted error budget**. It is not the sum of the original approximation errors: each error is multiplied by the denominator of the *other* approximation.

The Lean development makes this distinction explicit:

- **commonDenominatorCoefficient q r** is \(qr\);
- **commonDenominatorConstant q r p s** is \(-(rp+qs)\);
- **commonDenominatorScaledError x y q r p s** is \(r|qx-p|+q|ry-s|\).

The exact identity is **EPlusPiApproximation.commonDenominator_form_identity**; the estimate is **commonDenominator_form_abs_le**.

## 2. Conditional irrationality theorem

For sequences \(q_n,r_n\in\mathbb N\) and \(p_n,s_n\in\mathbb Z\), define
\[
L_n=(q_nr_n)(x+y)-(r_np_n+q_ns_n).
\]
If
\[
L_n\ne0\quad\text{for all sufficiently large }n
\tag{3}
\]
and
\[
r_n|q_nx-p_n|+q_n|r_ny-s_n|\longrightarrow0,
\tag{4}
\]
then (2) implies \(L_n\to0\). The repository's existing integer-linear-form criterion therefore gives
\[
x+y\notin\mathbb Q.
\]

The complete Lean theorem is **EPlusPiApproximation.irrational_of_common_denominator_approximations**. Its public contract is independently stated as **ProofAudit.irrational_of_common_denominator_approximations** in the Comparator challenge. The theorem assumes eventual non-vanishing; the formalization does not infer this from the approximation errors.

**Interpretation:** equation (4), not the two separate limits alone, is the sufficient smallness condition after denominator clearing.

## 3. Why separate convergence is insufficient

Here is an explicit general counterexample to the naive implication
\[
q_nx-p_n\to0,\quad r_ny-s_n\to0
\quad\Longrightarrow\quad
r_n|q_nx-p_n|+q_n|r_ny-s_n|\to0.
\]
The implication is false.

Set
\[
q_1=2,\qquad q_{n+1}=q_n^2,\qquad r_n=q_n^3,
\]
and define
\[
x=\sum_{j=1}^{\infty}\frac1{q_j},
\qquad
y=\sum_{j=1}^{\infty}\frac1{r_j}.
\]
For each \(n\), put
\[
p_n=\sum_{j=1}^{n}\frac{q_n}{q_j},
\qquad
s_n=\sum_{j=1}^{n}\frac{r_n}{r_j}.
\]
These are integers because \(q_j\mid q_n\) and \(r_j\mid r_n\) whenever \(j\le n\).

Since \(q_{n+k}=q_n^{2^k}\),
\[
0<q_nx-p_n
=\sum_{k=1}^{\infty}q_n^{1-2^k}
\le\sum_{k=1}^{\infty}q_n^{1-2k}
=\frac{1}{q_n(1-q_n^{-2})}
\le\frac{4}{3q_n}.
\]
The first term in the sum is \(1/q_n\), so
\[
\frac1{q_n}\le q_nx-p_n\le\frac4{3q_n}\longrightarrow0.
\]
The same argument applies to \(r_ny-s_n\), because \(r_{n+k}=r_n^{2^k}\):
\[
\frac1{r_n}\le r_ny-s_n\le\frac4{3r_n}\longrightarrow0.
\]
Nevertheless,
\[
r_n|q_nx-p_n|+q_n|r_ny-s_n|
\ge\frac{r_n}{q_n}
=q_n^2\longrightarrow\infty.
\]
Both individual integer-linear-form errors tend to zero, but their product-denominator fusion error diverges. All terms are positive here, so there is no cancellation hidden in the bound.

This example concerns arbitrary real numbers defined by rapidly convergent series. It is **not** an approximation to e or π, and it is not a counterexample to the conditional Lean theorem. It isolates the precise denominator-growth obstruction.

## 4. Application boundary for e + π

Taking \(x=e\) and \(y=\pi\) in (1) yields an integer linear form in \(e+\pi\):
\[
(q_nr_n)(e+\pi)-(r_np_n+q_ns_n).
\]
To use the theorem, a future construction must establish all of the following for the *same* index \(n\):

1. integer denominators \(q_n,r_n\) and integer numerators \(p_n,s_n\);
2. eventual non-vanishing of the fused form;
3. the cross-weighted decay
   \[
   r_n|q_ne-p_n|+q_n|r_n\pi-s_n|\to0.
   \]

Separate rational approximations to e and π do not automatically satisfy item 3. An approximation scheme that improves each unweighted error can still fail after the opposite denominator is applied.

This module proves a reusable conditional implication. **It does not produce the required sequence for e and π, so it proves neither irrationality nor transcendence of e + π.** The repository's stated open-problem boundary remains unchanged.

## 5. Literature context

The denominator-clearing issue is explicitly emphasized in Runlong Yu, *Tail Criteria, No-Go Audits, and Apéry-Type Certificate Obstructions for the Irrationality of e + π*, arXiv:2606.17303v1 (2026-06-15). That preprint audits crossed separate approximations and other bounded low-complexity constructions; it reports obstructions from coefficient growth and denominator clearing within the tested families, not a universal impossibility theorem. [arXiv record](https://arxiv.org/abs/2606.17303).

For standard terminology, Walter Van Assche's lecture notes *Padé and Hermite-Padé Approximation and Orthogonality* (2006) define Type II Hermite-Padé approximation using a common denominator for several functions. This is relevant background for simultaneous rational approximation, but is not a proof of the arithmetic conditions above. [EMIS copy](https://emis.de/ft/47080).

## 6. Lean and CI evidence

The formal files added or extended on the research branch are:

- lean/CommonDenominatorApproximationDefs.lean
- lean/CommonDenominatorApproximation.lean
- lean/ProofAudit.lean
- lean/ProofAuditChallenge.lean
- lakefile.lean
- comparator.json

The root Comparator contains 30 public theorem contracts, including the new common-denominator theorem. The challenge's sorry is a specification placeholder only; it is not imported by the solution or included in the implementation proof-hole scan.

Successful GitHub Actions push run #368: [run 43586720392](https://github.com/2503140kcsk-eng/G/actions/runs/43586720392), commit 6f49702caca4abded88e8e4463e2cc29261430ee.

Verified CI results:

- frozen Lake manifest and pinned Lean 4.36.0-rc2 checks passed;
- the implementation source scan passed;
- the default build completed (18,230 Lake jobs);
- lake build --wfail passed;
- axiom-audit audited 39 declarations under ProofAudit, all within propext, Classical.choice, and Quot.sound;
- the new public wrapper's own #print axioms output lists only those same three standard axioms;
- the 30-contract Comparator and paranoid step completed successfully;
- Lean paranoid kernel accepted the solution;
- lean4lean checked 57,995 declarations and accepted the solution;
- nanoda accepted the solution;
- con-leche accepted 57,994 declarations;
- con-ron accepted 57,994 declarations;
- Lean's default kernel accepted the solution.

The project continues to use the frozen manifest; no dependency refresh was performed. This audit does not claim independent replay of every declaration in Mathlib's entire transitive import closure.
