# Primitive denominator-survival standard and degree-lift audit

**Date:** 2026-11-14 (JST)  
**Repository:** 2503140kcsk-eng/G  
**Branch:** formalize-algebraic-number-closure  
**Status:** Exact structural results and one primitive-family rejection; no unconditional e+pi certificate sequence has been constructed.

> This note does not prove that \(e+\pi\) is irrational or transcendental. It proves that the requested exact-degree polynomial-family property is equivalent to irrationality of \(e+\pi\), sharpens denominator/gcd bookkeeping, and rejects one explicit family after primitive reduction. The target remains open in the literature checked through 2026-11-14.

## 1. Standard object: the primitive integer form

Put \(\alpha=e+\pi\). Start with a rational-coefficient form
\[
\Lambda_n=u_n\alpha-v_n,\qquad u_n,v_n\in\mathbb Q.
\]
Choose a positive integer common denominator \(D_n\), and set
\[
a_n=D_nu_n\in\mathbb Z,\qquad c_n=D_nv_n\in\mathbb Z.
\]
The denominator-cleared form is
\[
R_n=a_n\alpha-c_n=D_n\Lambda_n.
\]
For \((a_n,c_n)\ne(0,0)\), define the content
\[
g_n=\gcd(|a_n|,|c_n|)>0,
\]
the primitive coefficients
\[
A_n=a_n/g_n,\qquad C_n=c_n/g_n,
\]
and the primitive form and height
\[
L_n=A_n\alpha-C_n,\qquad H_n=\max(2,|A_n|,|C_n|).
\]

The exact scale identity is
\[
\boxed{
L_n=\frac{D_n}{g_n}\Lambda_n,\qquad
|L_n|=\frac{D_n}{g_n}|\Lambda_n|.
}
\tag{1.1}
\]
Every candidate must therefore report three errors:
\[
\varepsilon_n^{\rm an}=|\Lambda_n|,\quad
\varepsilon_n^{\rm clear}=D_n\varepsilon_n^{\rm an},\quad
\varepsilon_n^{\rm prim}=\frac{D_n}{g_n}\varepsilon_n^{\rm an}.
\tag{1.2}
\]
The final quantity, not the first two, must tend to zero.

Call \(\delta_n=D_n/g_n>0\) the **primitive survival multiplier**. It is invariant under replacing \(D_n\) by \(kD_n\) and \((a_n,c_n)\) by \((ka_n,kc_n)\), for any positive integer \(k\). With a minimal common denominator, \(\delta_n\) need not be an integer; it is a positive rational scale.

For an integer-polynomial construction, \(D_n=1\). Primitive reduction then divides the raw error by \(g_n\), so it cannot worsen it. Denominator-clearing loss occurs when the pre-integerized coefficients are rational. These two effects must not be conflated.

### 1.1 Required candidate ledger

| Field | Required record |
|---|---|
| Degree | Exact degree of \(P_n\), not just its index |
| Rational data | \(u_n,v_n,D_n\), with \(D_n\) a stated common denominator |
| Cleared integers | \(a_n=D_nu_n,\ c_n=D_nv_n\) |
| Content | \(g_n=\gcd(|a_n|,|c_n|)\), with proof or “finite computation only” |
| Primitive pair | \(A_n=a_n/g_n,\ C_n=c_n/g_n\), and \(\gcd(|A_n|,|C_n|)=1\) |
| Height | \(H_n=\max(2,|A_n|,|C_n|)\) |
| Analytic error | Exact identity and rigorous upper/lower bounds for \(\varepsilon_n^{\rm an}\) |
| Cleared error | Exact value \(D_n\varepsilon_n^{\rm an}\) |
| Primitive error | Exact value \((D_n/g_n)\varepsilon_n^{\rm an}=|A_n\alpha-C_n|\) |
| Non-vanishing | Proof of eventual nonzero; decimals do not count |
| Limit | Proof that the primitive error tends to zero; finite tables do not count |
| CF audit | Whether \(C_n/A_n\) is a continued-fraction convergent/intermediate convergent, and how this is certified |

A candidate is not a certificate until both non-vanishing and the primitive-limit statement are proved.

## 2. Exact degree-lifting lemma

For \(P\in\mathbb Z[X]\), the existing mixed-endpoint construction uses
\[
S_P(X)=\sum_{j=0}^{\deg P}(-1)^jP^{(j)}(X),\quad
A(P)=S_P(1),\quad C(P)=S_P(0).
\]
The alternating sum telescopes to \(S_P'+S_P=P\), and the mixed integral identity is
\[
\int_0^1\left(P(x)e^x+\frac{4A(P)}{1+x^2}\right)dx
=A(P)(e+\pi)-C(P).
\tag{2.1}
\]
This identity already appears in Runlong Yu's 2026 preprint; it is not claimed as a new identity.

### Lemma 2.1 (degree-lifting section)

For any \(a,c\in\mathbb Z\) and \(n\ge2\), let
\[
\begin{aligned}
T_{n,a,c}(X)&=(a-c)X+c+X^{n+1}-X^n,\\
P_{n,a,c}(X)&=T_{n,a,c}'(X)+T_{n,a,c}(X)\\
&=(a-c)X+a+X^{n+1}+nX^n-nX^{n-1}.
\end{aligned}
\]
Then \(P_{n,a,c}\in\mathbb Z[X]\), \(\deg P_{n,a,c}=n+1\), and
\[
A(P_{n,a,c})=a,\qquad C(P_{n,a,c})=c.
\]

**Proof.** For every polynomial \(P\), the finite alternating derivative sum satisfies \(S_P'+S_P=P\): the derivative terms of orders \(1,\ldots,\deg P\) cancel, and the next derivative is zero.

The polynomial \(S_P\) is the unique polynomial \(T\) satisfying \(T'+T=P\). If \(U'+U=0\) and \(U\ne0\), then \(\deg U'<\deg U\) when \(U\) is nonconstant, so its leading term cannot cancel; if \(U\) is constant, \(U'=0\), again forcing \(U=0\). Thus the homogeneous equation has only the zero polynomial solution.

By construction \(T_{n,a,c}'+T_{n,a,c}=P_{n,a,c}\), so uniqueness gives \(S_{P_{n,a,c}}=T_{n,a,c}\). Evaluating at the endpoints gives \(S(1)=a\) and \(S(0)=c\). Finally, the coefficient of \(X^{n+1}\) in \(P_{n,a,c}\) is \(1\), and all other terms have degree at most \(n\) for \(n\ge2\). Hence its degree is exactly \(n+1\). \(\square\)

Wolfram's symbolic evaluator checked the displayed identities for \(n=2,\ldots,6\). The proof above is the general argument; those finite checks are corroboration only.

### Corollary 2.2 (degree growth is equivalent to the open irrationality target)

For a real number \(\alpha\), the following are equivalent:

1. \(\alpha\notin\mathbb Q\).
2. There is a sequence \(P_n\in\mathbb Z[X]\), with \(\deg P_n=n+1\) for every \(n\ge2\), such that
   \[
   0<|A(P_n)\alpha-C(P_n)|\longrightarrow0.
   \]

**Proof.**

If \(\alpha=p/q\) with \(p\in\mathbb Z\), \(q\in\mathbb Z_{>0}\), then
\[
q(A(P_n)\alpha-C(P_n))=pA(P_n)-qC(P_n)
\]
is an integer. If the form is nonzero, its absolute value is at least \(1/q\), contradicting convergence to zero. Thus (2) implies (1).

Conversely, suppose \(\alpha\) is irrational. For each \(N\ge2\), place the \(N+1\) fractional parts of \(0,\alpha,\ldots,N\alpha\) in \(N\) equal subintervals of \([0,1)\). Two lie in the same subinterval. Their index difference gives integers \(1\le q_N\le N\) and \(p_N\) with
\[
0<|q_N\alpha-p_N|<1/N.
\]
Strict positivity follows from irrationality. Divide \((q_N,p_N)\) by \(g_N=\gcd(q_N,|p_N|)\). The resulting primitive pair \((A_N,C_N)\) satisfies
\[
0<|A_N\alpha-C_N|
=\frac{|q_N\alpha-p_N|}{g_N}<1/N.
\]
Set \(P_N=P_{N,A_N,C_N}\) using Lemma 2.1. Its degree is exactly \(N+1\), and its endpoint form is \(A_N\alpha-C_N\). This proves (2). \(\square\)

For \(\alpha=e+\pi\), this yields
\[
\boxed{
\exists(P_n)_{\deg P_n=n+1}:
0<|A(P_n)(e+\pi)-C(P_n)|\to0
\quad\Longleftrightarrow\quad e+\pi\notin\mathbb Q.
}
\tag{2.2}
\]
Therefore a proof of the requested family would itself prove the currently open irrationality of \(e+\pi\). The degree-lifting lemma encodes integer pairs in arbitrary high degrees; it does not create the approximating pairs.

## 3. Primitive denominator-survival criteria

If \(\varepsilon_n^{\rm an}\le e^{-\tau_n}\), then (1.1) gives
\[
|L_n|\le \exp\!\left(-\tau_n+\log(D_n/g_n)\right).
\tag{3.1}
\]
A sufficient condition for the irrationality certificate is
\[
\tau_n-\log(D_n/g_n)\longrightarrow+\infty,
\tag{3.2}
\]
together with eventual non-vanishing.

For the stronger Liouville route, if \(H_n\to\infty\), a sufficient condition is
\[
\frac{\tau_n-\log(D_n/g_n)}{\log H_n}\longrightarrow+\infty.
\tag{3.3}
\]
It implies
\[
\frac{-\log|L_n|}{\log H_n}\longrightarrow+\infty,
\]
which is the primitive super-polynomial criterion recorded in RESEARCH_CRITERIA.md and implies transcendence by Liouville's inequality.

The best standard is to record the exact primitive error itself and prove its limit. Conditions (3.2) and (3.3) are sufficient estimates, not substitutes for the exact ledger. Irrationality needs only (3.2); transcendence needs the much stronger height-relative decay (3.3).

## 4. Candidate audit: symmetric endpoint-vanishing polynomials

Consider
\[
P_n(X)=X^n(1-X)^n,\qquad n\ge1.
\]
Its degree is \(2n\), and its raw endpoint coefficients are
\[
a_n=A(P_n)=\sum_{k=0}^{n}(-1)^k\binom nk(n+k)!,
\quad
c_n=C(P_n)=(-1)^n\sum_{k=0}^{n}\binom nk(n+k)!.
\tag{4.1}
\]
The mixed integral identity gives
\[
a_n(e+\pi)-c_n=\pi a_n+I_n,\qquad
I_n=\int_0^1x^n(1-x)^ne^x\,dx,
\tag{4.2}
\]
and
\[
0<I_n\le e\frac{(n!)^2}{(2n+1)!}.
\tag{4.3}
\]

### Lemma 4.1 (exact content)

For every \(n\ge1\),
\[
\boxed{\gcd(|a_n|,|c_n|)=n!.}
\]

**Proof.** Put
\[
b_{n,k}=\frac{(n+k)!}{k!(n-k)!}\quad(0\le k\le n),
\]
and set \(b_{n,k}=0\) outside this range. Since \(\binom nk(n+k)!=n!b_{n,k}\), write
\[
a_n=n!v_n,\quad c_n=(-1)^n n!u_n,
\]
where
\[
u_n=\sum_{k=0}^{n}b_{n,k},\quad
v_n=\sum_{k=0}^{n}(-1)^k b_{n,k},\quad
w_n=(-1)^n v_n.
\]
Direct factorial simplification gives, for \(n\ge1\),
\[
b_{n+1,k}=2(2n+1)b_{n,k-1}+b_{n-1,k}.
\tag{4.4}
\]
For interior indices, putting both sides over \(k!(n-k+1)!\) reduces the identity to
\[
2k(2n+1)+(n-k)(n-k+1)=(n+k)(n+k+1).
\]
Boundary cases follow from the zero convention.

Summing (4.4), and then summing with alternating signs, gives
\[
u_{n+1}=2(2n+1)u_n+u_{n-1},\qquad
v_{n+1}=-2(2n+1)v_n+v_{n-1}.
\]
Consequently \(w_{n+1}=2(2n+1)w_n+w_{n-1}\). The initial values are
\[
u_0=1,\ u_1=3,\qquad w_0=1,\ w_1=1.
\]
Both sequences are odd, because the recurrence coefficient \(2(2n+1)\) is even and each new term is congruent modulo \(2\) to the term two places earlier.

Set \(\Delta_n=u_nw_{n-1}-u_{n-1}w_n\). The common recurrence gives
\[
\Delta_{n+1}=u_{n+1}w_n-u_nw_{n+1}=-\Delta_n.
\]
Since \(\Delta_1=2\), we have \(\Delta_n=(-1)^{n-1}2\). Any common divisor of \(u_n,w_n\) divides
\(\Delta_{n+1}=u_{n+1}w_n-u_nw_{n+1}\), hence divides \(2\). Both are odd, so \(\gcd(u_n,w_n)=1\). Therefore
\[
\gcd(|a_n|,|c_n|)=n!\gcd(w_n,u_n)=n!.
\]
\(\square\)

The primitive pair is thus exactly
\[
A_n=a_n/n!=(-1)^nw_n,\qquad C_n=c_n/n!=(-1)^nu_n.
\tag{4.5}
\]

### Proposition 4.2 (failure survives primitive reduction)

The primitive forms of this family diverge in absolute value:
\[
|A_n(e+\pi)-C_n|\longrightarrow\infty.
\]

**Proof.** Let \(t_k=\binom nk(n+k)!\). For \(1\le k\le n\),
\[
\frac{t_k}{t_{k-1}}=\frac{(n-k+1)(n+k)}{k}\ge2.
\]
Pairing the alternating sum from its final end gives
\[
|a_n|\ge t_n-t_{n-1}
=(2n)!-n(2n-1)!=(2n)!/2.
\]
Using (4.2)–(4.5) and \(|x+y|\ge|x|-|y|\),
\[
\begin{aligned}
|A_n(e+\pi)-C_n|
&=\frac{|a_n(e+\pi)-c_n|}{n!}\\
&=\left|\pi A_n+\frac{I_n}{n!}\right|\\
&\ge \pi|A_n|-\frac{I_n}{n!}\\
&\ge \frac{\pi(2n)!}{2n!}
-\frac{e\,n!}{(2n+1)!}
\longrightarrow\infty.
\end{aligned}
\]
Thus these primitive forms are nonzero for every \(n\), but cannot be an irrationality certificate. \(\square\)

### Exact finite records

The rows below follow from (4.1) and Lemma 4.1; the finite integer evaluations were cross-checked with Wolfram. The formula \(g_n=n!\) and the divergence are proved above, not extrapolated from the table.

| \(n\) | \(\deg P_n\) | raw \(a_n\) | raw \(c_n\) | \(g_n\) | primitive \(A_n\) | primitive \(C_n\) | \(H_n\) |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 2 | -1 | -3 | 1 | -1 | -3 | 3 |
| 2 | 4 | 14 | 38 | 2 | 7 | 19 | 19 |
| 3 | 6 | -426 | -1158 | 6 | -71 | -193 | 193 |
| 4 | 8 | 24024 | 65304 | 24 | 1001 | 2721 | 2721 |
| 5 | 10 | -2170680 | -5900520 | 120 | -18089 | -49171 | 49171 |
| 6 | 12 | 287250480 | 780827760 | 720 | 398959 | 1084483 | 1084483 |

For this family \(D_n=1\). Its analytic error, cleared error, and primitive error are
\[
\varepsilon_n^{\rm an}=|a_n\alpha-c_n|=|\pi a_n+I_n|,
\quad
\varepsilon_n^{\rm clear}=\varepsilon_n^{\rm an},
\quad
\varepsilon_n^{\rm prim}=\varepsilon_n^{\rm an}/n!.
\]
The primitive error diverges by Proposition 4.2. The small positive integral \(I_n\) is not the full linear-form error; it is overwhelmed by \(\pi a_n\).

## 5. Isolated degree-14 candidate in the literature

Runlong Yu's 2026 preprint reports one degree-14 example with
\[
a=245223,\qquad c=1436976,\qquad g=9.
\]
Its primitive pair is
\[
A=27247,\qquad C=159664,\qquad H=159664.
\]
The paper reports
\[
245223(e+\pi)-1436976\approx1.11462317066\times10^{-4},
\]
so the primitive numerical value is approximately
\[
|27247(e+\pi)-159664|\approx1.23847018962\times10^{-5}.
\]
Here \(D=1\), and primitive reduction divides the displayed raw value by \(9\). The paper classifies \(159664/27247\) as a continued-fraction convergent of \(e+\pi\). This is an isolated candidate, not a degree-continuing family. The decimal display is not a proof of non-vanishing or of any limit, so it is not an irrationality certificate.

Source: Runlong Yu, *Tail Criteria, No-Go Audits, and Apéry-Type Certificate Obstructions for the Irrationality of e+π*, arXiv:2606.17303v1 (2026), Sections 4–7: https://arxiv.org/abs/2606.17303

A later July 2026 University of Alabama preprint, *An Inverse Apéry Audit for e+π: Positivity–Smallness Separation*, reports a separate finite audit of 2,411 merged candidates. Its conclusions concern tested classes and are not a universal impossibility theorem: https://ir.ua.edu/items/3f1cbd3c-5578-4f1a-af83-8028f12c6122

## 6. Consequences for subsequent search

1. **Polynomial degree is not enough.** Lemma 2.1 embeds every integer pair in every sufficiently large degree. A useful family must carry additional arithmetic/analytic structure, not merely encode a preselected rational approximant.
2. **Raw error is not enough.** Equation (1.1) requires the primitive error to survive denominator clearing and gcd reduction.
3. **Smallness is not enough.** Eventual non-vanishing must be proved independently of the limiting estimate.
4. **A finite list is not a sequence theorem.** A degree-continuing law, recurrence, or uniform analytic estimate must justify the limit.
5. **A continued-fraction shadow is not automatically a new Apéry mechanism.** It may be a standard rational approximation repackaged in polynomial form.

The next search must find a mechanism coupling integrality, non-vanishing/sign, and a small primitive integral at the same scale. Repeating endpoint vanishing or enlarging an unconstrained lattice search does not address the obstruction proved above.

## 7. Lean and resource boundaries

Existing components on the G proof trunk:

- **lean/ApproximationCriteria.lean:** the generic Lean theorem that eventually nonzero integer linear forms tending to zero imply irrationality, plus the stronger super-polynomial-height criterion implying transcendence.
- **lean/MixedKernelQuotient.lean:** the mixed endpoint map, its affine section and quotient factorization, and the mixed integral identity.
- **lean/ProofAudit.lean:** theorem wrappers included in the project audit.

The degree-lifting lemma and exact gcd proof in this note are **not yet exported as Lean declarations**. They must be formalized and added to the independent theorem contract before being described as kernel-checked results. The existing project pins Lean 4 / Mathlib v4.36.0-rc2. PR #1's then-current commit 168eeaf4b10ce2991019a740ca704a3626de9922 had successful GitHub Actions run #335: https://github.com/2503140kcsk-eng/G/actions/runs/43543667625

The division of labour in TOOLS_AND_PROOF_PROTOCOL.md remains in force. Mathlib4 is the sole direct formal-mathematics dependency. Macaulay2 is for finite polynomial ideals/elimination; GAP for modular recurrence checks; SymPy for exact symbolic cross-checks; SageMath for interval and continued-fraction diagnostics; cvc5 for bounded side conditions; Naproche for written-proof audits; LeanDojo-v2 for premise/tactic discovery. These tools are not interchangeable with Lean's kernel. Wolfram was used here for finite symbolic/integer cross-checks; the other listed auxiliary packages were assigned their roles but were not executed in this session.

GitHub, Sider Scholar, Wolfram, Context7, and Parallel Search were used for repository inspection, literature discovery, symbolic corroboration, API documentation, and independent web cross-checking. Roles and limits of other available integrations are recorded in TOOLS_AND_PROOF_PROTOCOL.md; design, analytics, cloud, and project-management integrations do not contribute to this number-theory proof. Account-level plugin quotas and billing are not visible here, so no blanket guarantee that every connected action is free is made. No paid CAS or hosted theorem-prover is part of the formal proof dependency.

## 8. Final mathematical status

The requested unconditional polynomial sequence would imply that \(e+\pi\) is irrational by Corollary 2.2. The literature checked through 2026-11-14 still reports that irrationality as open. This work establishes a sharper standard and exact structural results, but does **not** claim to have constructed the requested unconditional sequence.

The completion condition remains unmet until a non-circular family \(P_n\) is found for which the primitive forms are proved nonzero and their absolute values are proved to converge to zero.
