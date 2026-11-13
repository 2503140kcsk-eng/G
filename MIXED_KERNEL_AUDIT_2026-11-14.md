# Mixed-kernel audit and exact failure certificate (2026-11-14)

**Branch:** `formalize-algebraic-number-closure`  
**Parent work:** PR #1, *Formalize e and π transcendence with audited e+π consequences*  
**Status:** New exact obstructions proved; no approximating sequence for (e+\pi) has been constructed.

This note records a continuation of the mixed-integral direction. It distinguishes identities that are exact from the still-missing asymptotic construction.

## 1. The certificate criterion is already formalized

Put (\alpha=e+\pi). If integers (A_n,C_n) satisfy

\[
A_n\alpha-C_n\ne0\quad\text{eventually},\qquad
|A_n\alpha-C_n|\longrightarrow0,
\]

then (\alpha\) is irrational. If (\alpha=p/q\) with (q>0), then

\[
q(A_n\alpha-C_n)=pA_n-qC_n
\]

is a nonzero integer, so every sufficiently late term has absolute value at least (1/q), a contradiction.

The theorem
`EPlusPiApproximation.irrational_of_tendsto_zero_signed_integer_linear_forms`
in `lean/ApproximationCriteria.lean` proves the general statement in Lean. The stronger Liouville / super-polynomial-height criterion is also present and included in `ProofAudit`. These results certify a sequence once one exists; they do not construct one for (e+\pi).

## 2. The mixed polynomial integral identity

For (P\in\mathbb Z[x]), let

\[
S_P(x)=\sum_{j=0}^{\deg P}(-1)^jP^{(j)}(x),\qquad
A(P)=S_P(1),\qquad C(P)=S_P(0).
\]

The finite sum telescopes:

\[
S_P'(x)+S_P(x)=P(x).
\]

It follows that

\[
\frac{d}{dx}\bigl(e^xS_P(x)\bigr)=e^xP(x),
\qquad
\int_0^1P(x)e^x\,dx=eA(P)-C(P).
\]

Since (4\int_0^1(1+x^2)^{-1}dx=\pi),

\[
\boxed{
\int_0^1\left(P(x)e^x+\frac{4A(P)}{1+x^2}\right)dx
=A(P)(e+\pi)-C(P).
}
\tag{2.1}
\]

For integer-coefficient (P), the endpoint derivative sums (A(P),C(P)) are integers. This is the mixed identity appearing in Runlong Yu, *Tail Criteria, No-Go Audits, and Apéry-Type Certificate Obstructions for the Irrationality of e+π*, arXiv:2606.17303v1 (2026); it is not claimed as a new identity.

### 2.1 A surjectivity warning

The map (P\mapsto(A(P),C(P))) is already surjective onto (\mathbb Z^2) on degree-at-most-one polynomials.

Indeed, for any integers (a,c), take

\[
P_{a,c}(x)=(a-c)x+a.
\]

Then (S_{P_{a,c}}(x)=P_{a,c}(x)-P'_{a,c}(x)=(a-c)x+c), whence

\[
(A(P_{a,c}),C(P_{a,c}))=(a,c).
\]

Therefore (2.1), by itself, imposes **no arithmetic restriction** on the integer pair in the linear form: every integer pair already occurs. A useful construction must impose additional structure on a degree-growing family (P_n), and that structure must force the integral in (2.1) to be small after primitive reduction. Merely rewriting a good rational approximation as a polynomial integral is not a new certificate.

## 3. Exact audit of the symmetric endpoint-vanishing family

A natural first test is

\[
P_n(x)=x^n(1-x)^n,\qquad n\ge1.
\]

It vanishes to order (n) at both endpoints, but this alone does not control the (\pi A(P_n)) term.

Expanding,

\[
P_n(x)=\sum_{k=0}^n(-1)^k\binom nkx^{n+k}.
\]

At (x=0), only the derivative of order (n+k) survives, so

\[
C_n:=C(P_n)=(-1)^n\sum_{k=0}^n\binom nk(n+k)!.
\tag{3.1}
\]

Also (P_n(1-x)=P_n(x)), hence (P_n^{(j)}(1)=(-1)^jP_n^{(j)}(0)). Therefore

\[
A_n:=A(P_n)=\sum_{k=0}^n(-1)^k\binom nk(n+k)!.
\tag{3.2}
\]

Let

\[
t_k=\binom nk(n+k)!.
\]

For (1\le k\le n),

\[
\frac{t_k}{t_{k-1}}
=\frac{(n-k+1)(n+k)}{k}\ge2,
\]

because

\[
(n-k+1)(n+k)-2k=(n-k)(n+k+1)\ge0.
\]

Thus the (t_k) increase at least geometrically by a factor of two. Pairing consecutive terms from the final end shows that the alternating sum (3.2) has sign ((-1)^n) and

\[
|A_n|\ge t_n-t_{n-1}
=(2n)!-n(2n-1)!
=\frac{(2n)!}{2}.
\tag{3.3}
\]

Now define the positive integral

\[
I_n=\int_0^1x^n(1-x)^ne^x\,dx.
\]

The exponential part of (2.1) gives (A_ne-C_n=I_n), so the target linear form is exactly

\[
L_n=A_n(e+\pi)-C_n=\pi A_n+I_n.
\tag{3.4}
\]

Since (e^x\le e) on ([0,1]),

\[
0<I_n\le e\int_0^1x^n(1-x)^n dx
=e\frac{(n!)^2}{(2n+1)!}.
\tag{3.5}
\]

Combining (3.3)–(3.5),

\[
|L_n|
\ge \pi|A_n|-I_n
\ge \frac{\pi}{2}(2n)!
-e\frac{(n!)^2}{(2n+1)!}
\longrightarrow\infty.
\]

**Conclusion:** this family fails decisively. Its linear forms do not tend to zero; their absolute values diverge factorially. The reason is structural: endpoint vanishing makes (I_n\) small, but leaves (\pi A_n\) with a factorially large coefficient.

Wolfram was used to check the first exact integer pairs and numerical values against (3.1)–(3.4). Those finite checks are corroboration only; the proof of divergence is the analytic and combinatorial estimate above.

## 4. Factorial-tail divisibility does not provide a shortcut

Yu's preprint gives an equivalent formulation of the rationality hypothesis. Let

\[
E_N=\sum_{k=0}^N\frac1{k!},\quad
B_N=N!E_N=\lfloor N!e\rfloor,\quad
\rho_N=N!(e-E_N),
\]

and

\[
A_N=\lceil N!\pi\rceil,\quad
\delta_N=A_N-N!\pi,\quad Q_N=A_N+B_N.
\]

For (N\ge1), (0<\rho_N,\delta_N<1), and the exponential tail satisfies

\[
\rho_{N+1}=(N+1)\rho_N-1.
\]

The ceiling recurrence is

\[
A_{N+1}=(N+1)A_N-\lfloor(N+1)\delta_N\rfloor.
\]

Also (B_{N+1}=(N+1)B_N+1). Consequently,

\[
Q_{N+1}=(N+1)Q_N+1-\lfloor(N+1)\delta_N\rfloor.
\tag{4.1}
\]

If ((N+1)\mid Q_{N+1}) for every sufficiently large (N), then (4.1) and (0\le\lfloor(N+1)\delta_N\rfloor\le N) force

\[
\lfloor(N+1)\delta_N\rfloor=1.
\]

Hence (\delta_{N+1}=(N+1)\delta_N-1), the same recurrence as (\rho_N). Their difference (\varepsilon_N=\rho_N-\delta_N) obeys

\[
\varepsilon_{N+m}
=\bigl((N+1)(N+2)\cdots(N+m)\bigr)\varepsilon_N.
\]

Because both remainders stay in ((0,1)), the left side has absolute value less than one. Letting (m\to\infty) gives (\varepsilon_N=0). Thus

\[
N!(e+\pi)=A_N+B_N=Q_N
\]

for all sufficiently large (N), so (e+\pi\in\mathbb Q). The converse follows by taking (N) large enough that the denominator of a hypothetical rational (e+\pi) divides ((N-1)!).

This is an exact characterization of what rationality would force, not a proof that the divisibility fails. In particular, the ordinary continued-fraction recurrence for (\pi) alone cannot be used to contradict the eventual divisibility: doing so without an additional independent estimate would smuggle in the desired information about (e+\pi).

## 5. Resource allocation for this continuation

| Resource | Assigned task | What was actually done / evidence boundary |
|---|---|---|
| GitHub | Inspect PR #1, edit this research branch, preserve the exact Lean lockfile, and rerun CI. | Repository, files, branch, and workflow state inspected; this note is committed on the PR branch. |
| Sider Scholar | Find primary research and check the bibliographic record of the mixed-integral preprint. | arXiv:2606.17303 metadata and related irrationality literature searched; search results are leads, not proofs. |
| Wolfram | Exact finite sums, derivative endpoints, and numerical consistency checks for (P_n). | Used for sample values; the infinite estimate is proved above, not inferred from a table. |
| Context7 | Check version-sensitive Lean/Mathlib interfaces for the existing approximation criteria. | Documentation queried; it does not replace the pinned build. |
| Parallel | Independent literature/logic cross-check, especially the factorial-tail route and the scope of the finite no-go audit. | Prior research response reused; no new research-mode request in this continuation. Research-mode account billing/quota is not visible here. |
| Macaulay2 | Future exact polynomial-ideal, elimination, or differential-module experiments for structured multi-period kernels. | Repository README inspected; binary not executed in this session. |
| GAP | Future modular and finite arithmetic checks for recurrences and divisibility patterns. | Repository README inspected; GAP not executed in this session. |
| SymPy | Future exact derivative-sum, series, and symbolic identity cross-checks. | Repository README inspected; SymPy not executed in this session. |
| SageMath | Future continued-fraction, interval, and rational-approximation diagnostics. | Repository README inspected; SageMath not executed in this session. |
| Naproche | Independent natural-language proof audit: quantifiers, endpoint cases, and induction steps. | Repository README inspected; Isabelle/Naproche not executed in this session. |
| cvc5 | Bounded side-condition checks and finite counterexample searches for candidate recurrences. | Repository README inspected; cvc5 not executed in this session. |
| LeanDojo-v2 | Retrieve Mathlib proof patterns and suggest tactic candidates for the exact formalization of (2.1). | Repository README inspected; the full agent/training stack was not run. |
| mathlib4 | Trusted Lean mathematics library and kernel-checked proof dependencies. | Existing PR pins Mathlib v4.36.0-rc2; current criteria already compile in the CI record. |

The public repository documentation was inspected for the eight repositories listed by the user. The software packages Macaulay2, GAP, SymPy, SageMath, Naproche, cvc5, and LeanDojo-v2 were not executed here; no output from them is represented as a computation. The proof trust base remains Lean plus the pinned Mathlib dependency.

## 6. What remains

The next mathematical target is **not** another arbitrary polynomial search. It is a family with a structural coupling that cancels the two periods before the final integral is estimated. A higher-dimensional mixed-period construction is a candidate direction, but it must still prove all of the following:

1. An exact evaluation of the form (I_n=A_n(e+\pi)-C_n), with no uncontrolled extra periods.
2. (A_n,C_n\in\mathbb Z), or an explicit denominator (D_n) whose growth is included in the error budget.
3. Eventual nonvanishing, preferably by a sign or positivity argument.
4. (0<|I_n|\to0) **after** denominator clearing and gcd reduction.
5. Non-circularity: no use of the continued fractions or irrationality of (e+\pi) being proved.

Until such a family is established, the correct project status remains: the generic irrationality criterion is formally proved, but its required (e+\pi) instance is not.
