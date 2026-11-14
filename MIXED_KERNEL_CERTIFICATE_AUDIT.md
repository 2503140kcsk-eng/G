# Mixed-kernel certificates: exact nonvanishing and the remaining smallness gap

**Snapshot:** 2026-11-14  
**Status:** rigorous partial results; this is not a proof that \(e+\pi\) is irrational.

## 1. Setup

For \(P\in\mathbb Z[x]\), define
\[
S_P(x)=\sum_{j=0}^{\deg P}(-1)^jP^{(j)}(x),
\qquad A(P)=S_P(1).
\]
All values \(A(P)\) and \(S_P(0)\) are integers. Since
\[
\frac{d}{dx}\left(e^xS_P(x)\right)=e^xP(x),
\]
integration by parts gives
\[
\int_0^1P(x)e^x\,dx=A(P)e-S_P(0).
\]
Using \(\pi=4\int_0^1(1+x^2)^{-1}\,dx\), define
\[
K_P(x)=P(x)e^x+\frac{4A(P)}{1+x^2}.
\]
Then the exact mixed-kernel identity is
\[
\boxed{\int_0^1K_P(x)\,dx=A(P)(e+\pi)-S_P(0).}\tag{1}
\]
This identity is a known construction; see Runlong Yu, arXiv:2606.17303 (2026), §4. The new point of this note is the sign-normalized nonvanishing test below and the paired primitive-square criterion.

## 2. A family with unconditional nonvanishing for every index

Let
\[
P_n(x)=x^n(1-x)^n,\qquad
I_n=\int_0^1P_n(x)e^x\,dx,
\]
and put \(a_n=A(P_n)\), \(s_n=S_{P_n}(0)\).

For \(0\le x\le1\), \(0\le x(1-x)\le1/4\). Hence, for every \(n\ge1\),
\[
0<I_n\le4^{-n}\int_0^1e^x\,dx
=(e-1)4^{-n}<1.
\]
Equation (1) without the arctangent term gives
\[
I_n=a_ne-s_n.
\]
If \(a_n=0\), then \(I_n=-s_n\in\mathbb Z\), contradicting \(0<I_n<1\). Thus \(a_n\ne0\) for every \(n\ge1\).

Let \(\varepsilon_n=\operatorname{sgn}(a_n)\in\{-1,1\}\), and set
\[
\widetilde P_n=\varepsilon_nP_n,\quad
g_n=\gcd(|a_n|,|s_n|),\quad
A_n=\frac{|a_n|}{g_n},\quad
C_n=\frac{\varepsilon_ns_n}{g_n}.
\]
Then \(A_n,C_n\in\mathbb Z\), \(A_n>0\), and
\(\gcd(A_n,|C_n|)=1\). Applying (1) to \(\widetilde P_n\) yields
\[
\boxed{
A_n(e+\pi)-C_n
=\frac{|a_n|\pi+\varepsilon_nI_n}{g_n}
=\pi A_n+\frac{\varepsilon_nI_n}{g_n}.
}\tag{2}
\]
Since \(A_n\ge1\), \(g_n\ge1\), and \(0<I_n<1\),
\[
A_n(e+\pi)-C_n
\ge\pi A_n-\frac{I_n}{g_n}
>\pi-1>0.
\]
Therefore
\[
\boxed{A_n(e+\pi)-C_n\ne0\quad\text{for every }n\ge1,}
\]
without assuming \(e+\pi\notin\mathbb Q\).

This family does **not** solve the irrationality problem: (2) also proves
\[
|A_n(e+\pi)-C_n|>\pi-1>2,
\]
so the forms cannot tend to zero. It isolates nonvanishing from smallness, but fails the latter decisively.

The endpoint sums can be written exactly as
\[
a_n=\sum_{j=0}^{n}(-1)^j\binom nj(n+j)!,
\qquad
s_n=(-1)^n\sum_{j=0}^{n}\binom nj(n+j)!.
\]
These formulas are useful for exact gcd and recurrence experiments.

## 3. A paired primitive-square certificate

For any integer pairs \((A_n,C_n)\), write
\[
L_n(X)=A_nX-C_n,\qquad
\Delta_n=A_nC_{n+1}-A_{n+1}C_n.
\]
Define the quadratic form
\[
\mathcal Q_n(X)=L_n(X)^2+L_{n+1}(X)^2.
\]
If \(\Delta_n\ne0\), then for every real \(X\),
\[
\boxed{
\mathcal Q_n(X)\ge
\frac{\Delta_n^2}{A_n^2+A_{n+1}^2}>0.
}\tag{3}
\]
Indeed, minimizing the quadratic polynomial in \(X\), or completing the square, gives the displayed lower bound. Thus the pair cannot vanish simultaneously; this conclusion is independent of the arithmetic nature of \(X\).

Moreover, suppose \(X=p/q\in\mathbb Q\) in lowest terms, with \(q>0\). Then
\[
L_n(X)=\frac{A_np-C_nq}{q},
\]
whose numerator is an integer. Since \(\Delta_n\ne0\), the two numerators cannot both vanish, so
\[
\mathcal Q_n(p/q)\ge q^{-2}.
\]
Consequently, if a sequence satisfies
\[
\Delta_n\ne0\quad\text{for all }n,
\qquad L_n(e+\pi)\longrightarrow0,
\]
then \(\mathcal Q_n(e+\pi)\to0\), contradicting the rational lower bound. This proves \(e+\pi\notin\mathbb Q\).

The paired formulation avoids having to prove that each individual \(L_n(e+\pi)\) is nonzero: it suffices to prove a nonzero determinant for every adjacent pair. It is a quadratic certificate, not a single linear form.

For the mixed-kernel family, (1) gives
\[
\mathcal Q_n(e+\pi)=
\left(\frac{1}{g_n}\int_0^1K_{\widetilde P_n}(x)\,dx\right)^2+
\left(\frac{1}{g_{n+1}}\int_0^1K_{\widetilde P_{n+1}}(x)\,dx\right)^2.
\]
Thus a future construction only needs to supply both a determinant condition and sufficiently small normalized kernel integrals.

## 4. Exact remaining target

A sufficient analytic-arithmetic target is to construct \(P_n\in\mathbb Z[x]\) such that, after primitive reduction,
\[
\Delta_n\ne0,\qquad
\frac1{g_n}\int_0^1|K_{\widetilde P_n}(x)|\,dx\longrightarrow0.
\]
The triangle inequality then gives \(L_n(e+\pi)\to0\), and §3 proves irrationality. A stronger route is to arrange a fixed sign for each normalized kernel and show its integral tends to zero; that would give individual nonvanishing as well.

The known mixed identity (1) does not itself establish this estimate. In particular, the family in §2 shows that a small \(e\)-remainder \(I_n\) can coexist with a large \(\pi\)-term. Denominator clearing, primitive reduction, and coefficient growth must all be controlled in the same construction.

## 5. Formalization boundary

The following are suitable unconditional Lean targets:

1. The finite integration-by-parts identity for integer polynomials.
2. Integrality of \(A(P)\) and \(S_P(0)\).
3. The \(P_n=x^n(1-x)^n\) bound \(0<I_n<1\).
4. Nonvanishing of \(a_n\) and the lower bound in (2).
5. The determinant inequality (3) over \(\mathbb R\).
6. The rational lower bound \(q^{-2}\) and the paired irrationality criterion.

None of these should be confused with the missing existence theorem for a small mixed-kernel family. No axiom, sorry, admit, numerical fit, or conjectural transcendence statement is used here.

## References

- Runlong Yu, “Tail Criteria, No-Go Audits, and Apéry-Type Certificate Obstructions for the Irrationality of \(e+\pi\),” arXiv:2606.17303 (2026), especially §§2, 4–5: https://arxiv.org/abs/2606.17303
- Helen Joyce, “Mathematical mysteries: Transcendental meditation,” Plus (2002), for the classical sum/product disjunction: https://plus.maths.org/content/mathematical-mysteries-transcendental-meditation
