# Concrete resultant–Liouville bound and Split–Machin function audit

**Snapshot:** 2026-11-21 (JST)  
**Parent:** \`research/resultant-paired-transcendence-criterion-2026-11-17\` at \`f48c0dae140b256fcab59be48d5b0387e819cfdc\`  
**Status:** The height/degree implication that supplies the abstract \`hLiouville\` premise is proved below as an ordinary mathematical theorem. This note does **not** prove the approximation upper bound needed for the \`e + pi\` target, and it does not claim irrationality or transcendence of \`e + pi\`.

## 1. Explicit sequence hypotheses

For a nonzero integer polynomial
\[
R(X)=\sum_{j=0}^N r_jX^j\in\mathbb Z[X],
\]
write
\[
\deg R=N,\qquad H(R)=\max_{0\le j\le N}|r_j|.
\]

Let \(P_n,Q_n\in\mathbb Q[X]\), and let \(H_n\in\mathbb N\). Suppose there are positive integers \(m_n^P,m_n^Q\) such that
\[
R_n=m_n^PP_n\in\mathbb Z[X],\qquad T_n=m_n^QQ_n\in\mathbb Z[X].
\]
Assume that fixed natural numbers \(A,B,c\) satisfy, for all sufficiently large \(n\),
\[
H_n\ge2,
\]
\[
H(R_n),H(T_n)\le H_n^A,
\qquad
m_n^P,m_n^Q\le H_n^B,
\tag{1}
\]
and
\[
2^{\deg R_n}\le H_n^c,\qquad
2^{\deg T_n}\le H_n^c.
\tag{2}
\]
Condition (2) is an integer-only form of the logarithmic degree bound
\[
\deg P_n,\deg Q_n\le c\log_2 H_n.
\]

Finally, assume the two sequences are separately pairwise Bézout-coprime:
\[
i\ne j\Longrightarrow
\gcd_{\mathbb Q[X]}(P_i,P_j)=1,
\qquad
i\ne j\Longrightarrow
\gcd_{\mathbb Q[X]}(Q_i,Q_j)=1.
\tag{3}
\]
The two coprimality conditions are separate sequence conditions. Coprimality only between \(P_n\) and \(Q_n\) at the same index is not a substitute.

## 2. The concrete \`hLiouville\` theorem

**Theorem.** Under (1)–(3), for every real algebraic number \(\xi\), there is a natural number \(d=d(\xi)\) such that, for all sufficiently large \(n\),
\[
P_n(\xi)\ne0\Longrightarrow |P_n(\xi)|\ge H_n^{-d},
\]
and
\[
Q_n(\xi)\ne0\Longrightarrow |Q_n(\xi)|\ge H_n^{-d}.
\]
One may take
\[
\boxed{d=cK_a+(D-1)(A+c+cK_C)+B,}
\tag{4}
\]
where \(D\) is the degree of the minimal polynomial of \(\xi\), and \(K_a,K_C\) are any natural numbers satisfying the bounds below.

### Proof

Let
\[
f(X)=a\prod_{j=1}^{D}(X-\xi_j)\in\mathbb Z[X]
\]
be the primitive irreducible polynomial of \(\xi\), with \(\xi_1=\xi\). Since the characteristic is zero, the conjugates are distinct. Choose \(C\ge1\) so that \(|\xi_j|\le C\) for all \(j\), and choose \(K_a,K_C\in\mathbb N\) with
\[
|a|\le2^{K_a},\qquad C\le2^{K_C}.
\tag{5}
\]
These constants depend on \(\xi\), not on \(n\).

First, (3) implies that \(\xi\) can be a zero of at most one member of either sequence. Indeed, if \(P_i(\xi)=P_j(\xi)=0\) for distinct \(i,j\), a Bézout identity \(UP_i+VP_j=1\) evaluated at \(\xi\) gives \(0=1\). The same argument applies to \(Q\). Thus both evaluations are eventually nonzero.

Fix a sufficiently large index \(n\) for which \(P_n(\xi)\ne0\), and put \(R=R_n=m_n^PP_n\), \(N=\deg R\). Since \(f\) is irreducible and \(R(\xi)\ne0\), the polynomials \(f\) and \(R\) are coprime in \(\mathbb Q[X]\). Hence their resultant is a nonzero integer:
\[
1\le|\operatorname{Res}(f,R)|.
\]
The product formula for the resultant gives
\[
|\operatorname{Res}(f,R)|
=|a|^N\prod_{j=1}^{D}|R(\xi_j)|.
\tag{6}
\]

For every conjugate \(\xi_j\), \(j\ge2\), the coefficient-height bound in (1) yields
\[
\begin{aligned}
|R(\xi_j)|
&\le \sum_{k=0}^{N}|r_k|\,|\xi_j|^k\\
&\le (N+1)H_n^A C^N.
\end{aligned}
\tag{7}
\]
For every natural number \(N\), \(N+1\le2^N\). Combining this with (2) and (5),
\[
N+1\le H_n^c,\qquad
C^N\le 2^{K_CN}\le H_n^{cK_C},\qquad
|a|^N\le H_n^{cK_a}.
\tag{8}
\]
Substitute (7)–(8) into (6), isolating the distinguished root \(\xi_1=\xi\):
\[
1
\le |a|^N |R(\xi)|
      \prod_{j=2}^{D}|R(\xi_j)|
\le
|R(\xi)|\,
H_n^{cK_a+(D-1)(A+c+cK_C)}.
\]
Therefore
\[
|R_n(\xi)|
\ge H_n^{-d_0},
\quad
d_0=cK_a+(D-1)(A+c+cK_C).
\tag{9}
\]
Since \(R_n=m_n^PP_n\) and \(m_n^P\le H_n^B\),
\[
|P_n(\xi)|
=\frac{|R_n(\xi)|}{m_n^P}
\ge H_n^{-(d_0+B)}.
\]
This proves the \(P\)-bound with (4). Repeating the identical argument for \(T_n=m_n^QQ_n\) proves the \(Q\)-bound with the same exponent. \(\square\)

## 3. Consequence for the paired approximation criterion

Suppose, in addition to (1)–(3), that
\[
\forall k\in\mathbb N,\quad
\text{eventually }\quad
\min\{|P_n(x)|,|Q_n(x)|\}<H_n^{-k}.
\tag{10}
\]
If \(x\) were algebraic, the theorem would give one fixed \(d=d(x)\) such that both evaluations are eventually at least \(H_n^{-d}\). Taking \(k=d+1\) in (10) contradicts \(H_n\ge2\). Hence \(x\) is transcendental.

This proves the arithmetic lower-bound implication required by the current paired criterion. In particular, (1)–(3) give a concrete sufficient condition for the existing abstract \`hLiouville\` premise.

**What remains:** the actual Split–Machin approximation construction must still provide (10), with the same coefficient source, denominators, and primitive normalization as in (1)–(3). The theorem above does not construct such a sequence.

## 4. Split–Machin system: exact analytic data

Set
\[
G(z)=16\arctan(z/5)-4\arctan(z/239),\qquad
S(z)=e^z+G(z).
\]
Machin's identity gives \(G(1)=\pi\), so \(S(1)=e+\pi\).

The Taylor coefficients at the origin are rational and exact:
\[
e^z=\sum_{k\ge0}\frac{z^k}{k!},\qquad a_k=\frac1{k!},
\]
and
\[
G(z)=\sum_{k\ge0}g_kz^k,\qquad
g_k=
\begin{cases}
0,&k\text{ even},\\[1mm]
(-1)^{(k-1)/2}\dfrac{16/5^k-4/239^k}{k},&k\text{ odd}.
\end{cases}
\tag{11}
\]

Differentiation gives
\[
\rho(z):=G'(z)
=\frac{80}{z^2+25}-\frac{956}{z^2+57121}
=\frac{12(378815-73z^2)}
{(z^2+25)(z^2+57121)}.
\tag{12}
\]

Let
\[
U_0=12(378815-73z^2),\quad
V_0=(z^2+25)(z^2+57121),\quad
W_0=U_0'V_0-U_0V_0'.
\]
Then \(G\) satisfies the homogeneous second-order differential equation
\[
\boxed{U_0V_0G''-W_0G'=0.}
\tag{13}
\]
This follows directly from \(\rho G''-\rho'G'=0\) after multiplying by \(V_0^2\).

For \(S=e^z+G\), define \(T=\rho'-\rho=U/V\), where
\[
\begin{aligned}
U=12(&-540957290375-43504015630z-21543516165z^2\\
&-1515260z^3+3792843z^4+146z^5+73z^6),\\
V={}&(z^2+25)^2(z^2+57121)^2,\qquad
W=U'V-UV'.
\end{aligned}
\tag{14}
\]
Since
\[
S''-S'=T,\qquad S'''-S''=T',
\]
we obtain
\[
\boxed{UVS'''-(UV+W)S''+WS'=0.}
\tag{15}
\]
Thus \(S\) is D-finite: it satisfies a nonzero linear differential equation with polynomial coefficients. The symbolic identity in (15) was independently checked in Wolfram Language; the residual simplifies to zero. No minimal-order claim is made here.

The closest singularities of \(G\) to the origin are the logarithmic branch points \(z=\pm5i\), so its Taylor radius is exactly \(5\). The odd coefficients in (11) have dominant magnitude \(16/(k5^k)\), while the \(239^{-k}\) term is exponentially smaller. Adding the entire function \(e^z\) cannot remove the logarithmic branch points, so \(S\) has the same finite-radius obstruction to being entire.

## 5. Function-class boundary

- \(e^z\) is an E-function: it is entire, has expansion \(\sum z^k/k!\), and satisfies \(y'-y=0\).
- \(G(z)\) is a G-function: its coefficients are rational, are exponentially bounded, have common denominators bounded exponentially (for example, \(5^N239^N\operatorname{lcm}(1,\ldots,N)\), together with the standard exponential bound on the least common multiple), and it satisfies (13).
- \(G\) is not an E-function because it is not entire.
- \(S=e^z+G(z)\) is D-finite by (15), but it is not an E-function because it is not entire. It is a mixed E/G-type sum, not an E-function to which the usual E-function specialization theorem can simply be applied.

Beukers' refined Siegel–Shidlovskii theorem concerns values of E-functions at nonzero algebraic points. Its hypotheses require entire E-functions in a differential system. Since \(G\) and \(S\) fail the entire-function condition, the theorem does not directly classify \(G(1)=\pi\) together with \(e^1\), and it does not imply that \(e+\pi\) is transcendental.

## 6. What the current endpoint experiments actually show

The existing Split–Machin branch records the type-II construction
\[
Q(z)e^z-P(z)=O(z^{N+1}),\qquad
Q(z)G(z)-R(z)=O(z^{N+1}),
\]
with \(\deg Q\le N=m+\ell\), \(\deg P\le\ell\), \(\deg R\le m\). For \(m=\ell=n\), the exact rational Taylor system has rank \(2n\), nullity one, for the finite range \(1\le n\le8\).

After clearing one common denominator across \(Q,P,R\) and removing their joint integer content, the endpoint form is
\[
L_n=\widehat Q_n(1)(e+\pi)-\widehat P_n(1)-\widehat R_n(1).
\]
The stored finite diagnostic gives:

| \(n\) | \(\log_{10}|L_n|\) |
|---:|---:|
| 1 | 3.7312 |
| 2 | 17.9835 |
| 3 | 36.4265 |
| 4 | 60.7552 |
| 5 | 91.3153 |
| 6 | 127.6334 |
| 7 | 172.6832 |
| 8 | 222.0888 |

These are values of the **normalized** integer linear form, not the unscaled analytic residual. This particular small diagonal family is therefore not a candidate for (10). The finite table does not prove an asymptotic obstruction for all multi-indices or all constructions.

The existing scalar truncation
\[
r_D=\sum_{k=0}^{D}\frac1{k!}
+16\sum_{k=0}^{2D+1}\frac{(-1)^k}{(2k+1)5^{2k+1}}
-4\sum_{k=0}^{2D}\frac{(-1)^k}{(2k+1)239^{2k+1}}
\]
has analytic error
\[
e+\pi-r_D=
\frac{200}{13(4D+5)5^{4D+5}}\bigl(1+O(D^{-1})\bigr).
\]
That is an unscaled real-analytic estimate. It is insufficient until it survives common-denominator clearing and primitive-content reduction. The existing endpoint note reports a 5-adic obstruction for that scalar truncation, but explicitly does not exclude coupled determinant or other split-channel constructions.

The current endpoint-lattice work also reports the fixed-instance invariant
\[
\theta_1=17\cdot239^{44}>1.
\]
This is a genuine \(r=1\) lattice obstruction, not an all-\(r\) theorem and not a transcendence result.

## 7. Acceptance gate

A Split–Machin sequence is not a transcendence certificate until the **same** polynomial source proves all of the following:

1. Exact rational Taylor construction and exact integerization.
2. Separate pairwise coprimality of the two polynomial sequences.
3. Uniform coefficient-height and denominator bounds as in (1).
4. Logarithmic degree bounds as in (2).
5. The super-polynomial endpoint estimate (10), after all denominator and primitive-content operations.
6. The argument applies to every sufficiently large index, not merely a finite data table.
7. Lean kernel checking and the project's proof-hole, axiom, and comparator audits pass on the exact commit.

The first four items would supply the concrete \`hLiouville\` theorem proved in this note. Item 5 is the unresolved arithmetic/analytic construction.

## References

- Beukers, *A refined version of the Siegel–Shidlovskii theorem*, Annals of Mathematics 163 (2006), 369–379: https://annals.math.princeton.edu/2006/163-1/p08
- Yu, *Computer-Assisted Diagonal Hermite–Padé Normality via 239-Adic Discrete Convexity*, University of Alabama (2026): https://ir.ua.edu/items/af229802-04e3-4c4c-be60-83f707613570
- Yu, *Primitive Laurent Completion and Endpoint Arithmetic in a Split–Machin Hermite–Padé System*, University of Alabama (2026): https://ir.ua.edu/items/8dc89475-beb6-47d8-8ee3-d8a92ec1e496
- Yu, *Tail Criteria, No-Go Audits, and Apéry-Type Certificate Obstructions for the Irrationality of e+π*, arXiv:2606.17303 (preprint): https://arxiv.org/abs/2606.17303
