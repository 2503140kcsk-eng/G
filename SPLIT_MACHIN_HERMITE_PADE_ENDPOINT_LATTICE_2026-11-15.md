# Split–Machin Hermite–Padé: primitive endpoint-lattice continuation

**Snapshot:** 2026-11-15 $JST$  
**Branch:** `research/split-machin-endpoint-lattice-2026-11-15`  
**Base:** PR #4 head `4d106ff9a81c2e6a28384a80c4a2feede0ee7b0c`  
**Status:** research continuation and exact finite diagnostic; **no irrationality proof is claimed**.

## 1. Executive result

The correct next target is not another unconstrained Padé search. It is the arithmetic compatibility problem for the Split–Machin source:

\[
G(z)=16\arctan(z/5)-4\arctan(z/239),\\\qquad G(1)=\pi,
\]
\[
(1,e^z,G(z)),\\\qquad S(1)=e+\pi,\\quad S(z)=e^z+G(z).
\]

The 2026 literature has already established substantial parts of the analytic and lattice architecture. In particular, diagonal type-I normality and a primitive Laurent completion theorem are available as research results, but neither supplies the final height/denominator estimate needed for an irrationality certificate. The remaining task is to couple, on one and the same primitive source, (i) nonzero endpoint arithmetic, (ii) the endpoint-lattice index, and (iii) an archimedean error that tends to zero **after** all common-denominator and primitive-content operations.

This document records that boundary, a corrected finite Type-II experiment, and a proof-oriented continuation plan. It deliberately does not repackage a finite computation or a published preprint as a proof of $e+\pi\notin\mathbb Q$.

## 2. Exact criterion already available in G

PR #4 contains the reusable common-denominator identity. For rational approximants $p/q\$ to (x) and $s/r\$ to $y$,

\[
$qr$$x+y$-$rp+qs$=r(qx-p)+q(ry-s),
\]
hence
\[
|$qr$$x+y$-$rp+qs$|\le r|qx-p|+q|ry-s|.
\]

The right-hand side is the cross-weighted error budget. Separate limits $qx-p\to0$ and $ry-s\to0$ do not imply that this budget tends to zero.

G also contains a paired determinant criterion. If integer sequences $A_n,C_n$ satisfy, eventually,
\[
A_nC_{n+1}-A_{n+1}C_n\ne0,
\]
and
\[
|A_nx-C_n|+|A_{n+1}x-C_{n+1}|\longrightarrow0,
\]
then (x) is irrational. The determinant guarantees that adjacent forms cannot both vanish at a rational (x).

These are conditional bridge theorems. The missing input is a construction in the Split–Machin system that supplies the arithmetic hypotheses and the post-normalization decay.

### Primitive scaling rule

Suppose a rational coefficient vector $v_n\$ is cleared by a positive common denominator $D_n\$, giving an integer vector $w_n=D_nv_n\$. Let
\[
c_n=\gcd\{ |$w_n$_j|:j\},
\\qquad w_n^{\mathrm{prim}}=w_n/c_n.
\]
For any linear functional $\Lambda\$,
\[
|\Lambda(w_n^{\mathrm{prim}})|=\frac{D_n}{c_n}|\Lambda(v_n)|.
\]
Thus gcd reduction itself cannot increase the error relative to the denominator-cleared integer vector, but denominator clearing can. The analytic estimate needed is
\[
\boxed{\frac{D_n}{c_n}|\Lambda(v_n)|\longrightarrow0,}
\]
not merely ( |\Lambda(v_n)|\to0). The same normalization must be used for the endpoint coefficient, the remainder, and the determinant/nonvanishing certificate.

## 3. Literature boundary found on 2026-11-15

The following are preprints or institutional research papers, not claims of a peer-reviewed consensus. They are relevant because they study this exact mixed system.

### 3.1 Diagonal type-I normality

Runlong Yu, *Computer-assisted diagonal Hermite–Padé normality via 239-adic discrete convexity* (University of Alabama repository, 2026-07-23), studies type-I Hermite–Padé combinations
\[
P_0(z)+P_1(z)e^z+P_2(z)G(z)
\]
with polynomial coefficients of degree at most $d$. It proves the expected maximal order of vanishing $3d+2$ for every $0\le d\le1{,}087{,}602{,}879$, by an exact 239-adic determinant/energy argument and a finite independently checked certificate.

**What this does give:** nondegeneracy of an enormous family of origin Taylor systems.

**What it does not give:** integer endpoint linear forms in $e+\pi$ whose primitive absolute values tend to zero. A determinant being nonzero and the order of vanishing being maximal are not denominator-height estimates at $z=1$.

Source: https://ir-api.ua.edu/api/core/bitstreams/e9bd0199-b010-4a9f-8344-228fe909f7a2/content

### 3.2 Primitive Laurent completion and endpoint arithmetic

Runlong Yu, *Primitive Laurent Completion and Endpoint Arithmetic in a Split–Machin Hermite–Padé System* (University of Alabama, listed 2026-08-21), uses the same (1,e^z,G(z)) system. Its main architecture distinguishes:

1. formal completion of missing moment directions;
2. realization on a primitive, saturated integral Laurent source;
3. the comparison of the resulting forcing lattice with the original polynomial source's distinguished endpoint plane.

On its canonical ray
\[
D=200r+37,\\quad L=20r+6,\\quad N=220r+40,\\quad M=440r+81,\\quad p_r=220r+42,
\]
the paper identifies an exact linear defect in the direct positive-moment construction, supplies a bounded Laurent realization with full-row-rank Taylor map, and derives an endpoint-lattice intersection theorem. In the notation of the paper,
\[
F_D^{\mathrm{Laur}}\cap\Pi_D=\mathbb Zx_D.
\]
The endpoint index is factored as
\[
\kappa_D=\theta_Da_D^{\mathrm{sel}},
\]
separating a selector-free lattice index from the primitivity of the selected endpoint mark.

At the first legal instance $r=1$, the paper obtains
\[
\theta_1=17\cdot239^{44}>1.
\]
This is a genuine fixed-instance endpoint obstruction: the Laurent least mark is not visible in the original distinguished endpoint plane. It is not an irrationality theorem and does not settle the all-$r$ behavior.

The paper explicitly leaves open the all-$r$ classification of the rank jump and residual orders, selector primitivity, canonical transversality, and the simultaneous archimedean/denominator/normalization budget.

Source / landing page:
https://ir.ua.edu/items/8dc89475-beb6-47d8-8ee3-d8a92ec1e496

PDF:
https://ir-api.ua.edu/api/core/bitstreams/74a0b277-12c4-40d0-8832-a65834b7d96d/content

### 3.3 Positivity–smallness separation

Runlong Yu, *An Inverse Apéry Audit for $e+\pi$: Positivity–Smallness Separation* (University of Alabama, 2026-07-08), examines exact polynomial-to-linear-form identities and finite lattice/HP searches. Its findings distinguish two directions: small residuals and small kernels can be found without stable sign dominance, while sampled one-sign HP kernels can be abundant at enormous endpoint/kernel scale. A coupled scan of 2,411 candidate records did not produce a candidate satisfying the combined thresholds.

This is a bounded computational audit, not a universal no-go theorem. It cautions against treating sign control, origin vanishing, or a small unscaled residual as a substitute for the primitive endpoint error.

Source:
https://ir-api.ua.edu/api/core/bitstreams/1b23ff50-123e-4180-aab8-7f3f1a155e69/content

### 3.4 General $e+\pi$ certificate boundary

Runlong Yu, *Tail Criteria, No-Go Audits, and Apéry-Type Certificate Obstructions for the Irrationality of $e+\pi$*, arXiv:2606.17303v1 (2026-06-15), formulates the needed certificate as
\[
L_n=A_n(e+\pi)+B_n,\\\qquad
A_n,B_n\in\mathbb Z,\\\qquad0<|L_n|\to0.
\]
It also studies (S(z)=e^z+G(z)), (S(1)=e+\pi), and reports denominator-clearing obstructions for the diagonal Padé cases tested. The paper explicitly leaves irrationality open.

Source: https://arxiv.org/abs/2606.17303

## 4. Corrected finite Type-II diagnostic

To avoid conflating type-I normality with type-II common-denominator approximation, a separate exact-rational Taylor experiment was run for
\[
\begin{aligned}
Q(z)e^z-P(z)&=O(z^{N+1}),\\
Q(z)G(z)-R(z)&=O(z^{N+1}).
\end{aligned}
\]
with $\deg Q\le N=m+\ell$, $\deg P\le\ell$, and $\deg R\le m$.

The Taylor coefficients used were
\[
a_k=\frac1{k!},\\\qquad
g_k=0\ $k\text{ even}$,\\\qquad
g_k=(-1)^{(k-1)/2}\frac{16/5^k-4/239^k}{k}\ $k\text{ odd}$.
\]
The $N$ homogeneous equations for the $N+1$ coefficients of $Q$ were
\[
\sum_{j=0}^{k}q_ja_{k-j}=0
\quad(k=\ell+1,\ldots,N),
\]
\[
\sum_{j=0}^{k}q_jg_{k-j}=0
\quad(k=m+1,\ldots,N).
\]
For the symmetric diagonal $m=\ell=n$, the exact rational matrix had rank $2n$ and nullity one for $1\le n\le8$.

After computing (P,R), a common denominator was applied to all coefficients, their joint integer content was removed, and the endpoint form
\[
L_n=\widehat Q_n(1)$e+\pi$-\widehat P_n(1)-\widehat R_n(1)
\]
was evaluated at high precision. The following finite values were obtained:

| $n$ | rank / nullity | $\log_{10}|L_n|$ (approx.) |
|---:|---:|---:|
| 1 | 2 / 1 | 3.7312 |
| 2 | 4 / 1 | 17.9835 |
| 3 | 6 / 1 | 36.4265 |
| 4 | 8 / 1 | 60.7552 |
| 5 | 10 / 1 | 91.3153 |
| 6 | 12 / 1 | 127.6334 |
| 7 | 14 / 1 | 172.6832 |
| 8 | 16 / 1 | 222.0888 |

The $n=2$ and $n=3$ exact coefficient constructions and endpoint evaluations were independently checked with Wolfram Language. For example, at $n=2$,
\[
\widehat Q_2(1)=10192184477845863987,
\]
\[
\widehat P_2(1)+\widehat R_2(1)=58762129940028973924,
\]
and $L_2\approx9.62791798034\times10^{17}$.

**Interpretation:** this particular low-order type-II diagonal family is not a candidate certificate. The finite data are not a proof of an asymptotic no-go theorem, and they do not rule out other multi-indices, split sources, or signed-cancellation constructions.

**Audit correction:** an earlier exploratory script accidentally used floating-point division while reducing large integers. Its resulting table was withdrawn. The table above is from the corrected exact-integer/rational path, with the $n=2,3$ values independently checked in Wolfram. No conclusion relies on the withdrawn output.

## 5. A scalar truncation no-go that must not be overgeneralized

The Split–Machin paper also derives the signed error for the scalar truncation
\[
r_D=\sum_{k=0}^D\frac1{k!}
+16\sum_{k=0}^{2D+1}\frac{(-1)^k}{$2k+1$5^{2k+1}}
-4\sum_{k=0}^{2D}\frac{(-1)^k}{$2k+1$239^{2k+1}}.
\]
The remainder is positive and has leading scale
\[
e+\pi-r_D=
\frac{200}{13(4D+5)5^{4D+5}}
\bigl(1+O(D^{-1})\bigr).
\]
The paper shows that the corresponding scalar 5-adic truncation loses the real 5-tail decay while the 239 contribution remains exponentially positive. **This rules out that scalar truncation only**; determinant, rank-two, split-channel, mixed-degree, and other coupled systems remain open.

This scalar result should be recorded as a stop rule for the obvious one-channel continuation, not promoted to a no-go theorem for all Hermite–Padé methods.

## 6. Chosen continuation for G

The new workstream is **formal endpoint-lattice arithmetic plus a quantitative post-normalization budget**, not a repeat of the finite Taylor search.

### Task A — formalize the generic rank-one endpoint-kernel lemma

Define an integer matrix $R_D:\mathbb Z^2\to\mathbb Z^{p_D}$. Prove a general theorem of the form:

- the rational rank of $R_D$ is one;
- $v_D=$b_D,\delta_D$$ is a primitive integer vector;
- (R_D(v_D)=0);

therefore
\[
\ker_{\mathbb Z}$R_D$=\mathbb Z v_D.
\]

This is the abstract algebra behind the endpoint-intersection statement. It should be formalized independently of the special-function analysis, tested against nonprimitive and rank-zero counterexamples, and audited with the project's pinned Mathlib version.

### Task B — formalize determinantal divisors and index factorization

Represent the forcing and endpoint lattices by exact integer matrices. Formalize the determinantal-divisor / Smith-normal-form identities that compute:
- the least positive endpoint mark;
- the index $\kappa_D$;
- the factorization $\kappa_D=\theta_Da_D^{\mathrm{sel}}$;
- the exceptional prime-primary residual factors $including the $17$-defect at $r=1$$.

The $r=1$ certificate is a regression test, not a replacement for the all-$r$ theorem.

### Task C — prove an all-$r$ arithmetic law

The decisive open arithmetic subproblem is to classify $\chi_r$, $\delta_r$, and selector primitivity uniformly on the canonical ray. A finite list of prime factors or a numerical recurrence guess is insufficient. The output must be an exact recurrence, a source-defined minor formula, or a uniform prime-local criterion.

### Task D — couple the same primitive source to an archimedean estimate

On the same chosen primitive source, establish an explicit inequality
\[
\frac{D_r}{c_r}\,|\mathcal R_r(1)|\le B_r,
\\\qquad B_r\to0,
\]
where $D_r$ is the common denominator and $c_r$ is the joint coefficient content. Separately prove nonvanishing, preferably by an exact determinant or endpoint-lattice invariant. Do not mix a small unscaled residual from one family with a nonvanishing determinant from a different family.

### Acceptance gate

A candidate reaches the mathematical acceptance gate only when all are proved:

1. Exact rational/integer coefficient construction, with no floating-point assumptions.
2. A single common source for all approximation channels and endpoint maps.
3. Exact common-denominator clearing and joint content computation.
4. Eventual nonvanishing of the primitive integer form (or the paired determinant condition).
5. A rigorous bound $B_r\to0$ after denominator clearing and primitive reduction.
6. A complete all-index argument, not a finite-data extrapolation.
7. Lean kernel verification, source proof-hole scan, axiom audit, and paranoid Comparator on the exact commit.

Until all seven hold, the output is a conditional criterion, a partial theorem, or a research diagnostic—not a proof of irrationality.

## 7. Tool and repository allocation

| Resource | Assigned responsibility | Status in this continuation / trust boundary |
|---|---|---|
| GitHub G | Isolated research branch, source notes, proof contracts, CI and review history. | Used. This continuation is stacked on PR #4; it does not edit main or rewrite PR #1. |
| Lean 4 + Mathlib v4.36.0-rc2 | Formalize integer matrices, primitive kernels, determinantal divisors, endpoint-index identities, and convergence criteria. | The only direct formal proof dependency. Keep the frozen manifest. |
| Sider Scholar | Locate arXiv and institutional versions; inspect authorship, dates, and whether a result claims irrationality. | Used for arXiv 2606.17303 metadata; broad OpenAlex search returned no matched papers. |
| Parallel Search / Fetch | Extract and cross-check the 2026 split-Machin and inverse-Apéry preprints. | Used. Search/fetch are literature evidence, not proof certificates. |
| Wolfram | Verify Machin's identity and independent exact finite Taylor-matrix / endpoint calculations. | Used for exact identity and $n=2,3$ checks; not used for any limit or universal claim. |
| SymPy 1.14.0 | Exact rational nullspace, coefficient clearing, content/gcd, and finite candidate ledger. | Used locally for the finite Type-II diagnostic only. |
| Context7 | Resolve the pinned Mathlib documentation target and find version-sensitive APIs. | Library ID resolved; the focused PowerSeries/gcd queries returned no matching docs. The pinned compiler/CI remains authoritative. |
| Macaulay2 | Explore syzygies, modules, saturation, and source-realization polynomial modules. | Role assigned; executable not installed in this environment. |
| GAP | Check finite abelian-group / invariant-factor calculations independently. | Role assigned; executable not installed. |
| SageMath | Recompute Smith forms, rational lattices, p-adic valuations, and LLL diagnostics independently. | Role assigned; executable not installed. |
| FLINT | Exact large integer and polynomial arithmetic cross-checks. | Role assigned; executable not installed. |
| cvc5 | Bounded integer-matrix and polynomial side-condition checks; search finite counterexamples to proposed lemmas. | Role assigned; executable not installed. |
| Naproche | Audit the prose proof for quantifier gaps, hidden assumptions, and circular use of nonvanishing. | Role assigned; executable not installed. |
| LeanDojo-v2 | Search Mathlib proof patterns and suggest tactic candidates for matrix/kernel lemmas. | Role assigned; stack not installed. Any suggestion must still be compiled and kernel-checked. |
| Rocq/Isabelle/MathComp/Metamath starred references | Compare independent integer-lattice and Smith-normal-form formalizations where useful. | Reference only; not in the trusted proof dependency. |

Only the Mathlib source pinned by the frozen Lake manifest is in the formal proof graph. Numerical systems, CAS tools, search, and theorem-search tools are untrusted discovery or corroboration aids.

## 8. Execution order

1. Freeze PR #4's exact head and manifest; work only on this isolated branch.
2. Add the independent integer-lattice kernel statement to a challenge module before implementation.
3. Formalize and test the generic rank-one/primitive-kernel lemma.
4. Add determinantal-divisor and endpoint-index contracts; independently recalculate the $r=1$ prime-17 regression certificate.
5. Only then encode the all-$r$ formulas from the paper's appendices and prove the uniform residual classification.
6. For each candidate family, maintain a machine-readable ledger containing degree/index, raw rational coefficients, common denominator $D_r$, coefficient content $c_r$, primitive vector, exact endpoint remainder, determinant/minors, and rigorous $B_r$.
7. Reject any family for which the primitive endpoint error fails to tend to zero. Preserve signed-cancellation candidates only if their nonzero property is proved independently.
8. Run the pinned warning-free build, source scan, axiom audit, and paranoid Comparator on the exact branch head. Open or update a draft PR only with the verified status and remaining gaps clearly stated.

## 9. Status statement

As of 2026-11-15, the unconditional irrationality and transcendence of $e+\pi$ remain unproved in G and are reported open in the sources checked. The present continuation narrows the next formal target to the endpoint-lattice residual and the same-source height/denominator budget. It supplies no new unconditional Diophantine theorem.
