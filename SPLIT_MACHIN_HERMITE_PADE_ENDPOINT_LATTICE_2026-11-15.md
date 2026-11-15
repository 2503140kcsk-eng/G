# Split–Machin Hermite–Padé: primitive endpoint-lattice continuation

**Snapshot:** 2026-11-15 (JST)  
**Branch:** \`research/split-machin-endpoint-lattice-2026-11-15\`  
**Base:** PR #4 head \`4d106ff9a81c2e6a28384a80c4a2feede0ee7b0c\`  
**Status:** research continuation and exact finite diagnostic; **no irrationality proof is claimed**.

## 1. Executive result

The next target is the arithmetic compatibility problem for the Split–Machin system
$$
G(z)=16\arctan(z/5)-4\arctan(z/239),\qquad G(1)=\pi,
$$
$$
(1,e^z,G(z)),\qquad S(z)=e^z+G(z),\quad S(1)=e+\pi.
$$

The 2026 literature has already established substantial parts of the analytic and lattice architecture. In particular, diagonal type-I normality and a primitive Laurent completion theorem are available as research results, but neither supplies the final height/denominator estimate needed for an irrationality certificate. The remaining task is to couple, on one and the same primitive source, (i) nonzero endpoint arithmetic, (ii) the endpoint-lattice index, and (iii) an archimedean error that tends to zero **after** all common-denominator and primitive-content operations.

This document records that boundary, a corrected finite type-II experiment, and a proof-oriented continuation plan. It deliberately does not repackage a finite computation or a published preprint as a proof of $e+\pi\notin\mathbb Q$.

## 2. Exact criteria already available in G

PR #4 contains the reusable common-denominator identity. For rational approximants $p/q$ to $x$ and $s/r$ to $y$,
$$
(qr)(x+y)-(rp+qs)=r(qx-p)+q(ry-s),
$$
hence
$$
|(qr)(x+y)-(rp+qs)|\le r|qx-p|+q|ry-s|.
$$

The right-hand side is the cross-weighted error budget. Separate limits $qx-p\to0$ and $ry-s\to0$ do not imply that this budget tends to zero.

G also contains a paired determinant criterion. If integer sequences $A_n,C_n$ satisfy, eventually,
$$
A_nC_{n+1}-A_{n+1}C_n\ne0,
$$
and
$$
|A_nx-C_n|+|A_{n+1}x-C_{n+1}|\longrightarrow0,
$$
then $x$ is irrational. The determinant guarantees that adjacent forms cannot both vanish at a rational $x$.

These are conditional bridge theorems. The missing input is a construction in the Split–Machin system that supplies the arithmetic hypotheses and the post-normalization decay.

### Primitive scaling rule

Suppose a rational coefficient vector $v_n$ is cleared by a positive common denominator $D_n$, giving an integer vector $w_n=D_nv_n$. Let
$$
c_n=\gcd\{|(w_n)_j|:j\},\qquad w_n^{\rm prim}=w_n/c_n.
$$
For any linear functional $\Lambda$,
$$
|\Lambda(w_n^{\rm prim})|=\frac{D_n}{c_n}|\Lambda(v_n)|.
$$

Thus gcd reduction itself cannot increase the error relative to the denominator-cleared integer vector, but denominator clearing can. The analytic estimate needed is
$$
\boxed{\frac{D_n}{c_n}|\Lambda(v_n)|\longrightarrow0,}
$$
not merely $|\Lambda(v_n)|\to0$. The same normalization must be used for the endpoint coefficient, the remainder, and the determinant/nonvanishing certificate.

## 3. Literature boundary found on 2026-11-15

The following are preprints or institutional research papers, not claims of a peer-reviewed consensus. They are relevant because they study this exact mixed system.

### 3.1 Diagonal type-I normality

Runlong Yu, *Computer-assisted diagonal Hermite–Padé normality via 239-adic discrete convexity* (University of Alabama repository, 2026-07-23), studies type-I Hermite–Padé combinations
$$
P_0(z)+P_1(z)e^z+P_2(z)G(z)
$$
with polynomial coefficients of degree at most $d$. It proves the expected maximal order of vanishing $3d+2$ for every $0\le d\le1{,}087{,}602{,}879$, by an exact 239-adic determinant/energy argument and a finite independently checked certificate.

**What this does give:** nondegeneracy of an enormous family of origin Taylor systems.

**What it does not give:** integer endpoint linear forms in $e+\pi$ whose primitive absolute values tend to zero. A determinant being nonzero and the order of vanishing being maximal are not denominator-height estimates at $z=1$.

Source: https://ir-api.ua.edu/api/core/bitstreams/e9bd0199-b010-4a9f-8344-228fe909f7a2/content

### 3.2 Primitive Laurent completion and endpoint arithmetic

Runlong Yu, *Primitive Laurent Completion and Endpoint Arithmetic in a Split–Machin Hermite–Padé System* (University of Alabama, listed 2026-08-21), uses the same $(1,e^z,G(z))$ system. Its main architecture distinguishes:

1. formal completion of missing moment directions;
2. realization on a primitive, saturated integral Laurent source;
3. comparison of the resulting forcing lattice with the original polynomial source's distinguished endpoint plane.

On its canonical ray
$$
D=200r+37,\quad L=20r+6,\quad N=220r+40,\quad
M=440r+81,\quad p_r=220r+42,
$$
the paper identifies an exact linear defect in the direct positive-moment construction, supplies a bounded Laurent realization with full-row-rank Taylor map, and derives an endpoint-lattice intersection theorem. In the notation of the paper,
$$
F_D^{\rm Laur}\cap\Pi_D=\mathbb Zx_D.
$$
The endpoint index is factored as
$$
\kappa_D=\theta_Da_D^{\rm sel},
$$
separating a selector-free lattice index from the primitivity of the selected endpoint mark.

At the first legal instance $r=1$, the paper obtains
$$
\theta_1=17\cdot239^{44}>1.
$$
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
$$
L_n=A_n(e+\pi)+B_n,\qquad
A_n,B_n\in\mathbb Z,\qquad0<|L_n|\to0.
$$
It also studies $S(z)=e^z+G(z)$, $S(1)=e+\pi$, and reports denominator-clearing obstructions for the diagonal Padé cases tested. The paper explicitly leaves irrationality open.

Source: https://arxiv.org/abs/2606.17303

## 4. Corrected finite type-II diagnostic

To avoid conflating type-I normality with type-II common-denominator approximation, a separate exact-rational Taylor experiment was run for
$$
\begin{aligned}
Q(z)e^z-P(z)&=O(z^{N+1}),\\
Q(z)G(z)-R(z)&=O(z^{N+1}).
\end{aligned}
$$
with $\deg Q\le N=m+\ell$, $\deg P\le\ell$, and $\deg R\le m$.

The Taylor coefficients used were
$$
a_k=\frac1{k!},\qquad
g_k=0\quad(k\text{ even}),\qquad
g_k=(-1)^{(k-1)/2}\frac{16/5^k-4/239^k}{k}\quad(k\text{ odd}).
$$
The $N$ homogeneous equations for the $N+1$ coefficients of $Q$ were
$$
\sum_{j=0}^{k}q_ja_{k-j}=0
\quad(k=\ell+1,\ldots,N),
$$
$$
\sum_{j=0}^{k}q_jg_{k-j}=0
\quad(k=m+1,\ldots,N).
$$
For the symmetric diagonal $m=\ell=n$, the exact rational matrix had rank $2n$ and nullity one for $1\le n\le8$.

After computing $P,R$, a common denominator was applied to all coefficients, their joint integer content was removed, and the endpoint form
$$
L_n=\widehat Q_n(1)(e+\pi)-\widehat P_n(1)-\widehat R_n(1)
$$
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
$$
\widehat Q_2(1)=10192184477845863987,
$$
$$
\widehat P_2(1)+\widehat R_2(1)=58762129940028973924,
$$
and $L_2\approx9.62791798034\times10^{17}$.

**Interpretation:** this particular low-order type-II diagonal family is not a candidate certificate. The finite data are not a proof of an asymptotic no-go theorem, and they do not rule out other multi-indices, split sources, or signed-cancellation constructions.

**Audit correction:** an earlier exploratory script accidentally used floating-point division while reducing large integers. Its resulting table was withdrawn. The table above is from the corrected exact-integer/rational path, with the $n=2,3$ values independently checked in Wolfram. No conclusion relies on the withdrawn output.



### Exact arithmetic ledger and independent verification

The complete eight-row record is stored in
\`data/split_machin_type_ii_diagonal_audit_2026-11-15.json\`.
It contains the matrix rank/nullity, joint common denominator, coefficient
content, and the high-precision logarithm of the normalized endpoint form.
Wolfram Language independently rebuilt the rational Taylor matrix for every
$n=1,\ldots,8$, verified ranks $2n$ and nullity one, cleared the joint
denominator, divided the joint coefficient content, and reproduced all eight
$\log_{10}|L_n|$ values. The content was one in every row; the common
denominators were $1195,1,1195,1,5975,1,5975,1$.

For the $r=1$ endpoint-index datum reported in the Laurent endpoint-arithmetic
preprint, Wolfram independently checked
$
17\cdot239^{44}
=7585017080433407590878271022167940357899238784003404874750825000878408791786146064790946637606736779711697,
$
with factorization $17^1 239^{44}$ and $239$ prime. This verifies the integer
arithmetic of the quoted fixed-instance invariant; it does **not** reconstruct
the source matrices or prove the invariant for other $r$.

The exact computational workflow and its scope are recorded in the JSON
ledger. These computations are diagnostic and reproducibility aids only.

## 5. A scalar truncation no-go that must not be overgeneralized

The Split–Machin paper also derives the signed error for the scalar truncation
$$
r_D=\sum_{k=0}^D\frac1{k!}
+16\sum_{k=0}^{2D+1}\frac{(-1)^k}{(2k+1)5^{2k+1}}
-4\sum_{k=0}^{2D}\frac{(-1)^k}{(2k+1)239^{2k+1}}.
$$
The remainder is positive and has leading scale
$$
e+\pi-r_D=
\frac{200}{13(4D+5)5^{4D+5}}
\bigl(1+O(D^{-1})\bigr).
$$
The paper shows that the corresponding scalar 5-adic truncation loses the real 5-tail decay while the 239 contribution remains exponentially positive. **This rules out that scalar truncation only**; determinant, rank-two, split-channel, mixed-degree, and other coupled systems remain open.

This scalar result should be recorded as a stop rule for the obvious one-channel continuation, not promoted to a no-go theorem for all Hermite–Padé methods.

## 6. Chosen continuation for G

The new workstream is **formal endpoint-lattice arithmetic plus a quantitative post-normalization budget**, not a repeat of the finite Taylor search.

### Completed Lean layer — primitive rank-one kernels

The branch now contains \`lean/IntegerEndpointLattice.lean\`, wired into
\`ProofAudit.lean\`, \`ProofAuditChallenge.lean\`, and \`comparator.json\`.
The formalized statements are:

1. \`exists_bezout_of_int_gcd_eq_one\`: extract an explicit integer Bezout
   witness from \`Int.gcd a b = 1\), using the pinned Mathlib extended-gcd
   identity \`Int.gcd_eq_gcd_ab\`.
2. \`integer_pair_multiple_of_bezout_and_determinant\`: a Bezout-primitive
   pair spans every integer pair on the same rational line.
3. \`integer_pair_multiple_of_gcd_one_and_determinant\`: the same result with
   primitivity expressed by gcd one.
4. \`integer_row_kernel_iff_anchor\` and its gcd-one variant: if an anchor row
   is actually included and every other row has zero determinant with it, the
   common integer kernel of all rows equals the anchor-row kernel.
5. \`integer_two_column_matrix_kernel_iff_anchor\`: the matrix form for
   \`Matrix ι (Fin 2) ℤ\`, with the vanishing anchor minors stated explicitly.
6. \`nonprimitive_pair_counterexample\`: without primitivity, collinearity
   does not imply integral proportionality; rows (2,2) and (1,1) give a
   concrete counterexample.

The proof uses only integer identities and Mathlib's extended gcd; no
floating-point or custom axiom is involved. The pinned Mathlib source
\`Mathlib/Data/Int/GCD.lean\` contains the cited \`Int.gcd_eq_gcd_ab\`,
\`Int.gcdA\`, and \`Int.gcdB\` declarations. Context7 resolved
\`/leanprover-community/mathlib4/v4.36.0-rc2\` but returned no focused snippets
for the exact queries, so the checked pinned source and the successful CI build
are the API evidence used here.

**Important boundary:** these theorems formalize the abstract saturation
step. They assume the source-specific collinearity condition
\[
a\,B_i=b\,A_i\quad\text{for every source row }i.
\]
They do not yet prove that condition for the Split–Machin endpoint matrix.
That source-specific determinant/minor identity is now the next exact
obligation, not something hidden inside the general lemma.



### Split–Machin success-coordinate specialization

A further Lean theorem now matches the notation of the endpoint-intersection
paper directly:
\`integer_endpoint_kernel_from_primitive_success\`.

For a two-column integer endpoint matrix $M$, its hypotheses are precisely:

- $\gcd(b_0,\delta)=1$;
- every row annihilates the old success vector,
  $M_{i,0}b_0+M_{i,1}\delta=0$;
- at least one row is nonzero.

Its conclusion is
$
\ker_{\mathbb Z}M
=\mathbb Z(b_0,\delta).
$
The proof converts the Bezout identity for $(b_0,\delta)$ into one for the
perpendicular row direction $(\delta,-b_0)$ and applies the nonzero-row
matrix theorem. In particular, it does not require the primitive direction
itself to occur as a matrix row.

This is the correct abstract specialization of Theorem 8.1: the paper's
$R_D$ has a nonzero row because its rational rank is one; the old success
relation supplies the row-annihilation equations; and the paper's
$\gcd(b_0(x_D),\delta_D)=1$ supplies primitivity. The remaining bridge is to
encode the paper's actual coefficient formulas for $R_D$ and certify these
three hypotheses from its source definitions, rather than merely instantiate
them as assumptions.


The latest extension also isolates the elementary row identity
\[
A_i b_0+B_i\delta=0
\quad\Longrightarrow\quad
\delta B_i=-b_0A_i.
\]
It is formalized as
\`endpoint_success_row_implies_anchor_minor\` and its family version
\`endpoint_success_rows_imply_anchor_minors\`. The source-specific theorem
\`integer_endpoint_kernel_from_primitive_success\` now takes the three
paper-level hypotheses (primitive old success coordinates, their annihilation
by every row, and one nonzero row) and concludes the exact cyclic integer
kernel. This removes the need to assume collinearity as a separate black-box
hypothesis: it is derived from the old success relation itself.


### Expanded exact $r=1$ arithmetic regression data

The JSON ledger now also records the paper's exact residual integer
$
\delta_1=159398051612822846779584203616462141285376240077766656
$
with prime factorization
$
\delta_1=2^{100}3^{20}7^6 11^3\\cdot17\\cdot19\\cdot23\\cdot31.
$
Using the paper's $\theta_1=17\\cdot239^{44}$, the maximal-minor content
$M_1=\\delta_1\\theta_1$ is
$
M_1=1209036944071067165377573032570313997496785708212807790734534682176883017241389374626133926218544316839846710894657778906837530834213495308229136309667319775232,
$
with factorization
$
M_1=2^{100}3^{20}7^6 11^3\\cdot17^2\\cdot19\\cdot23\\cdot31\\cdot239^{44}.
$
Wolfram verifies the multiplication and both factorizations exactly. The
paper's 499-column/261-coordinate membership and modular-dual certificates
are still distinct proof objects; this arithmetic check does not replace
them.

### Task A — derive the Split–Machin anchor-minor identities

Extract the concrete two-column endpoint map $R_D$ and instantiate the new theorem using the paper's coordinates $x_D=(b_0(x_D),\delta_D)$. Prove directly from the source definitions that:

- $\gcd(b_0(x_D),\delta_D)=1$;
- every endpoint row annihilates $x_D$;
- $R_D$ has a nonzero row (the paper already proves $\operatorname{rank}_{\mathbb Q}R_D=1$).

The Lean specialization then yields $\ker_{\mathbb Z}R_D=\mathbb Zx_D$. The remaining bridge is to encode the actual source coefficients and verify these hypotheses, not to re-prove the abstract rank-one kernel lemma.

### Task B — formalize determinantal divisors and index factorization

Represent the forcing and endpoint lattices by exact integer matrices. Formalize the determinantal-divisor / Smith-normal-form identities that compute:
- the least positive endpoint mark;
- the index $\kappa_D$;
- the factorization $\kappa_D=\theta_Da_D^{\rm sel}$;
- the exceptional prime-primary residual factors (including the 17-defect at $r=1$).

The $r=1$ certificate is a regression test, not a replacement for the all-$r$ theorem.

### Task C — prove an all-$r$ arithmetic law

The decisive open arithmetic subproblem is to classify $\chi_r$, $\delta_r$, and selector primitivity uniformly on the canonical ray. A finite list of prime factors or a numerical recurrence guess is insufficient. The output must be an exact recurrence, a source-defined minor formula, or a uniform prime-local criterion.

### Task D — couple the same primitive source to an archimedean estimate

On the same chosen primitive source, establish an explicit inequality
$$
\frac{D_r}{c_r}|\mathcal R_r(1)|\le B_r,
\qquad B_r\to0,
$$
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
| Parallel Search / Fetch | Extract and cross-check the 2026 Split–Machin and inverse-Apéry preprints. | Used. Search/fetch are literature evidence, not proof certificates. |
| Wolfram | Verify Machin's identity, exact rational nullspaces, common denominators, primitive contents, endpoint errors, and the fixed $r=1$ index arithmetic. | Used to recompute all $n=1,\ldots,8$ type-II table rows and $17\cdot239^{44}$; finite computations only, no limit or universal claim. |
| SymPy 1.14.0 | Exact rational nullspace, coefficient clearing, content/gcd, and finite candidate ledger. | Used locally for the finite type-II diagnostic only. |
| Context7 | Resolve the pinned Mathlib documentation target and find version-sensitive APIs. | Resolved the exact Mathlib v4.36.0-rc2 library ID; focused queries returned no snippets. The required gcd API was confirmed directly in the pinned Mathlib source and then compiled in CI. |
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
