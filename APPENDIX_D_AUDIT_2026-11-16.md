# Appendix D audit and proof-status addendum — 2026-11-16

## Executive result

This addendum records a source-level and CI-level audit of PR #7. The generic Lean proof layer is now verified by the pinned GitHub Actions workflow. The paper's actual 261-by-499 integer residual matrix, target, and witness vectors remain unavailable in the published repository item and were not reconstructed or fabricated. Consequently, none of the nine matrix-level prime-local certificate checks is claimed complete.

Primary source:
- Runlong Yu, *Primitive Laurent Completion and Endpoint Arithmetic in a Split–Machin Hermite–Padé System*, University of Alabama repository item: https://ir.ua.edu/items/8dc89475-beb6-47d8-8ee3-d8a92ec1e496
- PDF: https://ir.ua.edu/bitstreams/74a0b277-12c4-40d0-8832-a65834b7d96d/download
- Appendix D is printed page 48.
- The item page's file inventory contains one original-bundle PDF and a separate license file. Searches of the institutional item page, PDF text, exact matrix/order strings, and public code/data searches did not locate an attached supplementary array, source archive, or witness bundle.

## 1. Exact r = 1 source data that is available

The paper specifies the residual dimensions and arithmetic, but not the arrays themselves:

- (D=237), (L=26), (p_1=262).
- (A_{\mathrm{res},1}\in\mathbb Z^{261\times499}).
- (w_1\in\mathbb Z^{261}).
- The prime support of (M_1) is exactly ({2,3,7,11,17,19,23,31,239}).

The source-reported local exponent vectors, in that prime order, are
[
(v_p(M_1))=(100,20,6,3,2,1,1,1,44),
\qquad
(v_p(\delta_1))=(100,20,6,3,1,1,1,1,0).
]

Thus
[
\delta_1=2^{100}3^{20}7^6 11^3\cdot17\cdot19\cdot23\cdot31
=159398051612822846779584203616462141285376240077766656,
]
and
[
\theta_1=M_1/\delta_1=17\cdot239^{44}
=7585017080433407590878271022167940357899238784003404874750825000878408791786146064790946637606736779711697.
]
The complete reported modulus order is
[
M_1=\delta_1\theta_1
=2^{100}3^{20}7^6 11^3\cdot17^2\cdot19\cdot23\cdot31\cdot239^{44}.
]

An independent exact Wolfram Language computation on 2026-11-16 reproduced the displayed integer products and both prime factorizations. This is an arithmetic cross-check only; it does not verify any entry of (A_{\mathrm{res},1}), (w_1), or a local witness.

## 2. The nine Appendix D certificate obligations

All vectors below are source obligations, not available data values.

| Prime | Exponent in (M_1) | Exponent in (\delta_1) | Required exact evidence |
|---:|---:|---:|---|
| 2 | 100 | 100 | (s_2\in\mathbb Z^{261}) with (s_2^T A_{\mathrm{res},1}\equiv0\pmod{2^{100}}) and (s_2^T((M_1/2)w_1)\not\equiv0\pmod{2^{100}}). |
| 3 | 20 | 20 | The analogous dual separator modulo (3^{20}), detecting ((M_1/3)w_1). |
| 7 | 6 | 6 | The analogous dual separator modulo (7^6), detecting ((M_1/7)w_1). |
| 11 | 3 | 3 | The analogous dual separator modulo (11^3), detecting ((M_1/11)w_1). |
| 17 | 2 | 1 | An exact `c_17 ∈ ℤ^499` with `A_res,1 c_17 = (M_1/17)w_1`, and a dual nonmembership certificate for `(M_1/17²)w_1`. The paper does not specify its modulus in the displayed prose, so the Lean type leaves it arbitrary and nonzero. |
| 19 | 1 | 1 | A dual separator modulo 19, detecting ((M_1/19)w_1). |
| 23 | 1 | 1 | A dual separator modulo 23, detecting ((M_1/23)w_1). |
| 31 | 1 | 1 | A dual separator modulo 31, detecting ((M_1/31)w_1). |
| 239 | 44 | 0 | An explicit local exponent ceiling (K=259), together with localized membership of ((M_1/239^{44})w_1), represented fraction-free by a denominator not divisible by 239 and an exact equation after clearing that denominator. |

For an ordinary nonmembership witness modulo (q=p^k), the exact finite checks are:
[
\forall j<499,\quad q\mid\sum_{i<261}s_i A_{ij},
\qquad
q\nmid\sum_{i<261}s_i y_i.
]
For the membership witness, check all 261 equations in (A c=y). For localized membership at 239, check (u\not\equiv0\pmod{239}) and all 261 equations (u y=A c), plus the paper's finite-exponent-ceiling obligation.

The corresponding Lean structures already exist in `lean/IntegerLatticeCertificates.lean`. A populated structure value is still required for every source witness. The existence of a certificate type is not itself a concrete certificate.

## 3. Why the arrays have not been fabricated

The paper gives a regeneration pipeline from its coefficient formulas:

1. Construct the rational Taylor/moment matrix and forcing column using the source-defined (Q_r,F_r) and (f_n).
2. Jointly clear denominators and remove each complete row's content.
3. Apply the specified saturated-coordinate and projection stages.
4. Compute the Smith and column-Hermite transformations, including a selected (z_{0,r}), to obtain (A_{\mathrm{res},r}) and a representative (w_r).

The source does not provide the resulting Smith/Hermite transformation arrays, the chosen (z_{0,1}), the selected representative of the target residue class, or the nine local witnesses. The paper explicitly permits choices at the residual-representative stage. Hence the byte-for-byte (A_{\mathrm{res},1},w_1) pair and its vectors cannot be inferred from the dimensions, factorization, or theorem statements alone.

A valid reconstruction must publish:
- the exact convention for every allowed choice and pivot/order;
- the full 261×499 integer matrix and 261-entry target;
- all eight modular separator vectors, with their moduli and detected targets;
- the 499-entry p=17 membership vector;
- the p=239 unit denominator/coefficient witness and a verifiable (K=259) ceiling proof;
- checksums and a deterministic generator or independently checkable raw files.

Until these are obtained or regenerated exactly, the nine local checks remain open.

## 4. Smith factors, maximal minors, and the all-r formula

For a full-row-rank matrix (A\in\mathbb Z^{m\times n}), define the maximal determinantal divisor
[
\Delta_m(A)=\gcd\{\,|\det A_{[:,J]}|:J\subseteq\{1,\ldots,n\},\ |J|=m\,\}.
]
This is the **gcd of all maximal minors**, not their maximum absolute value.

The mathematical identity needed by the paper is
[
[\mathbb Z^m:A\mathbb Z^n]=\Delta_m(A)=\prod_{i=1}^m s_i,
]
where (s_1\mid s_2\mid\cdots\mid s_m) are the nonzero Smith invariant factors. Proof: choose unimodular (U,V) with (UAV=[\operatorname{diag}(s_1,\ldots,s_m)\mid0]). Left multiplication by (U) changes each maximal minor by the unit (\det U=\pm1). Cauchy–Binet shows that every maximal minor after right multiplication by (V) is an integer linear combination of the old maximal minors; applying the same argument to (V^{-1}) gives equality of the ideals generated by the maximal minors. In Smith form only one maximal minor is nonzero, and it is (s_1\cdots s_m). The index is invariant under these unimodular changes and is the same product.

For the augmented matrix ([A\mid w]), assuming it also has full row rank, the order of the class (w+A\mathbb Z^n) in the finite quotient is
[
\operatorname{ord}(w+A\mathbb Z^n)
=\frac{[\mathbb Z^m:A\mathbb Z^n]}{[\mathbb Z^m:A\mathbb Z^n+\mathbb Zw]}
=\frac{\Delta_m(A)}{\Delta_m([A\mid w])}.
]

Consequently the source's all-(r) structural formula is
[
D_{\mathrm{res},r}=\Delta_{a_r-1}(A_{\mathrm{res},r}),\quad
E_{\mathrm{aug},r}=\Delta_{a_r-1}([A_{\mathrm{res},r}\mid w_r]),\quad
\delta_r=D_{\mathrm{res},r}/E_{\mathrm{aug},r}.
]
For each prime (p), the residual valuation is the difference
(v_p(D_{\mathrm{res},r})-v_p(E_{\mathrm{aug},r})). A finite-local decision then uses the paper's ceiling (K_{r,p}=v_p(D_{\mathrm{res},r})) and a finite congruence modulo (p^{K_{r,p}}).

**Lean boundary:** PR #7 formalizes the full-rank index as the product of Mathlib's Smith diagonal coefficients, basis-change determinant/index identities, and the cyclic extension/index-tower relation. It does not yet formalize the rectangular maximal-minor gcd invariance (the Cauchy–Binet step above) or the composite theorem `maximalMinorGcd_eq_index`. Therefore the all-(r) statement is mathematically specified, but its direct matrix-level Lean bridge is still a TODO. The r=1 prime exponent classification must not be extrapolated to every r.

## 5. Primitive integerization and error convergence in one fixed lattice

Let (L\le\mathbb Z^m) be one fixed saturated (primitive) lattice: whenever (d\ne0) and (d v\in L), then (v\in L). For every (n), suppose:
- (x_n\in\mathbb Q^m);
- (D_n\in\mathbb N), (D_n>0);
- (z_n=D_nx_n\in\mathbb Z^m\cap L);
- (z_n=c_nv_n), with (c_n\in\mathbb N), (c_n>0), and (v_n\in\mathbb Z^m) primitive.

Then saturation gives (v_n\in L) for every (n). For any fixed real linear functional (F:\mathbb R^m\to\mathbb R), exact linearity gives
[
F(v_n)=\frac{D_n}{c_n}F(x_n),
\qquad
|F(v_n)|=\frac{D_n}{c_n}|F(x_n)|.
]
There is no approximation in this equality.

It follows that the exact sufficient-and-necessary convergence condition for this particular functional is
[
\frac{D_n}{c_n}|F(x_n)|\longrightarrow0.
]
A simpler sufficient condition is that (D_n/c_n\to b<\infty) and (F(x_n)\to0) (or merely that (D_n/c_n) is eventually bounded and the rational errors tend to zero).

Rational error decay alone is insufficient. Counterexample: (x_n=1/(n+1)), (D_n=n+1), (c_n=1), (v_n=1), and (F(t)=t). Then (F(x_n)\to0), but (F(v_n)=1) for every (n).

**Lean result already present and CI-checked:** `PrimitiveIntegerization.primitive_mem` keeps each primitive representative in the same (L); `primitive_pairing_eq_scaled_rational` proves the exact scaling formula; `tendsto_primitive_errors_of_weighted` proves the weighted transfer; and `tendsto_primitive_errors_of_ratio` proves the bounded/convergent-ratio corollary. These are unconditional abstract theorems. They do not by themselves supply a sequence (x_n) from the Split–Machin construction satisfying the weighted bound.

## 6. CI and trust audit for PR #7

The exact head commit before this addendum, `1c7cae54e615073c61069a5581a340255e4f3291`, passed GitHub Actions workflow run #551:
https://github.com/2503140kcsk-eng/G/actions/runs/43690643269

The successful job reported:
- frozen Lake manifest check passed;
- implementation-source proof-hole and custom-axiom scan passed;
- pinned Lean build and warning-free default build passed;
- comparator and paranoid checker stage passed;
- 58,465 declarations checked; con-leche and con-ron accepted 58,464 declarations each;
- all exported PR #7 certificate, Smith-index, primitive-membership, and weighted-convergence declarations were audited with only `propext`, `Classical.choice`, and `Quot.sound`.

The Comparator challenge file intentionally contains `sorry` statements as independent theorem specifications; those are not implementation proofs and are excluded from the implementation-source hole scan. This successful CI certifies the abstract declarations and current source graph, **not** the absent Appendix D matrix data or its nine unpopulated witness instances.

The repository continues to use the pinned Lean `v4.36.0-rc2` and Mathlib `v4.36.0-rc2` manifest. No dependency refresh is part of this addendum.

## 7. Task-specific resource and tool allocation

### Connected tools used in this audit

| Resource | Assigned responsibility | What was actually established in this pass |
|---|---|---|
| GitHub | Read the repository/PR, inspect source blobs, read CI job steps and logs, and store an auditable branch update. | PR #7 and run #551 inspected; this addendum is committed on the PR branch. |
| Parallel Search / Fetch | Find the primary institutional source, read Appendix D's verification conditions, and search for a supplementary data bundle or alternate public witness archive. | Paper and item inventory inspected; no public matrix/witness attachment found. Search/Fetch were used, not Parallel Research mode. |
| Sider Scholar | Search OpenAlex/Scholar-indexed literature and formalization references. | Exact title query returned no matching indexed paper in this search; a broader Smith-form search returned background literature only. |
| Wolfram | Verify exact integer products and prime factorizations independently. | Reproduced δ₁, θ₁, M₁ and their factorizations. No matrix witness was available to evaluate. |
| Context7 | Resolve version-sensitive Lean/Mathlib APIs. | Lean/mathlib library resolution was attempted; focused Mathlib queries returned no matching documentation. The pinned Mathlib source and CI build were used as API evidence instead. |
| GitLab | Check whether a corresponding GitLab project/mirror can be used. | The connected user profile is accessible, but `2503140kcsk-eng/G` returned 404 in GitLab. No GitLab repository was assumed or created. |

### User-starred repositories and the role boundary

The repository's 2026-11-10 public-star snapshot contains 30 public entries; that snapshot is recorded in `TOOLS_AND_PROOF_PROTOCOL.md`. Current authenticated-star enumeration was not available through the GitHub fetch endpoint in this pass, and private/inaccessible stars are not inferred.

For this integer-lattice task:
- `leanprover-community/mathlib4`: only direct formal-mathematics dependency; pinned and kernel checked.
- `Macaulay2/M2`: optional module/saturation and symbolic ideal exploration.
- `gap-system/gap`: optional finite abelian quotient and primary-decomposition cross-check.
- `sympy/sympy`: optional transparent exact-integer and small-instance regression checks.
- `sagemath/sage`: optional independent HNF/SNF, modular solving, and p-adic valuation checks.
- `flintlib/flint` (also listed in the project snapshot): optional exact large-integer and matrix backend.
- `cvc5/cvc5`: bounded counterexample search and finite side-condition checks only.
- `naproche/naproche`: written-proof quantifier/rank/saturation audit.
- `lean-dojo/LeanDojo-v2`: retrieve proof traces/tactic candidates; never a proof authority.
- Rocq/MathComp, Isabelle/AFP, Mizar and Metamath repositories in the snapshot: independent formalization/methodology comparisons only.
- The remaining starred graph/ordinal/large-number repositories are not relevant to this matrix problem and are not given artificial execution roles.

The starred projects are source repositories, not automatically available executables or callable ChatGPT services. In this session their GitHub sources were not mistaken for having run M2, GAP, SageMath, cvc5, Naproche, or LeanDojo. The only computational corroboration performed directly here was Wolfram's exact finite arithmetic; the formal proof authority was the pinned Lean CI.

### Cost and free-scope boundary

- Public GitHub source/PR inspection and the repository's public Actions run were used.
- Parallel Search/Fetch were used; the Parallel Research workflow was not invoked in this audit.
- No paid CAS, cloud theorem prover, or hosted data service was made a proof dependency.
- Provider account quotas/charges are not visible to this workflow. Do not interpret the availability of a connector as a guarantee that every third-party plan or future call is free.
- All optional open-source packages remain optional until an actual environment is available and their outputs are independently checked.

## 8. Next acceptance gates

1. Obtain the original array bundle from the author, or implement the entire rational-to-integer regeneration pipeline with every choice fixed and documented.
2. Publish (A_{\mathrm{res},1}), (w_1), and the eight modular/one localized membership witness data in a stable machine-readable format with checksums.
3. Instantiate all nine certificate structures and prove every row/column congruence or equality by exact integer computation and Lean kernel checking.
4. Formalize maximal-minor gcd invariance under unimodular transformations (Cauchy–Binet in both directions), then prove `maximalMinorGcd_eq_index` for full-row-rank rectangular integer matrices.
5. Derive the all-(r) residual order theorem from that bridge and the cyclic extension index theorem; keep the r=1 prime table as a fixed regression instance.
6. For any approximation family, provide one unchanged saturated lattice, exact denominators and contents, a same-source construction, a weighted error bound tending to zero, and an independent nonvanishing argument.
7. Re-run pinned build, warning-free build, source scan, axiom audit, Comparator and paranoid checkers on the exact final commit.

Until gates 1–3 are met, the correct status is: **generic certificate logic verified; actual Appendix D certificates not reproduced**. Until gates 4–5 are met, the direct rectangular maximal-minor/Smith bridge is a formalization gap. None of these partial results proves the irrationality or transcendence of (e+\pi).
