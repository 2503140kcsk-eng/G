# Appendix D certificate reconstruction — 2026-11-15

## Source identity

Runlong Yu, *Primitive Laurent Completion and Endpoint Arithmetic in a Split–Machin Hermite–Padé System*, University of Alabama repository item 8dc89475-beb6-47d8-8ee3-d8a92ec1e496.

- Item: https://ir.ua.edu/items/8dc89475-beb6-47d8-8ee3-d8a92ec1e496
- PDF: https://ir.ua.edu/bitstreams/74a0b277-12c4-40d0-8832-a65834b7d96d/download
- Repository date: 2026-08-21
- Appendix D: printed PDF page 48.

## Critical data-availability result

The paper states that the witness arrays are large and machine-readable, but the repository item page lists only the PDF and its license file. No supplementary data bundle or code archive is attached to that item. The PDF itself specifies the certificate conditions but does **not** print the 261×499 matrix, target vector, or the nine separator/coefficient vectors.

Consequently, this branch records the source-reported arithmetic below but does not fabricate the missing arrays and does not claim to have replayed the nine matrix checks. The missing artifacts required to complete that replay are:

- A_res_1: 261×499 integer matrix;
- w_1: 261-coordinate integer target;
- seven prime-power modular dual separators for p = 2, 3, 7, 11, 19, 23, 31, with each local exponent and target specified below;
- for p = 17: one 499-coordinate integral membership vector and one 261-coordinate modular dual separator;
- for p = 239: the explicit exponent ceiling K = 259, plus a finite-congruence/localized-membership certificate modulo 239^259 for the 499-column residual presentation, with the denominator/unit witness.

No reconstructed matrix or vector should be substituted for these source arrays.

## Reconstructing the residual presentation from the paper's formulas

The paper does specify a reconstruction *pipeline*, even though it does not publish the resulting arrays. In the canonical ray,
\[
D=200r+37,\quad L=20r+6,\quad p_r=220r+42,\quad
I_D=\{N_D,\ldots,M_D\}
\]
with \(N_D=220r+40\) and \(M_D=440r+81\). It defines
\[
P(z)=(z^2+25)(z^2+239^2),\quad
Q_r(z)=\frac{P(z)^{2r}}{(2r)!(25\cdot239^2)^{2r}},\quad
F_r(z)=Q_r(z)G(z)=\sum_{n\ge0}f_nz^n.
\]
The endpoint value is
\[
q_{\rm end,r}=Q_r(1)=\frac{(26/25)^{2r}(57122/57121)^{2r}}{(2r)!}.
\]
Writing \(q_{\rm end,r}=\alpha_D/\beta_D\) in lowest terms and
\(g_D=\gcd(\beta_D,D!)\), the primitive endpoint pair is
\[
\lambda_D=\beta_D/g_D,\qquad \sigma_D=D!\alpha_D/g_D.
\]
The fixed Taylor presentation has row order \(n=N_D,\ldots,M_D\), and its polynomial block is specified by
\[
A^Q_D[n,a_k]=(k-n+1){n\choose k},\quad
A^Q_D[n,\rho_j]=n!(f_{n-j}-f_{n-1-j}),\quad
t^Q_D[n]=\lambda_Dn!f_n+\sigma_D{n\choose D}.
\]
The negative-shift columns are defined from the tail observations \(B_{D,-\ell}=T_D(G_\ell)\), with
\(G_\ell(z)=z^{-\ell}(F_r(z)-T_{<\ell}F_r(z))\) and
\(G_\ell(z)=\sum_{k\ge0}f_{k+\ell}z^k\). The paper then jointly clears and primitive-normalizes each complete row of
\([A^Q_D\mid B_{-D}\mid -t^Q_D]\), fixes the negative-column reversal, and calls the resulting blocks \(A_r,B_r,t_r\).

The saturated-coordinate and projected-coset stages then specify the residual presentation:
\[
W_r=\operatorname{span}_{\mathbb Q}(A_r)\cap\mathbb Z^{p_r},\quad
A_r=E_rX_r,\quad B_rK_{{\rm tail},r}=E_rY_r,\quad t_r=E_rs_r.
\]
For the first Smith phase choose unimodular \(U_{1,r},V_{1,r}\) with
\[
U_{1,r}X_rV_{1,r}=\operatorname{diag}(d_r,X_{1,r}),
\quad U_{1,r}s_r=(\alpha_r,\sigma_r),\quad
U_{1,r}Y_r=(\beta_r,Y'_r).
\]
Let \(J_r\) be a column-Hermite basis of
\(\{z\in\mathbb Z^{k_r}:\beta_rz\equiv0\pmod{d_r}\}\).
For \(q_{{\rm proj},r}=g_r/\gcd(g_r,\alpha_r)\), with
\(g_r=\gcd(d_r,\beta_{r,1},\ldots,\beta_{r,k_r})\), choose \(z_{0,r}\) satisfying
\(\beta_rz_{0,r}\equiv q_{{\rm proj},r}\alpha_r\pmod{d_r}\). The residual data are
\[
A_{{\rm res},r}=[X_{1,r}\mid Y'_rJ_r],\quad
w_r\equiv q_{{\rm proj},r}\sigma_r-Y'_rz_{0,r}
\pmod{\operatorname{im}(Y'_rJ_r)}.
\]
At \(r=1\), \(a_1=262\), so the source-reported shape is
\(A_{{\rm res},1}\in\mathbb Z^{261\times499}\) and \(w_1\in\mathbb Z^{261}\).

This is an exact regeneration route, not a claim that the current branch has executed it. In particular, the paper does not pin down the machine-readable Smith transformations, Hermite-basis tie-breaking, the chosen \(z_{0,1}\), or the chosen representative \(w_1\) in the published item; those choices matter for reproducing the *same byte-for-byte* matrix and witness vectors, even though the residual group and its order are invariant under the allowed changes. That, together with the absent attachments, is why we have not fabricated an “actual” array.

## Source-reported fixed instance at r = 1

\[
D=237,\quad L=26,\quad A_{\rm res,1}\in\mathbb Z^{261\times499},\quad
w_1\in\mathbb Z^{261}.
\]

The allowed order is

\[
M_1=2^{100}3^{20}7^6 11^3 17^2 19\cdot23\cdot31\cdot239^{44}.
\]

The paper reports the local exponent vector, in the order
\((2,3,7,11,17,19,23,31,239)\), as

\[
(100,20,6,3,1,1,1,1,0).
\]

Thus the reported residual order is

\[
\delta_1=2^{100}3^{20}7^6 11^3\cdot17\cdot19\cdot23\cdot31
\]

\[
=159398051612822846779584203616462141285376240077766656.
\]

The reported quotient is

\[
M_1/\delta_1=17\cdot239^{44}
\]

\[
=7585017080433407590878271022167940357899238784003404874750825000878408791786146064790946637606736779711697.
\]

The exact product factorization is independently recomputed in Wolfram Language; this verifies the displayed arithmetic, not the unavailable matrix witnesses.

## Nine local certificate obligations

| Prime | \(v_p(M_1)\) | Reported \(v_p(\delta_1)\) | Appendix D certificate form |
|---:|---:|---:|---|
| 2 | 100 | 100 | dual separator modulo \(2^{100}\), detecting \((M_1/2)w_1\) |
| 3 | 20 | 20 | dual separator modulo \(3^{20}\), detecting \((M_1/3)w_1\) |
| 7 | 6 | 6 | dual separator modulo \(7^6\), detecting \((M_1/7)w_1\) |
| 11 | 3 | 3 | dual separator modulo \(11^3\), detecting \((M_1/11)w_1\) |
| 17 | 2 | 1 | integral membership for \((M_1/17)w_1\), plus dual nonmembership for \((M_1/17^2)w_1\) |
| 19 | 1 | 1 | dual separator modulo 19, detecting \((M_1/19)w_1\) |
| 23 | 1 | 1 | dual separator modulo 23, detecting \((M_1/23)w_1\) |
| 31 | 1 | 1 | dual separator modulo 31, detecting \((M_1/31)w_1\) |
| 239 | 44 | 0 | explicit K = 259: 239^259 Z^261_239 is contained in the localized residual lattice; localized membership for \\((M_1/239^{44})w_1\\) is reduced to a finite congruence modulo 239^259 |

The generic modular dual condition is:

\[
s^\top A_{\rm res,1}\equiv0\pmod{p^k},\qquad
s^\top y\not\equiv0\pmod{p^k}.
\]

Integral membership is the exact equation \(A_{\rm res,1}c=y\). Localized membership at 239 requires a denominator not divisible by 239 and an exact fraction-free equation after multiplying the target by that denominator.

## Formalization strategy

lean/IntegerLatticeCertificates.lean defines separate data types and soundness theorems for:
1. exact integral membership (A*c = y);
2. general modular-dual nonmembership;
3. prime-power modular-dual nonmembership;
4. localized membership with a denominator that is a unit at the chosen prime.

The paper's prime-local certificates are instances of these types once the original arrays are supplied. A certificate type is not itself a certificate instance: no nine data vectors are populated by this commit.

## General-r theorem boundary

For the all-r presentation A_res,r, the paper states the maximal-minor content formula. With \(\Delta_j(A)\) denoting the gcd of all \(j\times j\) minors,

\[
D_{{\rm res},r}=\Delta_{a_r-1}(A_{{\rm res},r}),\quad
E_{{\rm aug},r}=\Delta_{a_r-1}([A_{{\rm res},r}\mid w_r]),\quad
\delta_r=D_{{\rm res},r}/E_{{\rm aug},r}.
\]

This gives the all-r structural formula, but it does not decide all prime-local branches at every r. The nine-prime exponent classification in the cited result is only for r = 1.

## Fixed primitive lattice: exact denominator/content identity

Let \(x_n\in\mathbb Q^m\), choose \(D_n>0\) with \(z_n=D_nx_n\in\mathbb Z^m\), and write \(z_n=c_nv_n\), where \(c_n>0\) is the common content and \(v_n\) is primitive. For any fixed real linear functional \(F\),

\[
F(v_n)=\frac{D_n}{c_n}F(x_n).
\]

Therefore \(F(x_n)\to0\) alone does not imply \(F(v_n)\to0\). Example: \(x_n=1/(n+1)\), \(D_n=n+1\), \(z_n=1\), \(c_n=1\), \(v_n=1\), and \(F(t)=t\). The rational error tends to zero while the primitive integer error stays equal to one.

For a general r and prime p, the paper gives the finite-local ceiling K_{r,p} = v_p(D_{res,r}); at r = 1 and p = 239 it states that K = 259 suffices. The valid transfer hypothesis is the weighted convergence
\[
\frac{D_n}{c_n}|F(x_n)|\longrightarrow0.
\]
The Lean theorem returns both convergence of the primitive errors and membership of every primitive representative in the same fixed saturated lattice.

## Tool responsibility allocation

- **GitHub**: preserve this as an isolated branch, version source/data provenance, wire Lean modules, and run the pinned Actions build, axiom audit, and comparator.
- **Wolfram**: exact integer factorization and product consistency checks only; never treat a CAS output as a proof of the missing matrix identities.
- **Parallel Search/Fetch**: locate the primary paper, inspect Appendix D, and check whether a supplementary repository exists.
- **Sider Scholar**: literature search and bibliographic cross-check. The targeted title search did not return a matching indexed record in this run.
- **Context7**: library/API discovery. Its retrieval did not return useful Mathlib excerpts for the relevant theorem names; pinned Mathlib source files were inspected directly instead.
- **Mathlib4**: formal authority for the Lean statements. The pinned source exposes Submodule.smithNormalForm, Submodule.smithNormalFormOfRankEq, Smith diagonal coefficient APIs, and finite-index/determinant basis-change results.
- **SageMath**: independent exact Smith/normal-form, rank, gcd-of-minors, and modular linear-system cross-checks once arrays exist.
- **FLINT** (the exact integer arithmetic core used by Sage/SymPy integrations where appropriate): fast gcd, determinant, HNF/SNF and modular matrix arithmetic.
- **SymPy**: transparent small-case symbolic checks and independent determinant/recurrence calculations.
- **GAP**: finite abelian quotient and primary decomposition sanity checks.
- **Macaulay2**: polynomial/ideal elimination only if the all-r symbolic matrix construction is encoded polynomially.
- **cvc5**: bounded finite counterexample search for toy instances and certificate-schema edge cases; it does not prove the unbounded theorem.
- **LeanDojo-v2**: retrieve proof patterns and tactic suggestions; every final theorem remains kernel-checked by Lean.
- **Naproche**: audit the prose proof for hidden quantifier, rank, saturation, and localization assumptions.

These roles are task-specific. Unrelated installed apps and unrelated starred repositories do not improve this exact-integer proof and are not invoked. The role inventory is a research plan, not a claim that every external system was run.

## Verification status

- Source and appendix conditions located.
- Source-reported integer arithmetic independently recomputed.
- Certificate data types and generic soundness statements written to Lean.
- Full-r Smith-index theorem and weighted primitive-error convergence theorem written in Lean source.
- The 261×499 matrix and witness arrays remain unavailable from the primary repository item; the nine local proof instances are not yet reproduced.
- The new Lean module still requires a successful pinned build, axiom audit, and comparator run before any formal verification claim is made.
