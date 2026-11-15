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
| 239 | 44 | 0 | finite 239-primary exponent ceiling, plus localized membership for \((M_1/239^{44})w_1\) |

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
