# Paired resultant-type transcendence criterion — research note (2026-11-18)

## Status and scope

This branch formalizes a non-vacuous paired approximation criterion. The kernel-checked part consists of:

1. A Bézout-coprime pair of rational polynomials cannot vanish simultaneously at one real point.
2. A pairwise Bézout-coprime sequence has at most one polynomial vanishing at a fixed real point; its evaluations are therefore eventually nonzero.
3. If both evaluation channels have a fixed-power lower bound in the common height, then super-polynomial smallness of their minimum is contradictory.
4. Consequently, an abstract transcendence theorem follows once the fixed-power lower bound is supplied for every algebraic candidate.

The remaining central arithmetic theorem is **not yet proved**: derive the fixed-power lower bound from integer resultants, minimal polynomials, and explicit degree/height hypotheses. The abstract theorem exposes this exact missing input as the hypothesis hLiouville; it is not an axiom and does not conceal a sorry in implementation code.

## Correct non-vacuous statement

Let P_n,Q_n be in Q[X], and let H_n be natural numbers eventually exceeding 1. Assume:

- P is pairwise Bézout-coprime as a sequence: for i ≠ j, IsCoprime (P i) (P j);
- Q is pairwise Bézout-coprime as a sequence;
- for every fixed k in N, eventually
  min{|P_n(ξ)|, |Q_n(ξ)|} < H_n^(-k).

For an algebraic candidate ξ, suppose there is a fixed d = d(ξ) such that, eventually for every nonzero evaluation in either channel,
|P_n(ξ)| ≥ H_n^(-d), and |Q_n(ξ)| ≥ H_n^(-d).
Then ξ is not algebraic.

The sequence-level coprimality is important. The weaker condition that only P_n and Q_n are coprime to each other for each individual n does **not** imply their values are eventually nonzero at an algebraic candidate: one polynomial may keep having the candidate's minimal polynomial as a factor. Requiring both values to be arbitrarily small in the same index is also not useful: the Bézout/resultant identity already forbids simultaneous smallness at every real point, algebraic or not. The current formulation avoids both defects.

## Resultant derivation still to formalize

A useful sufficient arithmetic package is:

- P_n,Q_n in Z[X];
- a common height parameter H_n tending to infinity;
- coefficient heights H(P_n),H(Q_n) ≤ H_n^A;
- degree bounds deg P_n,deg Q_n ≤ c log_2 H_n, for fixed A,c > 0;
- each evaluation is nonzero eventually (provided by sequence-level coprimality).

Fix an algebraic ξ, and choose a primitive irreducible f in Z[X] with f(ξ)=0, degree D, leading coefficient a ≠ 0, and complex roots ξ=ξ_1,ξ_2,...,ξ_D. Write R for either P_n or Q_n. If R(ξ) ≠ 0, irreducibility gives gcd_Q[X](f,R)=1; hence the integer resultant is nonzero:
|Res(f,R)| = |a|^(deg R) * product_{j=1}^D |R(ξ_j)| ≥ 1.

Let C ≥ 1 bound all the fixed conjugates ξ_j. The elementary evaluation estimate is
|R(ξ_j)| ≤ (deg R+1) H(R) C^(deg R).
Consequently,
|R(ξ)| ≥ |a|^(-deg R) * ((deg R+1) H(R) C^(deg R))^(-(D-1)).

Choose integers K_a,K_C ≥ 0 with |a| ≤ 2^(K_a) and C ≤ 2^(K_C). For sufficiently large H_n, the logarithmic degree bound also gives deg R+1 ≤ H_n. Thus one may take, for example, the fixed exponent
d = (D-1)(A+1+K_C*c) + K_a*c
(or any larger integer) in
|R(ξ)| ≥ H_n^(-d).
The same argument applies separately to P_n and Q_n. This supplies the hLiouville premise of the abstract Lean theorem.

Proof obligations to implement next:

1. Formalize the coefficient-evaluation upper bound using Polynomial.eval₂_eq_sum_range and norm/sum estimates.
2. Show that f and R have nonzero resultant from irreducibility, the root condition, and R(ξ) ≠ 0.
3. Apply the resultant root-product formula and bound every non-target conjugate via Polynomial.IsRoot.norm_lt_cauchyBound (or an explicit fixed conjugate bound).
4. Derive the concrete exponent inequality from the logarithmic degree and height bounds.
5. Package the result as the algebraic lower-bound premise of the abstract criterion, then strengthen the current Polynomial Q interfaces to explicit integer-coefficient polynomial sequences or provide a denominator-clearing bridge with controlled height.

For rational-coefficient polynomial inputs, a denominator-clearing step is required before using integer resultant non-vanishing. Mathlib's pinned IsFractionRing.integerNormalization lemmas are a candidate bridge. An alternative is to use Algebra.natDenominator to scale an algebraic number into an algebraic integer, then transform each polynomial under the fixed scaling. The height change must be included explicitly in the estimate.

## Lean modules and audit boundary

- lean/ResultantSuperpolynomial.lean: proved fixed-power lower bound versus arbitrary-power upper bound contradiction.
- lean/ResultantPairedCriterion.lean: proved Bézout no-common-root, sequence eventual nonvanishing, paired contradiction, and the abstract transcendence theorem with explicit hLiouville.
- lean/ProofAudit.lean: exposes the implemented theorem surface and prints axiom dependencies.
- lean/ProofAuditChallenge.lean: independent statement contracts only; its sorry placeholders are deliberate and excluded from implementation builds.
- comparator.json: compares the solution's public theorem types against those independent contracts.

The project remains pinned to leanprover/lean4:v4.36.0-rc2 and Mathlib v4.36.0-rc2. Do not update the lockfile as part of this proof task. Only propext, Classical.choice, and Quot.sound are permitted in the central proof audit.

## Division of labour

| Resource | Assigned role | Trust boundary |
|---|---|---|
| GitHub connector | Source-of-truth commits, branch/PR management, CI logs, comparator and axiom-audit results | Only successful CI for the exact commit is evidence of a green build |
| Sider Scholar | Find papers on Gel'fond criteria, Mahler inequalities, resultants, algebraic heights | Literature discovery only; each theorem must be checked against the cited paper |
| Wolfram | Symbolic resultant examples and exact algebraic-number sanity checks | Computational experiments only; an attempted evaluation in this session failed internally |
| Context7 | Retrieve APIs matching the repository's pinned Mathlib version | API guidance only; Lean elaboration and kernel checking decide correctness |
| Parallel Search | Search and extract relevant primary/secondary literature and repository documentation | External evidence, not a proof dependency |
| GitLab Beta | Potential second CI/review mirror | No corresponding target project was found in the connected GitLab account; GitLab Orbit was unavailable |

| Starred repository supplied for this task | Assigned role |
|---|---|
| [Macaulay2/M2](https://github.com/Macaulay2/M2) | Experiment with elimination ideals, Sylvester matrices, resultants, and Gröbner bases |
| [sympy/sympy](https://github.com/sympy/sympy) | Exact symbolic resultants, polynomial transforms, and coefficient-height test cases |
| [sagemath/sage](https://github.com/sagemath/sage) | Minimal polynomials, number fields, embeddings, conjugates, and Galois-group experiments |
| [gap-system/gap](https://github.com/gap-system/gap) | Finite Galois/group examples and automorphism calculations |
| [naproche/naproche](https://github.com/naproche/naproche) | Audit the written proof for hidden quantifier changes, missing assumptions, and proof-flow gaps |
| [cvc5/cvc5](https://github.com/cvc5/cvc5) | Search bounded counterexamples and discharge finite arithmetic side conditions |
| [lean-dojo/LeanDojo-v2](https://github.com/lean-dojo/LeanDojo-v2) | Retrieve premise candidates and tactic suggestions for the pinned Lean goal states |
| [leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4) | Sole direct mathematics dependency and trusted theorem library for the Lean kernel proof |

These repositories have been assigned roles based on their documented project purpose; listing or inspecting their source does not mean their executables were run in this session. The trusted proof graph imports Mathlib only.

## Literature and API references

- K. Mahler, “An inequality for a pair of polynomials that are relatively prime” (1964): https://carmamaths.org/resources/mahler/docs/156.pdf
- B. Arbour and D. Roy, “A Gel'fond type criterion in degree two” (2004): https://www.impan.pl/shop/en/publication/transaction/download/product/82692
- V. Kumar and R. Tosi, “A simultaneous approximation problem for exponentials and logarithms” (2025): https://arxiv.org/abs/2505.20957
- Pinned Mathlib resultant API: https://github.com/leanprover-community/mathlib4/blob/v4.36.0-rc2/Mathlib/RingTheory/Polynomial/Resultant/Basic.lean
- Pinned Mathlib Cauchy root bound: https://github.com/leanprover-community/mathlib4/blob/v4.36.0-rc2/Mathlib/Analysis/Polynomial/CauchyBound.lean
- Pinned Mathlib denominator clearing: https://github.com/leanprover-community/mathlib4/blob/v4.36.0-rc2/Mathlib/RingTheory/Localization/Integral.lean
