# Factorial-Taylor Fusion: a Conditional No-Go Theorem

**Date:** 2026-11-15  
**Branch:** `research/factorial-taylor-fusion-obstruction-2026-11-14`  
**Verified implementation commit:** `bac0fb0b0151c99b6434c0b7a6951b81a748ac83`  
**CI:** [GitHub Actions run #391](https://github.com/2503140kcsk-eng/G/actions/runs/43662369506)

## 1. Existing factorial-Taylor approximants to e

Define
\[
T_n=\sum_{k=0}^{n}\frac1{k!},\qquad q_n=2n!,\qquad p_n=2n!T_n.
\]
Since `n!/k!` is an integer for `0 <= k <= n`, `p_n` is an integer. The associated integer-linear form is
\[
E_n=q_ne-p_n=2n!\left(e-T_n\right)>0.
\]
The first omitted term in the exponential series gives
\[
\frac1{(n+1)!}\le e-T_n.
\]
A geometric comparison of the remaining positive tail gives
\[
e-T_n\le \frac2{(n+1)!}.
\]
Therefore
\[
\boxed{\frac2{n+1}\le E_n\le\frac4{n+1}.}
\tag{1}
\]
The upper estimate was already present in the simultaneous polynomial-approximation development. The lower estimate is proved in `FactorialTaylorFusion.expTaylor_remainder_lower` and `FactorialTaylorFusion.factorialTaylor_linearForm_lower`.

## 2. The cross-weighted error budget forces a sublinear denominator

Let `r_n` be positive integers and `s_n` integers, intended to approximate pi by `s_n/r_n`. The common-denominator method uses the nonnegative budget
\[
F_n=r_n|q_ne-p_n|+q_n|r_n\pi-s_n|
=r_nE_n+2n!|r_n\pi-s_n|.
\tag{2}
\]
If `F_n -> 0`, then (1) yields
\[
0\le \frac{2r_n}{n+1}\le r_nE_n\le F_n\longrightarrow0.
\]
Thus the current e-side approximation imposes the necessary condition
\[
\boxed{\frac{r_n}{n+1}\longrightarrow0.}
\tag{3}
\]
This implication is kernel-checked as `FactorialTaylorFusion.factorialTaylor_denominator_sublinear_of_fusion_tendsto_zero` and exposed as `ProofAudit.factorial_taylor_fusion_forces_sublinear_pi_denominators` (Comparator contract 31).

## 3. The published Diophantine input for pi

Zeilberger and Zudilin prove the irrationality-measure bound
\[
\mu(\pi)\le 7.103205334137\ldots<7.104.
\]
Their definition says that for every `epsilon > 0`, all sufficiently large positive denominators `b`, and every integer numerator `a`,
\[
\left|\pi-\frac ab\right|>b^{-(\mu(\pi)+\epsilon)}.
\]
Choose `epsilon = 1/2`. Since `mu(pi) + 1/2 < 7.604 < 8`, for all sufficiently large `b` we obtain
\[
\left|\pi-\frac ab\right|>b^{-8},\qquad |b\pi-a|>b^{-7}.
\tag{4}
\]
The finitely many exceptional positive denominators can be absorbed into a single positive constant. For each fixed `b`, `b*pi` is irrational, so its distance from the integer lattice is positive. Taking the minimum over the finite exceptional set, after multiplying each distance by `b^7`, and including `1`, gives some `c > 0` such that
\[
\boxed{|b\pi-a|\ge \frac{c}{b^7}}
\quad\text{for every }b\in\mathbb N_{>0},\ a\in\mathbb Z.
\tag{5}
\]
**Formalization boundary:** the Lean no-go theorem accepts the global bound (5) as an explicit hypothesis. The finite-exception argument above is mathematically justified here, but the bridge from the published eventual measure bound to a global constant `c` is not yet a separate Lean theorem. The published irrationality-measure theorem is also not silently imported as an axiom or claimed to have been formalized by this repository.

**Primary source:** Doron Zeilberger and Wadim Zudilin, “The irrationality measure of pi is at most 7.103205334137…,” *Moscow Journal of Combinatorics and Number Theory* 9(4), 2020, DOI [10.2140/moscow.2020.9.407](https://doi.org/10.2140/moscow.2020.9.407). [Publisher PDF](https://msp.org/moscow/2020/9-4/moscow-v9-n4-p06-s.pdf).

## 4. Conditional no-go theorem

Assume for contradiction that `F_n -> 0`. By (3), eventually `r_n <= n+1`. The lower bound (5) then gives
\[
\begin{aligned}
F_n
&\ge 2n!\frac{c}{r_n^7}\\
&\ge \frac{2c\,n!}{(n+1)^7}.
\end{aligned}
\tag{6}
\]
Factorial growth dominates every fixed polynomial, so
\[
\frac{n!}{(n+1)^7}\longrightarrow+\infty.
\tag{7}
\]
The auxiliary Lean theorem `FactorialTaylorFusion.factorial_div_seventh_power_tendsto_atTop` proves (7) from Mathlib's factorial product inequality. Equations (6) and (7) contradict `F_n -> 0`. Hence
\[
\boxed{F_n\not\longrightarrow0.}
\]
The formal theorem is `FactorialTaylorFusion.factorialTaylor_fusion_not_tendsto_zero_of_pi_lower_bound`. Its hypotheses are explicit: `c > 0`, every `r_n > 0`, and the uniform lower bound `c/r_n^7 <= |r_n*pi-s_n|` for every `n`. The exported wrapper is `ProofAudit.factorial_taylor_fusion_no_go_from_pi_measure_lower_bound`, Comparator contract 32.

## 5. Exact scope of the obstruction

This result rules out one particular strategy:

1. Approximate `e` by the existing factorial Taylor forms with denominator `2*n!`.
2. Approximate `pi` by arbitrary rational forms `s_n/r_n`.
3. Use the sum of the two cross-weighted absolute errors (2) as the smallness certificate for common-denominator fusion.

It does **not** prove that `e + pi` is irrational or transcendental. It does not rule out every other Hermite-Pade family, mixed integral, or structured simultaneous construction.

It also does **not** rule out small signed fused forms produced by cancellation between the e-side and pi-side errors. The theorem concerns the nonnegative absolute-error budget (2), which is the sufficient bound used by the current generic common-denominator criterion. A signed-cancellation construction would still need an independent proof of eventual non-vanishing; assuming that property without proof could be circular.

The repository therefore retains the status: unconditional irrationality or transcendence of `e + pi` is not proved.

## 6. Independent finite checks

Wolfram and local SymPy 1.14.0 were used only as numerical and exact-arithmetic cross-checks. For `7 <= n <= 18`, the computed values of `E_n` lie in `[2/(n+1), 4/(n+1)]`. The growth term `2*n!/(n+1)^7` rises from approximately `0.00481` at `n=7`, exceeds `1` between `n=10` and `n=11`, and is approximately `1.43e7` at `n=18`. These finite values corroborate the formulas but do not prove (7); the Lean proof does.

The numerator and denominator pairs need not be coprime. This causes no issue: the integer-linear-form argument uses the actual coefficients `q_n,p_n`, and (5) applies to every integer numerator, whether or not the rational fraction is reduced.

## 7. CI certificate

Successful push run #391 on commit `bac0fb0b0151c99b6434c0b7a6951b81a748ac83`: [GitHub Actions run #391](https://github.com/2503140kcsk-eng/G/actions/runs/43662369506).

- The pinned manifest and Lean 4.36.0-rc2 checks passed.
- The implementation-source scan passed.
- The default build and `lake build --wfail` passed with no warnings.
- The axiom audit examined 41 declarations under `ProofAudit`; all stayed within `propext`, `Classical.choice`, and `Quot.sound`.
- The new no-go wrapper itself depends only on those same three allowed axioms.
- Comparator accepted all 32 public theorem statements.
- Lean paranoid kernel accepted the solution.
- lean4lean checked 58,038 declarations and accepted the solution.
- nanoda accepted the solution.
- con-leche accepted 58,037 declarations.
- con-ron accepted 58,037 declarations.
- Lean's default kernel accepted the solution.

The Comparator challenge intentionally contains `sorry` placeholders as statement specifications. It is excluded from the implementation proof-hole scan and is not imported by the solution. The pinned Mathlib dependency remains the mathematical-library trust boundary; this run does not independently replay every declaration in Mathlib's entire transitive import closure.
