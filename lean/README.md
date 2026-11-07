# Lean formalization workspace

The initial formal artifact defines:
- e + π as Real.exp 1 + Real.pi;
- transcendence over ℚ as the non-vanishing of every nonzero polynomial in ℚ[X];
- the target proposition without asserting it as an axiom or theorem.

This is a statement-only milestone, not a proof. The next implementation milestone is to establish elementary algebraic-closure lemmas and the sum/product disjunction, then audit classical inputs and the exact mathlib API.

Build configuration has deliberately not been guessed. Pin a Lean toolchain and mathlib revision before claiming reproducibility or CI success.
