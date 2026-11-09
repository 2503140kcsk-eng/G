# Lean formalization workspace

The e + π file remains a statement-only artifact: it defines the exact real number, the transcendence predicate, and the unresolved target without claiming a proof.

A separate, fully proved algebraic-field development now lives in:
- G/AlgebraicElements.lean: the intermediate field of all algebraic elements, field-operation closure, maximality, algebraic closedness, splitting, roots, and uniqueness.
- G/AxiomAudit.lean: theorem-by-theorem #print axioms output.

The project is pinned by lean-toolchain and lakefile.lean to Lean/mathlib v4.36.0-rc2. Run lake exe cache get and lake build. GitHub Actions additionally runs LeanChecker, nanoda with sorry disallowed, and axiom-audit. Do not treat the workflow configuration as a passing build until its run succeeds.
