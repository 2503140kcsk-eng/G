# Lean formalization workspace

The e + π file remains a statement-only artifact: it defines the exact real number, the transcendence predicate, and the unresolved target without claiming a proof.

A separate algebraic-field development lives in:
- G/AlgebraicElements.lean: the intermediate field of all algebraic elements, its explicit Field structure, field-operation closure, maximality, algebraic closedness under the ambient-field hypothesis, polynomial splitting, roots, and uniqueness.
- G/AxiomAudit.lean: theorem-by-theorem #print axioms output.

The project is pinned by lean-toolchain, lakefile.lean, and lake-manifest.json to Lean/mathlib v4.36.0-rc2 and exact transitive dependency revisions.

Run lake exe cache get and lake build. GitHub Actions also runs nanoda with sorry disallowed and axiom-audit. LeanChecker was attempted but the GitHub-hosted runner exited with code 139 even with one thread; it is not part of the blocking CI pipeline. Do not treat workflow configuration as a passing verification until the current run completes successfully.
