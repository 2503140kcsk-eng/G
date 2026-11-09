# Lean formalization workspace

## Toolchain

This package is pinned to:

- Lean: `leanprover/lean4:v4.36.0-rc2`
- Mathlib: `v4.36.0-rc2`

From the repository root:

```sh
cd lean
lake update
lake exe cache get
lake build --wfail
lake comparator --config=comparator.json --paranoid
```

The CI workflow installs a pinned Elan v4.2.4 release asset, installs the exact toolchain from `lean-toolchain`, fetches the matching Mathlib cache, and builds with warnings treated as errors. It then runs the Comparator challenge with all paranoid checkers inside the Bubblewrap sandbox.

## What the Comparator check establishes

- `AlgebraicFieldClosureChallenge.lean` is the separately maintained statement baseline.
- `AlgebraicFieldClosure.lean` is the solution module.
- `comparator.json` names the six declarations whose types must match between the challenge and solution and permits only Lean's standard logical axioms: `propext`, `Classical.choice`, and `Quot.sound`.
- `lake comparator --config=comparator.json --paranoid` checks that the solution proves the challenge statements, uses no unpermitted axioms, and is accepted by Lean's kernel and all additional checkers bundled with the pinned Lean toolchain.

The trust boundary is intentional and explicit: the challenge module, the Lake configuration, and their transitive imports must be trusted. Mathlib is therefore pinned to `v4.36.0-rc2` and treated as a trusted dependency for this targeted theorem check. Comparator independently checks the six solution declarations; this does **not** claim that every declaration in the full Mathlib import closure has been independently replayed.

A separate, more expensive full dependency audit is available through `lake check --paranoid`. The GitHub Actions workflow exposes it as an opt-in `workflow_dispatch` input named `full_dependency_audit`. This full-closure audit is deliberately separate from the normal targeted check because it replays a very large transitive Mathlib environment.

## Formalized results

`AlgebraicFieldClosure.lean` contains:

1. `isAlgebraic_inv`: inversion preserves algebraicity.
2. `isAlgebraic_nat_pow`: nonnegative powers preserve algebraicity.
3. `isAlgebraic_int_pow`: all integer powers preserve algebraicity.
4. `finiteDimensional_adjoin_of_algebraic`: adjoining a finite set of algebraic elements gives a finite-dimensional intermediate field.
5. `algebraic_extension_of_finiteDimensional`: finite-dimensional field extensions are algebraic.
6. `finite_iff_essFiniteType_and_algebraic`: a field extension is module-finite exactly when it is algebraic and essentially of finite type. For field extensions, mathlib's `IntermediateField.fg_top_iff` identifies this finiteness condition with finite generation as a field.

No separability hypothesis is required. The finite-generator theorem is formalized through Mathlib's `IntermediateField.finiteDimensional_adjoin`; the finite-generation criterion uses `Algebra.finite_of_essFiniteType_of_isAlgebraic`.

## Important convention

Lean fields use totalized inversion, so `0⁻¹ = 0`, and integer powers are totalized as well. Therefore the formal inverse and negative-power lemmas do not need a nonzero hypothesis. In the usual textbook statement, negative powers are considered only for nonzero elements.

## Proof integrity and status

The solution file includes `#print axioms` for every theorem. In the previously completed build on commit `e31621e`, all six declarations compiled with `lake build --wfail`; their reported axioms were exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

That historical run also reported that Lean's paranoid kernel accepted the solution and that lean4lean accepted it after checking 290,765 declarations. The runner shut down while nanoda was running, so nanoda, con-leche, and con-ron were **not** all confirmed on that run. Do not treat the historical run as a complete five-checker pass.

The current CI uses the targeted Comparator challenge described above. A result is considered fully verified under that trust boundary only after the current pinned CI run succeeds. The optional full-closure audit is a separate stronger check.

These are classical field-theory results. They do not settle the repository's separate open target that `e + π` is transcendental.
