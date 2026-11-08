# Lean formalization workspace

## Toolchain

This package is pinned to:

- Lean: `leanprover/lean4:v4.36.0-rc2`
- Mathlib: `v4.36.0-rc2`

The package is located in this `lean/` directory. From the repository root:

```sh
cd lean
lake update
lake exe cache get
lake build --wfail
lake check --paranoid
```

The CI workflow uses a pinned Elan v4.2.4 release asset instead of the moving `elan-init.sh` latest-release URL. It installs the exact toolchain from `lean-toolchain`, fetches the matching Mathlib cache, builds with warnings treated as failures, and runs `lake check --paranoid`. The `AlgebraicFieldClosure` library is marked as Lake's default target so both commands inspect the intended Lean module.

## Formalized results

`AlgebraicFieldClosure.lean` contains:

1. `isAlgebraic_inv`: inversion preserves algebraicity.
2. `isAlgebraic_nat_pow`: nonnegative powers preserve algebraicity.
3. `isAlgebraic_int_pow`: all integer powers preserve algebraicity.
4. `finiteDimensional_adjoin_of_algebraic`: adjoining a finite set of algebraic elements gives a finite-dimensional intermediate field.
5. `algebraic_extension_of_finiteDimensional`: finite-dimensional field extensions are algebraic.
6. `finite_iff_essFiniteType_and_algebraic`: finite module extensions are exactly the extensions that are both algebraic and essentially of finite type. For field extensions, mathlib's `IntermediateField.fg_top_iff` identifies this finiteness condition with finite generation as a field.

No separability hypothesis is required. The finite-generator theorem is formalized through Mathlib's `IntermediateField.finiteDimensional_adjoin`; the finite-generation criterion uses `Algebra.finite_of_essFiniteType_of_isAlgebraic`.

## Important convention

Lean fields use totalized inversion, so (0^{-1}=0), and integer powers are totalized as well. Therefore the formal inverse and negative-power lemmas do not need a nonzero hypothesis. In the usual textbook statement over a field, negative powers are considered only for nonzero elements.

## Proof integrity

The file includes `#print axioms` commands for every declared theorem. `lake check --paranoid` replays the exported declarations through Lean's kernel and bundled independent checkers, accepting only the standard logical axioms. A result is considered verified only after the pinned CI run succeeds.

These are classical field-theory results. They do not settle the separate open target that (e+\pi) is transcendental.
