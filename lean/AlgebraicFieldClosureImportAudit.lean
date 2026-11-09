module

import AlgebraicFieldClosure

public section

/-!
# Downstream import audit

These checks run in a separate module that imports the solution. They ensure
that the module-system export preserves each theorem proof body, rather than
turning a public theorem into a new axiom for downstream users.
-/

/-- info: 'AlgebraicFieldClosure.isAlgebraic_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicFieldClosure.isAlgebraic_inv

/-- info: 'AlgebraicFieldClosure.isAlgebraic_nat_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicFieldClosure.isAlgebraic_nat_pow

/-- info: 'AlgebraicFieldClosure.isAlgebraic_int_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicFieldClosure.isAlgebraic_int_pow

/-- info: 'AlgebraicFieldClosure.finiteDimensional_adjoin_of_algebraic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicFieldClosure.finiteDimensional_adjoin_of_algebraic

/--
info: 'AlgebraicFieldClosure.algebraic_extension_of_finiteDimensional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AlgebraicFieldClosure.algebraic_extension_of_finiteDimensional

/--
info: 'AlgebraicFieldClosure.finite_iff_essFiniteType_and_algebraic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AlgebraicFieldClosure.finite_iff_essFiniteType_and_algebraic
