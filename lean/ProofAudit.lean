module
public import AlgebraicClosure
public import LindemannBasic
public import HermiteLindemannBridge
public import EPlusPi
public import SchanuelConditional

@[expose] public section

/-!
# Central proof-dependency audit

This module re-exports the project's main theorem declarations under one
namespace so the CI axiom-audit tool can inspect their complete transitive
proof dependencies with a single explicit root.

No new mathematical assumptions are introduced here.
-/

namespace ProofAudit

/-! ## Algebraic closure and descent -/
theorem algebraic_add : _ := AlgebraicNumberClosureFormalization.isAlgebraic_add
theorem algebraic_mul : _ := AlgebraicNumberClosureFormalization.isAlgebraic_mul
theorem algebraic_neg : _ := AlgebraicNumberClosureFormalization.isAlgebraic_neg
theorem algebraic_numbers_add : _ := AlgebraicNumberClosureFormalization.algebraicNumbers_add
theorem algebraic_numbers_mul : _ := AlgebraicNumberClosureFormalization.algebraicNumbers_mul
theorem algebraic_root_of_algebraic_coefficients : _ :=
  AlgebraicNumberClosureFormalization.isAlgebraic_of_root_of_algebraic_coefficients
theorem algebraic_root_over_algebraic_extension : _ :=
  AlgebraicNumberClosureFormalization.isAlgebraic_of_root_over_algebraic_extension
theorem transcendental_sum_or_product_of_left : _ :=
  AlgebraicNumberClosureFormalization.transcendental_add_or_mul_of_left
theorem transcendental_sum_or_product : _ :=
  AlgebraicNumberClosureFormalization.transcendental_add_or_mul

/-! ## Lindemann–Weierstrass and individual transcendence -/
theorem complex_exp_linear_independent : _ := Complex.linearIndependent_exp
theorem complex_exp_algebraically_independent : _ := Complex.algebraicIndependent_exp
theorem complex_exp_transcendental : _ := Complex.transcendental_exp
theorem complex_e_transcendental : _ := Complex.transcendental_e
theorem real_pi_transcendental : _ := Real.transcendental_pi
theorem algebraic_imaginary_unit : _ := HermiteLindemannBridge.isAlgebraic_complex_I
theorem lindemann_analytic_approximation : _ :=
  HermiteLindemannBridge.lindemann_analytic_approximation
theorem hermite_lindemann_exp_transcendental : _ :=
  HermiteLindemannBridge.transcendental_exp_of_algebraic
theorem rational_e_transcendental : _ := HermiteLindemannBridge.transcendental_e
theorem rational_pi_transcendental : _ := HermiteLindemannBridge.transcendental_pi

/-! ## Unconditional e + pi module -/
theorem e_and_pi_transcendental : _ := _root_.e_and_pi_transcendental
theorem e_add_pi_or_mul_transcendental : _ := _root_.e_add_pi_or_mul_transcendental

/-! ## Schanuel-conditional consequence -/
theorem schanuel_inputs_linear_independent : _ :=
  SchanuelConditional.ePiSchanuelInputs_linearIndependent
theorem schanuel_generated_field_eq : _ :=
  SchanuelConditional.generatedField_ePi_eq
theorem schanuel_transcendence_degree_bound : _ :=
  SchanuelConditional.ePi_generatedField_trdeg_ge_two
theorem schanuel_pair_generates_field : _ :=
  SchanuelConditional.ePiPairInGeneratedField_adjoin_eq_top
theorem schanuel_pair_field_algebraic : _ :=
  SchanuelConditional.ePiPairInGeneratedField_isAlgebraic
theorem schanuel_pair_algebraically_independent : _ :=
  SchanuelConditional.ePi_pair_algebraicIndependent
theorem schanuel_adjoin_i_algebraic : _ :=
  SchanuelConditional.QAdjoinI_isAlgebraic
theorem schanuel_pair_independent_over_qi : _ :=
  SchanuelConditional.ePi_pair_algebraicIndependent_over_QAdjoinI
theorem schanuel_implies_e_plus_pi_transcendental : _ :=
  SchanuelConditional.transcendental_ePlusPi_of_schanuel

end ProofAudit
