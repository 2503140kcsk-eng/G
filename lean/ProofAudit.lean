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
def algebraic_add := AlgebraicNumberClosureFormalization.isAlgebraic_add
def algebraic_mul := AlgebraicNumberClosureFormalization.isAlgebraic_mul
def algebraic_neg := AlgebraicNumberClosureFormalization.isAlgebraic_neg
def algebraic_numbers_add := AlgebraicNumberClosureFormalization.algebraicNumbers_add
def algebraic_numbers_mul := AlgebraicNumberClosureFormalization.algebraicNumbers_mul
def algebraic_root_of_algebraic_coefficients :=
  AlgebraicNumberClosureFormalization.isAlgebraic_of_root_of_algebraic_coefficients
def algebraic_root_over_algebraic_extension :=
  AlgebraicNumberClosureFormalization.isAlgebraic_of_root_over_algebraic_extension
def transcendental_sum_or_product_of_left :=
  AlgebraicNumberClosureFormalization.transcendental_add_or_mul_of_left
def transcendental_sum_or_product :=
  AlgebraicNumberClosureFormalization.transcendental_add_or_mul

/-! ## Lindemann–Weierstrass and individual transcendence -/
def complex_exp_linear_independent := Complex.linearIndependent_exp
def complex_exp_algebraically_independent := Complex.algebraicIndependent_exp
def complex_exp_transcendental := Complex.transcendental_exp
def complex_e_transcendental := Complex.transcendental_e
def real_pi_transcendental := Real.transcendental_pi
def algebraic_imaginary_unit := HermiteLindemannBridge.isAlgebraic_complex_I
def lindemann_analytic_approximation :=
  HermiteLindemannBridge.lindemann_analytic_approximation
def hermite_lindemann_exp_transcendental :=
  HermiteLindemannBridge.transcendental_exp_of_algebraic
def rational_e_transcendental := HermiteLindemannBridge.transcendental_e
def rational_pi_transcendental := HermiteLindemannBridge.transcendental_pi

/-! ## Unconditional e + pi module -/
def e_and_pi_transcendental := _root_.e_and_pi_transcendental
def e_add_pi_or_mul_transcendental := _root_.e_add_pi_or_mul_transcendental

/-! ## Schanuel-conditional consequence -/
def schanuel_inputs_linear_independent :=
  SchanuelConditional.ePiSchanuelInputs_linearIndependent
def schanuel_generated_field_eq :=
  SchanuelConditional.generatedField_ePi_eq
def schanuel_transcendence_degree_bound :=
  SchanuelConditional.ePi_generatedField_trdeg_ge_two
def schanuel_pair_generates_field :=
  SchanuelConditional.ePiPairInGeneratedField_adjoin_eq_top
def schanuel_pair_field_algebraic :=
  SchanuelConditional.ePiPairInGeneratedField_isAlgebraic
def schanuel_pair_algebraically_independent :=
  SchanuelConditional.ePi_pair_algebraicIndependent
def schanuel_adjoin_i_algebraic :=
  SchanuelConditional.QAdjoinI_isAlgebraic
def schanuel_pair_independent_over_qi :=
  SchanuelConditional.ePi_pair_algebraicIndependent_over_QAdjoinI
def schanuel_implies_e_plus_pi_transcendental :=
  SchanuelConditional.transcendental_ePlusPi_of_schanuel

end ProofAudit
