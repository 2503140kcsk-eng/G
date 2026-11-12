module
public import AlgebraicClosure
public import LindemannBasic
public import HermiteLindemannBridge
public import EPlusPi
public import SchanuelConditional

@[expose] public section

/-!
# Central proof-dependency audit

The declarations below restate the project's key theorems with explicit types.
CI runs axiom-audit with root `ProofAudit`; the audit therefore follows each
proof's complete transitive dependency graph, including the algebraic-closure
lemmas, the vendored Lindemann–Weierstrass proof, Mathlib's analytic estimate,
and the Schanuel field-theory argument.

No new mathematical assumption is introduced here.
-/

namespace ProofAudit

/-- The complex exponential value exp(1) is transcendental over ℤ. -/
theorem complex_e_transcendental :
    Transcendental ℤ (Complex.exp (1 : ℂ)) :=
  Complex.transcendental_e

/-- The real number π is transcendental over ℤ. -/
theorem real_pi_transcendental :
    Transcendental ℤ Real.pi :=
  Real.transcendental_pi

/-- The rational-base Hermite–Lindemann consequence for e. -/
theorem rational_e_transcendental :
    Transcendental ℚ (Real.exp 1) :=
  HermiteLindemannBridge.transcendental_e

/-- The rational-base Lindemann consequence for π. -/
theorem rational_pi_transcendental :
    Transcendental ℚ Real.pi :=
  HermiteLindemannBridge.transcendental_pi

/-- Unconditionally, at least one of e+π and eπ is transcendental. -/
theorem e_add_pi_or_mul_transcendental :
    Transcendental ℚ ePlusPi ∨ Transcendental ℚ eTimesPi :=
  _root_.e_add_pi_or_mul_transcendental

/-- Schanuel's conjecture conditionally implies transcendence of e+π. -/
theorem schanuel_implies_e_plus_pi_transcendental
    (hSC : SchanuelConditional.SchanuelConjecture) :
    Transcendental ℚ ePlusPi :=
  SchanuelConditional.transcendental_ePlusPi_of_schanuel hSC

end ProofAudit
