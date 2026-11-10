module
public import Mathlib
public import AlgebraicClosure
public import HermiteLindemannBridge

@[expose] public section

/-!
# The arithmetic status of e + π

The unconditional open target is stated in this file, separately from
the conditional Hermite–Lindemann input and from Schanuel's conjecture.
No axiom, sorry, or admit is used to claim the open target.
-/

/-- The real number e + π, represented using Mathlib's real exponential and pi. -/
noncomputable def ePlusPi : ℝ := Real.exp 1 + Real.pi

/-- The corresponding product e * π. -/
noncomputable def eTimesPi : ℝ := Real.exp 1 * Real.pi

/-- The open target: e + π is transcendental over ℚ. -/
def EPlusPiTranscendental : Prop :=
  Transcendental ℚ ePlusPi

/--
If e is transcendental, at least one of e+π and e*π is transcendental.
This is an unconditional algebraic implication; its only hypothesis is
the independently established transcendence of e.
-/
theorem e_add_pi_or_mul_transcendental
    (he : Transcendental ℚ (Real.exp 1)) :
    Transcendental ℚ ePlusPi ∨ Transcendental ℚ eTimesPi := by
  simpa [ePlusPi, eTimesPi] using
    AlgebraicNumberClosureFormalization.transcendental_add_or_mul_of_left
      (K := ℚ) (A := ℝ) (x := Real.exp 1) (y := Real.pi) he

/--
Hermite–Lindemann gives the separate transcendence statements for e and π.
The analytic Hermite–Lindemann statement is a hypothesis here, not an axiom.
-/
theorem e_and_pi_transcendental_of_hermite_lindemann
    (hHL : HermiteLindemannBridge.HermiteLindemannInput) :
    Transcendental ℚ (Real.exp 1) ∧ Transcendental ℚ Real.pi :=
  ⟨HermiteLindemannBridge.transcendental_e_of_hermite_lindemann hHL,
   HermiteLindemannBridge.transcendental_pi_of_hermite_lindemann hHL⟩

/--
Combining the explicit Hermite–Lindemann input with the quadratic
algebraic argument proves the sum/product alternative.
This does not identify which of the two numbers is transcendental.
-/
theorem e_add_pi_or_mul_transcendental_of_hermite_lindemann
    (hHL : HermiteLindemannBridge.HermiteLindemannInput) :
    Transcendental ℚ ePlusPi ∨ Transcendental ℚ eTimesPi :=
  e_add_pi_or_mul_transcendental
    (HermiteLindemannBridge.transcendental_e_of_hermite_lindemann hHL)

/-!
EPlusPiTranscendental is only the target proposition, not a proved theorem.
The question whether it holds unconditionally remains open in the checked
literature. Do not replace this status with an axiom, sorry, or admit.
-/

#print axioms e_add_pi_or_mul_transcendental
#print axioms e_and_pi_transcendental_of_hermite_lindemann
#print axioms e_add_pi_or_mul_transcendental_of_hermite_lindemann
