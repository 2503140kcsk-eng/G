module
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

/-- e and π are individually transcendental, by the imported
    Lindemann–Weierstrass/Hermite–Lindemann proof. -/
theorem e_and_pi_transcendental :
    Transcendental ℚ (Real.exp 1) ∧ Transcendental ℚ Real.pi :=
  ⟨HermiteLindemannBridge.transcendental_e,
   HermiteLindemannBridge.transcendental_pi⟩

/-- Unconditionally, at least one of e+π and e*π is transcendental. -/
theorem e_add_pi_or_mul_transcendental :
    Transcendental ℚ ePlusPi ∨ Transcendental ℚ eTimesPi := by
  exact AlgebraicNumberClosureFormalization.transcendental_add_or_mul_of_left
    (K := ℚ) (A := ℝ) (x := Real.exp 1) (y := Real.pi)
    HermiteLindemannBridge.transcendental_e
/-!
EPlusPiTranscendental is only the target proposition, not a proved theorem.
The question whether it holds unconditionally remains open in the checked
literature. Do not replace this status with an axiom, sorry, or admit.
-/

#print axioms e_and_pi_transcendental
#print axioms e_add_pi_or_mul_transcendental
