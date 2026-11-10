module
public import Mathlib
public import AlgebraicClosure

@[expose] public section

/-!
# The arithmetic status of e + π

This file defines the exact real number and the target property.
It intentionally contains no axiom, sorry, or theorem claiming that
the target is unconditionally transcendental.
-/ 

/-- The real number e + π, represented using Mathlib's real exponential and pi. -/
noncomputable def ePlusPi : ℝ := Real.exp 1 + Real.pi

/-- The corresponding product e * π. -/
noncomputable def eTimesPi : ℝ := Real.exp 1 * Real.pi

/-- A real number is transcendental over ℚ if no nonzero rational polynomial
    vanishes at it. -/
def IsTranscendentalOverQ (x : ℝ) : Prop :=
  ∀ p : Polynomial ℚ, p ≠ 0 → Polynomial.aeval x p ≠ 0

/-- The open target: prove that e + π is transcendental over ℚ. -/
def EPlusPiTranscendental : Prop :=
  IsTranscendentalOverQ ePlusPi

/--
Unconditionally in the algebraic sense, transcendence of e implies that
at least one of e+π and e*π is transcendental. The proof does not yet
supply the Hermite–Lindemann input for e; that is kept as an explicit
hypothesis rather than an axiom.
-/
theorem e_add_pi_or_mul_transcendental
    (he : Transcendental ℚ (Real.exp 1)) :
    Transcendental ℚ ePlusPi ∨ Transcendental ℚ eTimesPi := by
  simpa [ePlusPi, eTimesPi] using
    AlgebraicNumberClosureFormalization.transcendental_add_or_mul_of_left
      (K := ℚ) (A := ℝ) (x := Real.exp 1) (y := Real.pi) he

/-!
This is a statement, not a theorem:
  #check EPlusPiTranscendental

Do not add axiom, sorry, or admit to turn the target into an apparent
proof. The target remains open as of the literature snapshot dated 2026-11-10.
-/

#print axioms e_add_pi_or_mul_transcendental
