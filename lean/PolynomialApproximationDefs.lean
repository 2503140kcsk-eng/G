module
public import Mathlib

@[expose] public section

/-!
# Explicit integer-polynomial simultaneous approximation data

The definitions in this file are deliberately proof-free.  The challenge
module and the solution module import this same statement vocabulary.
-/

namespace SimultaneousPolynomialApproximation

open Polynomial

/-- The integer-coefficient Taylor numerator for the exponential:
    n! * (1 + X + X^2/2! + ... + X^n/n!). -/
noncomputable def taylorIntPoly (n : ℕ) : Polynomial ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    C (Int.ofNat (n.choose k * (n - k).factorial)) * X ^ k

/-- The common denominator n! (1 + X^2). -/
noncomputable def denominator (n : ℕ) : Polynomial ℤ :=
  C (Int.ofNat n.factorial) * (1 + X ^ 2)

/-- The exponential numerator (1 + X^2) times the integer Taylor numerator. -/
noncomputable def numerator (n : ℕ) : Polynomial ℤ :=
  (1 + X ^ 2) * taylorIntPoly n

/-- The exact numerator for the reciprocal function. -/
noncomputable def reciprocalNumerator (n : ℕ) : Polynomial ℤ :=
  C (Int.ofNat n.factorial)

/-- The integer value of the exponential Taylor numerator at the endpoint 1. -/
def endpointTaylorValue (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), n.choose k * (n - k).factorial

/-- Evaluation of an integer polynomial at a real number. -/
def evalReal (p : Polynomial ℤ) (x : ℝ) : ℝ :=
  p.eval₂ (Int.castRingHom ℝ) x

/-- Endpoint-value matrix, with rows x=0 and x=1 and columns Q_n and P_n. -/
noncomputable def endpointMatrix (n : ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![
    (denominator n).eval 0, (numerator n).eval 0;
    (denominator n).eval 1, (numerator n).eval 1
  ]

/-- The real Taylor polynomial used in the uniform error statement. -/
noncomputable def expTaylor (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), x ^ k / (k.factorial : ℝ)

end SimultaneousPolynomialApproximation
