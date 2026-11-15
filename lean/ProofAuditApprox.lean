module
public import SimultaneousPolynomialApproximation

@[expose] public section

namespace ProofAudit

/-- Audited public contract for the explicit simultaneous integer-polynomial family. -/
theorem simultaneous_polynomial_approximation_certificate
    (n : ℕ) (hn : 1 ≤ n) :
    (SimultaneousPolynomialApproximation.endpointMatrix n).det ≠ 0 ∧
    (∀ x ∈ Set.Icc (-1) 1,
      |SimultaneousPolynomialApproximation.evalReal
          (SimultaneousPolynomialApproximation.denominator n) x * Real.exp x -
        SimultaneousPolynomialApproximation.evalReal
          (SimultaneousPolynomialApproximation.numerator n) x|
          ≤ 4 / (n + 1 : ℝ)) ∧
    (∀ x : ℝ,
      SimultaneousPolynomialApproximation.evalReal
          (SimultaneousPolynomialApproximation.denominator n) x *
            (1 + x ^ 2)⁻¹ =
        SimultaneousPolynomialApproximation.evalReal
          (SimultaneousPolynomialApproximation.reciprocalNumerator n) x) ∧
    (∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
        (4 : ℝ) / (m + 1 : ℝ) < ε) :=
  SimultaneousPolynomialApproximation.simultaneous_approximation_certificate n hn

#print axioms simultaneous_polynomial_approximation_certificate

end ProofAudit
