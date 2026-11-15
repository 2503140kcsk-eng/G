module
public import CommonDenominatorApproximationDefs
public import PolynomialApproximationDefs

@[expose] public section

namespace FactorialTaylorFusion

open EPlusPiApproximation
open SimultaneousPolynomialApproximation

/-- The endpoint denominator of the existing integer Taylor approximation to e:
    Q_n(1) = 2*n!. -/
def factorialTaylorDenominator (n : ℕ) : ℕ :=
  2 * n.factorial

/-- The endpoint numerator of the existing integer Taylor approximation to e:
    P_n(1) = 2*endpointTaylorValue(n). -/
def factorialTaylorNumerator (n : ℕ) : ℤ :=
  2 * (endpointTaylorValue n : ℤ)

/-- The absolute integer-linear-form error in the existing Taylor approximation to e. -/
noncomputable def factorialTaylorApproximationError (n : ℕ) : ℝ :=
  |signedIntegerLinearFormValue (Real.exp 1)
      (factorialTaylorDenominator n) (-factorialTaylorNumerator n)|

/-- The cross-weighted error obtained by fusing the existing Taylor approximation
    to e with any rational approximation s(n)/r(n) to pi. -/
noncomputable def factorialTaylorFusionError
    (r : ℕ → ℕ) (s : ℕ → ℤ) (n : ℕ) : ℝ :=
  commonDenominatorScaledError (Real.exp 1) Real.pi
    (factorialTaylorDenominator n) (r n)
    (factorialTaylorNumerator n) (s n)

end FactorialTaylorFusion
