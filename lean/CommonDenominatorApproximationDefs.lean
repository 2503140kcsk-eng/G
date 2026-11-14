module
public import ApproximationCriteria

@[expose] public section

/-!
# Common-denominator fusion data

Given rational approximants p/q to x and s/r to y, the product denominator
q*r produces an integer linear form in x+y.  The associated error bound
records the cross-multipliers explicitly; this is the denominator-loss term
that must tend to zero for the irrationality criterion to apply.
-/

namespace EPlusPiApproximation

/-- Product denominator for fusing denominators q and r. -/
def commonDenominatorCoefficient (q r : ℕ) : ℤ :=
  (q * r : ℕ)

/-- Integer constant obtained by cross-multiplying the two numerators. -/
def commonDenominatorConstant (q r : ℕ) (p s : ℤ) : ℤ :=
  -((r : ℤ) * p + (q : ℤ) * s)

/--
The cross-multiplied error budget for rational approximants p/q to x and
s/r to y.  The factors r and q are exactly the costs of clearing the
denominators in the opposite summands.
-/
def commonDenominatorScaledError
    (x y : ℝ) (q r : ℕ) (p s : ℤ) : ℝ :=
  (r : ℝ) *
      |signedIntegerLinearFormValue x (q : ℤ) (-p)| +
    (q : ℝ) *
      |signedIntegerLinearFormValue y (r : ℤ) (-s)|

end EPlusPiApproximation
