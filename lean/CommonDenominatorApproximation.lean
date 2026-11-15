module
public import CommonDenominatorApproximationDefs

@[expose] public section

open Filter
open scoped Topology

namespace EPlusPiApproximation

/--
Exact common-denominator identity:
the form with coefficient q*r at x+y is the sum of the two original
integer forms, multiplied by the opposite denominators.
-/
theorem commonDenominator_form_identity
    (x y : ℝ) (q r : ℕ) (p s : ℤ) :
    signedIntegerLinearFormValue (x + y)
      (commonDenominatorCoefficient q r)
      (commonDenominatorConstant q r p s) =
      (r : ℝ) * signedIntegerLinearFormValue x (q : ℤ) (-p) +
        (q : ℝ) * signedIntegerLinearFormValue y (r : ℤ) (-s) := by
  simp only [signedIntegerLinearFormValue,
    commonDenominatorCoefficient, commonDenominatorConstant]
  push_cast
  ring

/--
The absolute value of the fused integer form is bounded by the
cross-multiplied sum of the two individual errors.
-/
theorem commonDenominator_form_abs_le
    (x y : ℝ) (q r : ℕ) (p s : ℤ) :
    |signedIntegerLinearFormValue (x + y)
      (commonDenominatorCoefficient q r)
      (commonDenominatorConstant q r p s)| ≤
      commonDenominatorScaledError x y q r p s := by
  rw [commonDenominator_form_identity]
  calc
    |(r : ℝ) * signedIntegerLinearFormValue x (q : ℤ) (-p) +
        (q : ℝ) * signedIntegerLinearFormValue y (r : ℤ) (-s)|
        ≤ |(r : ℝ) * signedIntegerLinearFormValue x (q : ℤ) (-p)| +
            |(q : ℝ) * signedIntegerLinearFormValue y (r : ℤ) (-s)| :=
          abs_add_le _ _
    _ = commonDenominatorScaledError x y q r p s := by
      simp [commonDenominatorScaledError, abs_mul]

/--
If the cross-multiplied error budget tends to zero, then the fused integer
linear forms themselves tend to zero.
-/
theorem commonDenominator_form_tendsto_zero
    {x y : ℝ} {q r : ℕ → ℕ} {p s : ℕ → ℤ}
    (hsmall : Tendsto
      (fun n : ℕ =>
        commonDenominatorScaledError x y (q n) (r n) (p n) (s n))
      atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        |signedIntegerLinearFormValue (x + y)
          (commonDenominatorCoefficient (q n) (r n))
          (commonDenominatorConstant (q n) (r n) (p n) (s n))|)
      atTop (𝓝 0) := by
  apply squeeze_zero
  · intro n
    exact abs_nonneg _
  · intro n
    exact commonDenominator_form_abs_le
      x y (q n) (r n) (p n) (s n)
  · exact hsmall

/--
A pair of separately constructed rational approximants proves irrationality
of their sum only when their *cross-multiplied* error budget tends to zero
and the resulting integer forms are eventually nonzero.
-/
theorem irrational_of_common_denominator_approximations
    {x y : ℝ} {q r : ℕ → ℕ} {p s : ℕ → ℤ}
    (hnz : ∀ᶠ n : ℕ in atTop,
      signedIntegerLinearFormValue (x + y)
        (commonDenominatorCoefficient (q n) (r n))
        (commonDenominatorConstant (q n) (r n) (p n) (s n)) ≠ 0)
    (hsmall : Tendsto
      (fun n : ℕ =>
        commonDenominatorScaledError x y (q n) (r n) (p n) (s n))
      atTop (𝓝 0)) :
    Irrational (x + y) :=
  irrational_of_tendsto_zero_signed_integer_linear_forms
    hnz (commonDenominator_form_tendsto_zero hsmall)

#print axioms irrational_of_common_denominator_approximations

end EPlusPiApproximation
