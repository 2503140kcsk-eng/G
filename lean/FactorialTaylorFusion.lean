module
public import FactorialTaylorFusionDefs
public import SimultaneousPolynomialApproximation
public import Mathlib.Analysis.Complex.Exponential

@[expose] public section

open Filter
open scoped Topology

namespace FactorialTaylorFusion

open EPlusPiApproximation
open SimultaneousPolynomialApproximation

/-- The positive exponential Taylor remainder is at least its first omitted term. -/
theorem expTaylor_remainder_lower (n : ℕ) :
    (1 : ℝ) / ((n + 1).factorial : ℝ) ≤
      Real.exp 1 - expTaylor n 1 := by
  have hsum := Real.sum_le_exp_of_nonneg (x := (1 : ℝ)) (by norm_num) (n + 2)
  have hsum' :
      expTaylor n 1 + (1 : ℝ) / ((n + 1).factorial : ℝ) ≤ Real.exp 1 := by
    simpa [expTaylor, Finset.sum_range_succ] using hsum
  linarith

/-- Evaluating the integer Taylor polynomial at one gives its endpoint integer. -/
theorem evalReal_taylorIntPoly_one (n : ℕ) :
    evalReal (taylorIntPoly n) 1 = (endpointTaylorValue n : ℝ) := by
  simp [evalReal, Polynomial.eval₂_at_one, taylorIntPoly_eval_one]

/-- The endpoint numerator of the integer Taylor family is exactly the stated integer. -/
theorem factorialTaylorNumerator_eval_one (n : ℕ) :
    (factorialTaylorNumerator n : ℝ) =
      evalReal (numerator n) 1 := by
  have hTaylor :
      (endpointTaylorValue n : ℝ) =
        (n.factorial : ℝ) * expTaylor n 1 := by
    have h := taylorIntPoly_eval_real n (1 : ℝ)
    rw [evalReal_taylorIntPoly_one] at h
    exact h
  calc
    (factorialTaylorNumerator n : ℝ) =
        2 * (endpointTaylorValue n : ℝ) := by
          simp [factorialTaylorNumerator]
    _ = 2 * (n.factorial : ℝ) * expTaylor n 1 := by rw [hTaylor]; ring
    _ = evalReal (numerator n) 1 := by
      rw [evalReal_numerator]
      norm_num
      ring

/-- The endpoint denominator of the integer Taylor family is exactly 2*n!. -/
theorem factorialTaylorDenominator_eval_one (n : ℕ) :
    (factorialTaylorDenominator n : ℝ) =
      evalReal (denominator n) 1 := by
  calc
    (factorialTaylorDenominator n : ℝ) = 2 * (n.factorial : ℝ) := by
      simp [factorialTaylorDenominator]
    _ = evalReal (denominator n) 1 := by
      rw [evalReal_denominator]
      norm_num
      ring

/-- Exact evaluation of the factorial Taylor integer-linear form at e. -/
theorem factorialTaylor_linearForm_identity (n : ℕ) :
    (factorialTaylorDenominator n : ℝ) * Real.exp 1 -
      (factorialTaylorNumerator n : ℝ) =
        2 * (n.factorial : ℝ) * (Real.exp 1 - expTaylor n 1) := by
  calc
    (factorialTaylorDenominator n : ℝ) * Real.exp 1 -
        (factorialTaylorNumerator n : ℝ) =
      evalReal (denominator n) 1 * Real.exp 1 -
        evalReal (numerator n) 1 := by
          rw [factorialTaylorDenominator_eval_one,
            factorialTaylorNumerator_eval_one]
    _ = 2 * (n.factorial : ℝ) * (Real.exp 1 - expTaylor n 1) := by
      rw [evalReal_denominator, evalReal_numerator]
      norm_num
      ring

/-- The existing factorial Taylor integer-linear form is positive. -/
theorem factorialTaylor_linearForm_pos (n : ℕ) :
    0 < (factorialTaylorDenominator n : ℝ) * Real.exp 1 -
      (factorialTaylorNumerator n : ℝ) := by
  rw [factorialTaylor_linearForm_identity]
  have htail := expTaylor_remainder_lower n
  have hrem : 0 < Real.exp 1 - expTaylor n 1 :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) <
      (1 : ℝ) / ((n + 1).factorial : ℝ)) htail
  positivity

/--
The factorial Taylor integer-linear form cannot be smaller than 2/(n+1).
This complements the existing upper bound 4/(n+1).
-/
theorem factorialTaylor_linearForm_lower (n : ℕ) :
    (2 : ℝ) / (n + 1 : ℝ) ≤
      (factorialTaylorDenominator n : ℝ) * Real.exp 1 -
        (factorialTaylorNumerator n : ℝ) := by
  rw [factorialTaylor_linearForm_identity]
  have htail := expTaylor_remainder_lower n
  have hfac :
      (2 : ℝ) / (n + 1 : ℝ) =
        (2 * (n.factorial : ℝ)) / ((n + 1).factorial : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    field_simp
  rw [hfac]
  have hmul := mul_le_mul_of_nonneg_left htail (by positivity :
    (0 : ℝ) ≤ 2 * (n.factorial : ℝ))
  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hmul

/-- The absolute approximation error equals the positive endpoint linear form. -/
theorem factorialTaylor_absError_eq (n : ℕ) :
    factorialTaylorApproximationError n =
      (factorialTaylorDenominator n : ℝ) * Real.exp 1 -
        (factorialTaylorNumerator n : ℝ) := by
  unfold factorialTaylorApproximationError signedIntegerLinearFormValue
  push_cast
  rw [← sub_eq_add_neg]
  exact abs_of_pos (factorialTaylor_linearForm_pos n)

/-- The first, e-side term is bounded by the fused cross-weighted error. -/
theorem factorialTaylor_firstTerm_le_fusion
    (r : ℕ → ℕ) (s : ℕ → ℤ) (n : ℕ) :
    (r n : ℝ) * factorialTaylorApproximationError n ≤
      factorialTaylorFusionError r s n := by
  unfold factorialTaylorFusionError factorialTaylorApproximationError
    commonDenominatorScaledError
  exact le_add_of_nonneg_right
    (mul_nonneg (by positivity) (abs_nonneg _))

/--
If the fused common-denominator error tends to zero, then the denominator r(n)
used for the pi-approximation must satisfy r(n)/(n+1) -> 0.

This is a necessary condition specific to the repository's factorial Taylor
approximants for e.
-/
theorem factorialTaylor_denominator_sublinear_of_fusion_tendsto_zero
    {r : ℕ → ℕ} {s : ℕ → ℤ}
    (hsmall : Tendsto (factorialTaylorFusionError r s) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (r n : ℝ) / (n + 1 : ℝ)) atTop (𝓝 0) := by
  have hfirst :
      Tendsto (fun n : ℕ => (r n : ℝ) * factorialTaylorApproximationError n)
        atTop (𝓝 0) := by
    apply squeeze_zero
    · intro n
      unfold factorialTaylorApproximationError
      positivity
    · intro n
      exact factorialTaylor_firstTerm_le_fusion r s n
    · exact hsmall
  apply squeeze_zero
  · intro n
    positivity
  · intro n
    have hlow := factorialTaylor_linearForm_lower n
    have hr : 0 ≤ (r n : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hlow hr
    have herror :
        factorialTaylorApproximationError n =
          (factorialTaylorDenominator n : ℝ) * Real.exp 1 -
            (factorialTaylorNumerator n : ℝ) :=
      factorialTaylor_absError_eq n
    calc
      (r n : ℝ) / (n + 1 : ℝ) =
          ((r n : ℝ) * (2 / (n + 1 : ℝ))) / 2 := by
            field_simp
      _ ≤ ((r n : ℝ) * factorialTaylorApproximationError n) / 2 := by
        rw [herror]
        exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2
          (by simpa [mul_comm] using hmul)
  · simpa [div_eq_mul_inv] using hfirst.mul_const (1 / 2 : ℝ)

#print axioms factorialTaylor_linearForm_lower
#print axioms factorialTaylor_denominator_sublinear_of_fusion_tendsto_zero

end FactorialTaylorFusion
