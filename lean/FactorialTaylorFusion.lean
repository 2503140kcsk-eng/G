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


/-- The factorial dominates the seventh power of n. -/
theorem factorial_div_seventh_power_tendsto_atTop :
    Tendsto (fun n : ℕ => (n.factorial : ℝ) / (n + 1 : ℝ) ^ 7)
      atTop atTop := by
  have hlin : Tendsto
      (fun n : ℕ => (n : ℝ) / ((4 : ℝ) ^ 8 * (2 : ℝ) ^ 7))
      atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
      |>.atTop_div_const (by positivity)
  refine Filter.tendsto_atTop_mono' atTop ?_ hlin
  filter_upwards [eventually_ge_atTop 14] with n hn
  have hfacMul := Nat.factorial_mul_pow_le_factorial (m := n - 8) (n := 8)
  have hsucc : n - 8 + 1 = n - 7 := by omega
  have hadd : n - 8 + 8 = n := by omega
  have hfacMul' : (n - 8).factorial * (n - 7) ^ 8 ≤ n.factorial := by
    simpa [hsucc, hadd] using hfacMul
  have hhalf : n / 2 ≤ n - 7 := by omega
  have hfacHalf : (n / 2) ^ 8 ≤ n.factorial := by
    have hpos : 1 ≤ (n - 8).factorial :=
      Nat.succ_le_iff.mpr (Nat.factorial_pos _)
    calc
      (n / 2) ^ 8 ≤ (n - 7) ^ 8 := Nat.pow_le_pow_left hhalf 8
      _ = 1 * (n - 7) ^ 8 := by simp
      _ ≤ (n - 8).factorial * (n - 7) ^ 8 :=
        Nat.mul_le_mul_right _ hpos
      _ ≤ n.factorial := hfacMul'
  have hthird : n / 3 ≤ n / 2 := by omega
  have hfrac : n ≤ 4 * (n / 3) := by omega
  have hfacThird : (n / 3) ^ 8 ≤ n.factorial :=
    (Nat.pow_le_pow_left hthird 8).trans hfacHalf
  have hfacReal : ((n / 3 : ℕ) : ℝ) ^ 8 ≤ (n.factorial : ℝ) := by
    exact_mod_cast hfacThird
  have hlow : (n : ℝ) / 4 ≤ ((n / 3 : ℕ) : ℝ) := by
    have hfracReal : (n : ℝ) ≤ 4 * ((n / 3 : ℕ) : ℝ) := by
      exact_mod_cast hfrac
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).2 (by nlinarith)
  have hnum : ((n : ℝ) / 4) ^ 8 ≤ (n.factorial : ℝ) := by
    calc
      ((n : ℝ) / 4) ^ 8 ≤ ((n / 3 : ℕ) : ℝ) ^ 8 := by gcongr
      _ ≤ (n.factorial : ℝ) := hfacReal
  have hnR : (14 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden : (n + 1 : ℝ) ≤ 2 * (n : ℝ) := by
    nlinarith
  have hdenPow : (n + 1 : ℝ) ^ 7 ≤ (2 * (n : ℝ)) ^ 7 := by
    gcongr
  have hbase :
      (n : ℝ) / ((4 : ℝ) ^ 8 * (2 : ℝ) ^ 7) =
        ((n : ℝ) / 4) ^ 8 / (2 * (n : ℝ)) ^ 7 := by
    field_simp
  rw [hbase]
  exact
    (div_le_div_of_nonneg_right hnum (by positivity)).trans
      (div_le_div_of_nonneg_left (by positivity) (by positivity) hdenPow)

/--
A uniform Diophantine lower bound for the pi-side rational approximants prevents
the factorial Taylor family from producing a vanishing cross-weighted error.

The hypothesis is the explicit arithmetic input.  The published irrationality-
measure bound for pi implies such a constant c > 0; it is not silently imported
as an axiom or claimed to be proved in this module.
-/
theorem factorialTaylor_fusion_not_tendsto_zero_of_pi_lower_bound
    {r : ℕ → ℕ} {s : ℕ → ℤ} {c : ℝ}
    (hc : 0 < c)
    (hrpos : ∀ n, 0 < r n)
    (hpi : ∀ n,
      c / (r n : ℝ) ^ 7 ≤
        |(r n : ℝ) * Real.pi - (s n : ℝ)|) :
    ¬ Tendsto (factorialTaylorFusionError r s) atTop (𝓝 0) := by
  intro hsmall
  have hsub :=
    factorialTaylor_denominator_sublinear_of_fusion_tendsto_zero hsmall
  have hrBound : ∀ᶠ n : ℕ in atTop, r n ≤ n + 1 := by
    have hlt : ∀ᶠ n : ℕ in atTop,
        (r n : ℝ) / (n + 1 : ℝ) < 1 :=
      hsub.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hlt] with n hn
    have hden : 0 < (n + 1 : ℝ) := by positivity
    have hltR : (r n : ℝ) < (n + 1 : ℝ) := by
      simpa using (div_lt_iff₀ hden).mp hn
    exact_mod_cast hltR.le
  have hbase : Tendsto
      (fun n : ℕ =>
        (2 * c * (n.factorial : ℝ)) / (n + 1 : ℝ) ^ 7)
      atTop atTop := by
    have hfac := factorial_div_seventh_power_tendsto_atTop
    have hmul := hfac.atTop_mul_const (mul_pos (by norm_num : (0 : ℝ) < 2) hc)
    convert hmul using 1; ext n; ring
  have hF : Tendsto (factorialTaylorFusionError r s) atTop atTop :=
    Filter.tendsto_atTop_mono' atTop
      (by
        filter_upwards [hrBound] with n hn
        have hrR : (r n : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast hn
        have hrposR : 0 < (r n : ℝ) := Nat.cast_pos.mpr (hrpos n)
        have hpow : (r n : ℝ) ^ 7 ≤ (n + 1 : ℝ) ^ 7 := by gcongr
        have hpi' :
            c / (n + 1 : ℝ) ^ 7 ≤
              |(r n : ℝ) * Real.pi - (s n : ℝ)| :=
          (div_le_div_of_nonneg_left hc.le (pow_pos hrposR _) hpow).trans (hpi n)
        have hsecond :
            (2 * c * (n.factorial : ℝ)) / (n + 1 : ℝ) ^ 7 ≤
              (factorialTaylorDenominator n : ℝ) *
                |(r n : ℝ) * Real.pi - (s n : ℝ)| := by
          have hdenom : (factorialTaylorDenominator n : ℝ) =
              2 * (n.factorial : ℝ) := by
            simp [factorialTaylorDenominator]
          rw [hdenom]
          calc
            (2 * c * (n.factorial : ℝ)) / (n + 1 : ℝ) ^ 7 =
                (2 * (n.factorial : ℝ)) *
                  (c / (n + 1 : ℝ) ^ 7) := by ring
            _ ≤ (2 * (n.factorial : ℝ)) *
                  |(r n : ℝ) * Real.pi - (s n : ℝ)| :=
              mul_le_mul_of_nonneg_left hpi' (by positivity)
        have hpiInner :
            (r n : ℝ) * Real.pi - (s n : ℝ) =
              signedIntegerLinearFormValue Real.pi (r n) (-s n) := by
          simp [signedIntegerLinearFormValue]
          ring
        have hpiForm := congrArg abs hpiInner
        rw [hpiForm] at hsecond
        unfold factorialTaylorFusionError EPlusPiApproximation.commonDenominatorScaledError
        have hfirstNonneg :
            0 ≤ (r n : ℝ) *
              |signedIntegerLinearFormValue (Real.exp 1)
                (factorialTaylorDenominator n) (-factorialTaylorNumerator n)| := by
          positivity
        exact le_trans hsecond (le_add_of_nonneg_left hfirstNonneg))
      hbase
  have hsmallOne : ∀ᶠ n : ℕ in atTop,
      factorialTaylorFusionError r s n < 1 :=
    hsmall.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hlargeOne : ∀ᶠ n : ℕ in atTop,
      1 ≤ factorialTaylorFusionError r s n :=
    hF.eventually_ge_atTop 1
  obtain ⟨n, hnsmall, hnlarge⟩ := (hsmallOne.and hlargeOne).exists
  linarith

#print axioms factorialTaylor_linearForm_lower
#print axioms factorialTaylor_denominator_sublinear_of_fusion_tendsto_zero

end FactorialTaylorFusion
