module
public import PolynomialApproximationDefs
public import Mathlib.Analysis.Complex.Exponential

@[expose] public section

open Filter
open scoped Topology

namespace SimultaneousPolynomialApproximation

/-- Clearing the factorial denominator in one Taylor coefficient gives an integer. -/
lemma cast_taylor_coefficient (n k : ℕ) (hk : k ≤ n) :
    ((n.choose k * (n - k).factorial : ℕ) : ℝ) =
      (n.factorial : ℝ) / (k.factorial : ℝ) := by
  have hNat := Nat.choose_mul_factorial_mul_factorial hk
  have hReal :
      (n.choose k : ℝ) * (k.factorial : ℝ) *
          ((n - k).factorial : ℝ) = (n.factorial : ℝ) := by
    exact_mod_cast hNat
  have hkfac : (k.factorial : ℝ) ≠ 0 := by positivity
  calc
    ((n.choose k * (n - k).factorial : ℕ) : ℝ)
        = (n.choose k : ℝ) * ((n - k).factorial : ℝ) := by norm_cast
    _ = (n.factorial : ℝ) / (k.factorial : ℝ) := by
      field_simp
      nlinarith [hReal]

/-- The integer polynomial evaluates to n! times the degree-n Taylor sum. -/
theorem taylorIntPoly_eval_real (n : ℕ) (x : ℝ) :
    evalReal (taylorIntPoly n) x = (n.factorial : ℝ) * expTaylor n x := by
  classical
  simp only [evalReal, taylorIntPoly, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Int.cast_ofNat]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := by
    simp only [Finset.mem_range] at hk
    omega
  have hcoeff := cast_taylor_coefficient n k hk'
  change ((n.choose k * (n - k).factorial : ℕ) : ℝ) * x ^ k =
    (n.factorial : ℝ) * (x ^ k / (k.factorial : ℝ))
  rw [hcoeff]
  ring

/-- At zero, the constant coefficient of the integer Taylor polynomial is n!. -/
theorem taylorIntPoly_eval_zero (n : ℕ) :
    (taylorIntPoly n).eval 0 = (n.factorial : ℤ) := by
  classical
  simp [taylorIntPoly]

/-- At one, the integer Taylor polynomial has the explicitly defined endpoint sum. -/
theorem taylorIntPoly_eval_one (n : ℕ) :
    (taylorIntPoly n).eval 1 = (endpointTaylorValue n : ℤ) := by
  classical
  simp [taylorIntPoly, endpointTaylorValue]

/-- The endpoint sum contains its k=0 and k=1 terms, each equal to n!. -/
theorem endpointTaylorValue_lower (n : ℕ) (hn : 1 ≤ n) :
    2 * n.factorial ≤ endpointTaylorValue n := by
  classical
  let s : Finset ℕ := Finset.range (n + 1)
  let f : ℕ → ℕ := fun k => n.choose k * (n - k).factorial
  have h0 : 0 ∈ s := by simp [s]
  have h1 : 1 ∈ s := by simp [s]; omega
  have h1erase : 1 ∈ s.erase 0 := by
    simp only [Finset.mem_erase]
    exact ⟨by decide, h1⟩
  have h0val : f 0 = n.factorial := by simp [f]
  have h1val : f 1 = n.factorial := by
    simpa [f, Nat.factorial_one, Nat.mul_assoc] using
      (Nat.choose_mul_factorial_mul_factorial (n := n) (k := 1) (by omega))
  have hrest : n.factorial ≤ ∑ k ∈ s.erase 0, f k := by
    calc
      n.factorial = f 1 := h1val.symm
      _ ≤ ∑ k ∈ s.erase 0, f k :=
        Finset.single_le_sum (fun k hk => Nat.zero_le _) h1erase
  have hdecomp :
      (∑ k ∈ s.erase 0, f k) + f 0 = ∑ k ∈ s, f k :=
    Finset.sum_erase_add s f h0
  calc
    2 * n.factorial = n.factorial + n.factorial := by omega
    _ = f 1 + f 0 := by rw [h1val, h0val]
    _ ≤ (∑ k ∈ s.erase 0, f k) + f 0 :=
      add_le_add_right hrest _
    _ = endpointTaylorValue n := by
      rw [hdecomp]
      simp [endpointTaylorValue, s, f]

/-- The determinant is the explicit nonzero integer
    2*n!*(endpointTaylorValue n - n!). -/
theorem endpointMatrix_det_formula (n : ℕ) :
    (endpointMatrix n).det =
      2 * (n.factorial : ℤ) *
        ((endpointTaylorValue n : ℤ) - (n.factorial : ℤ)) := by
  rw [Matrix.det_fin_two]
  simp [endpointMatrix, denominator, numerator,
    taylorIntPoly_eval_zero, taylorIntPoly_eval_one]
  ring

/-- The endpoint-value matrix is nonsingular for every n ≥ 1. -/
theorem endpointMatrix_det_ne_zero (n : ℕ) (hn : 1 ≤ n) :
    (endpointMatrix n).det ≠ 0 := by
  have hU : n.factorial < endpointTaylorValue n := by
    have h := endpointTaylorValue_lower n hn
    have hp : 0 < n.factorial := Nat.factorial_pos n
    omega
  have hfac : (n.factorial : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos n).ne'
  have hdiff :
      (endpointTaylorValue n : ℤ) - (n.factorial : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hU)
  rw [endpointMatrix_det_formula]
  exact mul_ne_zero (mul_ne_zero (by norm_num) hfac) hdiff

/-- The denominator evaluates to n! (1+x^2). -/
theorem evalReal_denominator (n : ℕ) (x : ℝ) :
    evalReal (denominator n) x =
      (n.factorial : ℝ) * (1 + x ^ 2) := by
  simp [evalReal, denominator, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_add,
    Polynomial.eval₂_pow, Polynomial.eval₂_X]

/-- The numerator evaluates to (1+x^2) times the exponential Taylor numerator. -/
theorem evalReal_numerator (n : ℕ) (x : ℝ) :
    evalReal (numerator n) x =
      (1 + x ^ 2) * ((n.factorial : ℝ) * expTaylor n x) := by
  simp [evalReal, numerator, Polynomial.eval₂_mul,
    Polynomial.eval₂_add, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, taylorIntPoly_eval_real]

/-- The reciprocal function is represented exactly, with zero error on all ℝ. -/
theorem reciprocal_exact (n : ℕ) (x : ℝ) :
    evalReal (denominator n) x * (1 + x ^ 2)⁻¹ =
      evalReal (reciprocalNumerator n) x := by
  rw [evalReal_denominator]
  simp [evalReal, reciprocalNumerator]
  have hpos : 0 < 1 + x ^ 2 := by positivity
  field_simp

/-- The degree-n Taylor error for exp is bounded uniformly on [-1,1]. -/
theorem expTaylor_error (n : ℕ) (x : ℝ)
    (hx : x ∈ Set.Icc (-1) 1) :
    |Real.exp x - expTaylor n x| ≤
      2 / ((n + 1).factorial : ℝ) := by
  have hxabs : |x| ≤ 1 :=
    abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hxnorm : ‖(x : ℂ)‖ ≤ 1 := by simpa using hxabs
  have hdenNat : 2 ≤ (n + 1).succ := by omega
  have hden : (2 : ℝ) ≤ ((n + 1).succ : ℝ) := by exact_mod_cast hdenNat
  have hcond :
      ‖(x : ℂ)‖ / ((n + 1).succ : ℝ) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((n + 1).succ : ℝ))).2
    nlinarith
  have hcomplex := Complex.exp_bound' (x := (x : ℂ)) (n := n + 1) hcond
  have hsum :
      ((expTaylor n x : ℝ) : ℂ) =
        ∑ k ∈ Finset.range (n + 1), (x : ℂ) ^ k / (k.factorial : ℂ) := by
    simp [expTaylor]
  have hcoerce :
      ((Real.exp x - expTaylor n x : ℝ) : ℂ) =
        Complex.exp (x : ℂ) -
          ∑ k ∈ Finset.range (n + 1), (x : ℂ) ^ k / (k.factorial : ℂ) := by
    simp [Complex.ofReal_exp, hsum]
  calc
    |Real.exp x - expTaylor n x|
        = ‖((Real.exp x - expTaylor n x : ℝ) : ℂ)‖ := by simp
    _ = ‖Complex.exp (x : ℂ) -
          ∑ k ∈ Finset.range (n + 1), (x : ℂ) ^ k / (k.factorial : ℂ)‖ := by
        rw [hcoerce]
    _ ≤ ‖(x : ℂ)‖ ^ (n + 1) / ((n + 1).factorial : ℝ) * 2 := hcomplex
    _ ≤ 1 / ((n + 1).factorial : ℝ) * 2 := by
      gcongr
      exact pow_le_one₀ (norm_nonneg _) hxnorm
    _ = 2 / ((n + 1).factorial : ℝ) := by ring

/-- Strict uniform error estimate for the exponential component:
    sup_{|x|≤1} |Q_n(x)e^x-P_n(x)| ≤ 4/(n+1). -/
theorem exp_approx_uniform (n : ℕ) (x : ℝ)
    (hx : x ∈ Set.Icc (-1) 1) :
    |evalReal (denominator n) x * Real.exp x -
      evalReal (numerator n) x| ≤ 4 / (n + 1 : ℝ) := by
  have hidentity :
      evalReal (denominator n) x * Real.exp x -
        evalReal (numerator n) x =
      (n.factorial : ℝ) * (1 + x ^ 2) *
        (Real.exp x - expTaylor n x) := by
    rw [evalReal_denominator, evalReal_numerator]
    ring
  have hscale : 0 ≤ (n.factorial : ℝ) * (1 + x ^ 2) := by positivity
  have hx2 : 1 + x ^ 2 ≤ 2 := by nlinarith [hx.1, hx.2]
  rw [hidentity, abs_mul, abs_of_nonneg hscale]
  calc
    (n.factorial : ℝ) * (1 + x ^ 2) *
        |Real.exp x - expTaylor n x|
        ≤ (n.factorial : ℝ) * 2 *
            (2 / ((n + 1).factorial : ℝ)) := by
          gcongr
          exact expTaylor_error n x hx
    _ = 4 / (n + 1 : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      have hnpos : (0 : ℝ) < (n + 1 : ℝ) := by positivity
      field_simp [hnpos.ne']
      ring

/-- The explicit rate 4/(n+1) tends to zero in the epsilon-N sense. -/
theorem uniform_error_vanishes :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (4 : ℝ) / (n + 1 : ℝ) < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (4 / ε)
  refine ⟨N, fun n hn => ?_⟩
  have hnR : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden : 4 / ε < (n + 1 : ℝ) := by
    have hN' : 4 / ε < (N : ℝ) := hN
    linarith
  have hmul : 4 < (n + 1 : ℝ) * ε :=
    (div_lt_iff₀ hε).mp hden
  exact (div_lt_iff₀ (by positivity : (0 : ℝ) < (n + 1 : ℝ))).2 (by
    simpa [mul_comm] using hmul)

/-- Complete simultaneous approximation certificate:
    integer coefficients by construction, nonzero integer endpoint determinant,
    exact reciprocal approximation, and a vanishing uniform exponential error. -/
theorem simultaneous_approximation_certificate (n : ℕ) (hn : 1 ≤ n) :
    (endpointMatrix n).det ≠ 0 ∧
    (∀ x ∈ Set.Icc (-1) 1,
      |evalReal (denominator n) x * Real.exp x -
        evalReal (numerator n) x| ≤ 4 / (n + 1 : ℝ)) ∧
    (∀ x : ℝ,
      evalReal (denominator n) x * (1 + x ^ 2)⁻¹ =
        evalReal (reciprocalNumerator n) x) ∧
    (∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
        (4 : ℝ) / (m + 1 : ℝ) < ε) := by
  refine ⟨endpointMatrix_det_ne_zero n hn, ?_, ?_, uniform_error_vanishes⟩
  · intro x hx
    exact exp_approx_uniform n x hx
  · intro x
    exact reciprocal_exact n x

#print axioms simultaneous_approximation_certificate

end SimultaneousPolynomialApproximation
