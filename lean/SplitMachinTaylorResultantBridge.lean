module
public import Mathlib
public import ResultantHeightBound
public import SplitMachinTaylorArithmetic

@[expose] public section

/-!
# Scalar Split–Machin Taylor sequence and the concrete resultant bridge

The coefficient sequence is that of
  S(z) = exp(z) + 16 atan(z/5) - 4 atan(z/239).

For each truncation degree N, a product of explicit coefficient
denominators clears the whole Taylor polynomial.  The endpoint partial sum
is therefore a rational number with an explicit integer numerator and
denominator.  This gives an actual rational polynomial P_N(X)=X-r_N and an
integerization of it, to which the general resultant-height theorem applies.

This file establishes integrality and the fixed-power algebraic lower bound.
It does NOT establish the required super-polynomial smallness after this
integerization; that is a separate Diophantine obligation.
-/

namespace EPlusPiApproximation

/-- The explicit denominator of the k-th coefficient of exp(z)+G(z). -/
def splitMachinScalarTaylorDenominator (k : ℕ) : ℕ :=
  k.factorial * splitMachinTaylorDenominator k

/-- The integer numerator of the k-th scalar Split–Machin coefficient. -/
def splitMachinScalarTaylorNumerator (k : ℕ) : ℤ :=
  if k % 2 = 1 then
    (k * 5 ^ k * 239 ^ k : ℤ) +
      (if k / 2 % 2 = 0 then 1 else -1) *
        (k.factorial : ℤ) *
          (16 * (239 : ℤ) ^ k - 4 * (5 : ℤ) ^ k)
  else 1

/-- Exact rational Taylor coefficient of S(z)=exp(z)+G(z). -/
def splitMachinScalarTaylorCoefficient (k : ℕ) : ℚ :=
  (splitMachinScalarTaylorNumerator k : ℚ) /
    (splitMachinScalarTaylorDenominator k : ℚ)

/-- Common denominator for all scalar Taylor coefficients up to degree N. -/
def splitMachinScalarTaylorCommonDenominator (N : ℕ) : ℕ :=
  ∏ k ∈ Finset.range (N + 1), splitMachinScalarTaylorDenominator k

theorem splitMachinScalarTaylorDenominator_pos (k : ℕ) :
    0 < splitMachinScalarTaylorDenominator k := by
  unfold splitMachinScalarTaylorDenominator
  exact Nat.mul_pos (Nat.factorial_pos k)
    (splitMachinTaylorDenominator_pos k)

theorem splitMachinScalarTaylorCommonDenominator_pos (N : ℕ) :
    0 < splitMachinScalarTaylorCommonDenominator N := by
  classical
  unfold splitMachinScalarTaylorCommonDenominator
  apply Finset.prod_pos
  intro k hk
  exact splitMachinScalarTaylorDenominator_pos k

theorem splitMachinScalarTaylorDenominator_dvd_common
    (N k : ℕ) (hk : k ≤ N) :
    splitMachinScalarTaylorDenominator k ∣
      splitMachinScalarTaylorCommonDenominator N := by
  classical
  unfold splitMachinScalarTaylorCommonDenominator
  exact Finset.dvd_prod_of_mem splitMachinScalarTaylorDenominator
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

/--
Every scalar Taylor coefficient up to degree N becomes an integer after
multiplication by the explicit product common denominator.
-/
theorem splitMachinScalarTaylor_commonDenominator_clears_coefficient
    (N k : ℕ) (hk : k ≤ N) :
    ∃ z : ℤ,
      (splitMachinScalarTaylorCommonDenominator N : ℚ) *
        splitMachinScalarTaylorCoefficient k = z := by
  classical
  let s := Finset.range (N + 1)
  let d := splitMachinScalarTaylorDenominator k
  let D := splitMachinScalarTaylorCommonDenominator N
  let E : ℕ := ∏ j ∈ s.erase k, splitMachinScalarTaylorDenominator j
  have hkMem : k ∈ s := Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
  have hprod : D = d * E := by
    dsimp [D, E, s, splitMachinScalarTaylorCommonDenominator]
    exact (Finset.mul_prod_erase (Finset.range (N + 1))
      splitMachinScalarTaylorDenominator hkMem).symm
  have hprodQ : (D : ℚ) = (d : ℚ) * (E : ℚ) := by
    exact_mod_cast hprod
  have hdq :
      (splitMachinScalarTaylorDenominator k : ℚ) ≠ 0 := by
    exact_mod_cast (splitMachinScalarTaylorDenominator_pos k).ne'
  refine ⟨(E : ℤ) * splitMachinScalarTaylorNumerator k, ?_⟩
  dsimp [splitMachinScalarTaylorCoefficient, d, D]
  rw [hprodQ]
  push_cast
  field_simp [hdq]
  ring

/-- Rational Taylor partial sum through degree N, evaluated at z=1. -/
def splitMachinScalarTaylorPartialSum (N : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (N + 1), splitMachinScalarTaylorCoefficient k

/-- The common denominator makes the full Taylor partial sum an integer. -/
theorem splitMachinScalarTaylorPartialSum_integerized (N : ℕ) :
    ∃ z : ℤ,
      (splitMachinScalarTaylorCommonDenominator N : ℚ) *
        splitMachinScalarTaylorPartialSum N = z := by
  classical
  let s := Finset.range (N + 1)
  have hterm : ∀ k ∈ s,
      ∃ z : ℤ,
        (splitMachinScalarTaylorCommonDenominator N : ℚ) *
          splitMachinScalarTaylorCoefficient k = z := by
    intro k hk
    exact splitMachinScalarTaylor_commonDenominator_clears_coefficient
      N k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  let z : ℕ → ℤ := fun k =>
    if hk : k ∈ s then Classical.choose (hterm k hk) else 0
  have hz (k : ℕ) (hk : k ∈ s) :
      (splitMachinScalarTaylorCommonDenominator N : ℚ) *
        splitMachinScalarTaylorCoefficient k = (z k : ℚ) := by
    dsimp [z]
    rw [dite_eq_left hk]
    exact_mod_cast Classical.choose_spec (hterm k hk)
  refine ⟨∑ k ∈ s, z k, ?_⟩
  calc
    (splitMachinScalarTaylorCommonDenominator N : ℚ) *
        splitMachinScalarTaylorPartialSum N
        = ∑ k ∈ s,
            (splitMachinScalarTaylorCommonDenominator N : ℚ) *
              splitMachinScalarTaylorCoefficient k := by
              simp [splitMachinScalarTaylorPartialSum, s, Finset.mul_sum]
    _ = ∑ k ∈ s, (z k : ℚ) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact hz k hk
    _ = ((∑ k ∈ s, z k : ℤ) : ℚ) := by simp

/-- Canonical chosen integer numerator of the Taylor partial sum. -/
noncomputable def splitMachinScalarTaylorPartialSumInteger (N : ℕ) : ℤ :=
  Classical.choose (splitMachinScalarTaylorPartialSum_integerized N)

theorem splitMachinScalarTaylorPartialSumInteger_spec (N : ℕ) :
    (splitMachinScalarTaylorCommonDenominator N : ℚ) *
      splitMachinScalarTaylorPartialSum N =
        (splitMachinScalarTaylorPartialSumInteger N : ℚ) :=
  Classical.choose_spec (splitMachinScalarTaylorPartialSum_integerized N)

/-- The rational linear polynomial X-r_N, where r_N is the scalar endpoint
Taylor truncation for e+pi. -/
noncomputable def splitMachinScalarTaylorApproxPolynomial (N : ℕ) : Polynomial ℚ :=
  Polynomial.X - Polynomial.C (splitMachinScalarTaylorPartialSum N)

/-- Integer numerator polynomial for X-r_N after denominator clearing. -/
noncomputable def splitMachinScalarTaylorIntegerNumeratorPolynomial (N : ℕ) :
    Polynomial ℤ :=
  Polynomial.C (splitMachinScalarTaylorCommonDenominator N : ℤ) * Polynomial.X -
    Polynomial.C (splitMachinScalarTaylorPartialSumInteger N)

theorem splitMachinScalarTaylorIntegerNumerator_map_eq (N : ℕ) :
    (splitMachinScalarTaylorIntegerNumeratorPolynomial N).map
        (algebraMap ℤ ℚ) =
      Polynomial.C (splitMachinScalarTaylorCommonDenominator N : ℚ) *
        splitMachinScalarTaylorApproxPolynomial N := by
  classical
  simp only [splitMachinScalarTaylorIntegerNumeratorPolynomial,
    Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    splitMachinScalarTaylorApproxPolynomial]
  have hDcast :
      (algebraMap ℤ ℚ)
        (splitMachinScalarTaylorCommonDenominator N : ℤ) =
          (splitMachinScalarTaylorCommonDenominator N : ℚ) := by
    norm_cast
  have hAcast :
      (algebraMap ℤ ℚ) (splitMachinScalarTaylorPartialSumInteger N) =
        (splitMachinScalarTaylorPartialSumInteger N : ℚ) := by
    norm_cast
  rw [hDcast, hAcast]
  have hA :
      (splitMachinScalarTaylorPartialSumInteger N : ℚ) =
        (splitMachinScalarTaylorCommonDenominator N : ℚ) *
          splitMachinScalarTaylorPartialSum N :=
    (splitMachinScalarTaylorPartialSumInteger_spec N).symm
  rw [hA]
  ring

/-- An actual integerized polynomial sequence for the scalar truncations. -/
noncomputable def splitMachinScalarTaylorIntegerizedSequence :
    IntegerizedPolynomialSequence splitMachinScalarTaylorApproxPolynomial where
  numerator := splitMachinScalarTaylorIntegerNumeratorPolynomial
  denominator := splitMachinScalarTaylorCommonDenominator
  denominator_pos := splitMachinScalarTaylorCommonDenominator_pos
  map_eq := splitMachinScalarTaylorIntegerNumerator_map_eq

/-- A concrete height large enough for the numerator coefficients,
denominator, and degree of the scalar Taylor sequence. -/
noncomputable def splitMachinScalarTaylorHeight (N : ℕ) : ℕ :=
  max (Int.natAbs (splitMachinScalarTaylorPartialSumInteger N))
    (max (splitMachinScalarTaylorCommonDenominator N)
      (2 ^ (splitMachinScalarTaylorIntegerNumeratorPolynomial N).natDegree)) + 2

/--
The coefficient height of the integerized scalar Taylor polynomial is
bounded by the explicit H_N above.
-/
private lemma norm_complex_intCast_eq_natAbs (z : ℤ) :
    ‖(z : ℂ)‖ = (Int.natAbs z : ℝ) := by
  cases z with
  | ofNat n => simp
  | negSucc n => simp [Int.natAbs]

theorem splitMachinScalarTaylor_coefficient_height_bound (N : ℕ) :
    ∀ i,
      ‖((splitMachinScalarTaylorIntegerizedSequence.numerator N).map
        (algebraMap ℤ ℂ)).coeff i‖ ≤
          (splitMachinScalarTaylorHeight N : ℝ) := by
  intro i
  let a := splitMachinScalarTaylorPartialSumInteger N
  let D := splitMachinScalarTaylorCommonDenominator N
  have hDcast : (algebraMap ℤ ℂ) (D : ℤ) = (D : ℂ) := by
    norm_cast
  have hAcast : (algebraMap ℤ ℂ) (-a) = (-(a : ℂ)) := by
    simp
  have hconst : Polynomial.coeff (Polynomial.C (-(a : ℂ)) : Polynomial ℂ) i =
      if i = 0 then -(a : ℂ) else 0 := by
    simpa using (Polynomial.coeff_C_mul_X_pow (-(a : ℂ)) 0 i)
  have hlinear : Polynomial.coeff
      (Polynomial.C (D : ℂ) * Polynomial.X : Polynomial ℂ) i =
      if i = 1 then (D : ℂ) else 0 := by
    exact Polynomial.coeff_C_mul_X (D : ℂ) i
  have hformula :
      ((splitMachinScalarTaylorIntegerizedSequence.numerator N).map
        (algebraMap ℤ ℂ)).coeff i =
          (if i = 0 then (-(a : ℂ))
           else if i = 1 then (D : ℂ) else 0) := by
    simp only [splitMachinScalarTaylorIntegerizedSequence,
      splitMachinScalarTaylorIntegerNumeratorPolynomial,
      Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_X, Polynomial.coeff_sub]
    rw [hDcast, hAcast, hlinear, hconst]
    by_cases hi0 : i = 0
    · subst i
      simp
    · by_cases hi1 : i = 1
      · subst i
        simp [hi0]
      · simp [hi0, hi1]
  let M := max (Int.natAbs a) (max D
    (2 ^ (splitMachinScalarTaylorIntegerNumeratorPolynomial N).natDegree))
  have hA : Int.natAbs a ≤ splitMachinScalarTaylorHeight N := by
    dsimp [splitMachinScalarTaylorHeight]
    exact Nat.le_trans (le_max_left _ _) (Nat.le_add_right M 2)
  have hD : D ≤ splitMachinScalarTaylorHeight N := by
    dsimp [splitMachinScalarTaylorHeight]
    have hDM : D ≤ M := by
      dsimp [M]
      exact Nat.le_trans (le_max_left D _) (le_max_right _ _)
    exact Nat.le_trans hDM (Nat.le_add_right M 2)
  rw [hformula]
  split_ifs with hi0 hi1
  · rw [norm_neg, norm_complex_intCast_eq_natAbs]
    exact_mod_cast hA
  · have hnormD : ‖(D : ℂ)‖ = (D : ℝ) := by norm_cast
    simpa [hnormD] using
      (show (D : ℝ) ≤ (splitMachinScalarTaylorHeight N : ℝ) by exact_mod_cast hD)
  · simp

/-- The chosen height is at least two. -/
theorem splitMachinScalarTaylorHeight_ge_two (N : ℕ) :
    2 ≤ splitMachinScalarTaylorHeight N := by
  dsimp [splitMachinScalarTaylorHeight]
  omega

/-- The same height controls the integerized denominator. -/
theorem splitMachinScalarTaylor_denominator_height_bound (N : ℕ) :
    (splitMachinScalarTaylorIntegerizedSequence.denominator N) ≤
      splitMachinScalarTaylorHeight N := by
  dsimp [splitMachinScalarTaylorIntegerizedSequence,
    splitMachinScalarTaylorHeight]
  exact Nat.le_trans
    (Nat.le_trans (le_max_left _ _) (le_max_right _ _))
    (Nat.le_add_right _ _)

/-- The degree contribution is controlled by the same height. -/
theorem splitMachinScalarTaylor_degree_height_bound (N : ℕ) :
    2 ^ (splitMachinScalarTaylorIntegerizedSequence.numerator N).natDegree ≤
      splitMachinScalarTaylorHeight N := by
  dsimp [splitMachinScalarTaylorIntegerizedSequence,
    splitMachinScalarTaylorHeight]
  exact Nat.le_trans
    (Nat.le_trans (le_max_right _ _) (le_max_right _ _))
    (Nat.le_add_right _ _)

/--
For every algebraic candidate x, the actual scalar Split–Machin Taylor
polynomial sequence satisfies the concrete resultant Liouville lower bound.
The second channel is taken to be the same sequence; the paired smallness
condition is deliberately NOT asserted here.
-/
theorem splitMachinScalarTaylor_has_concrete_hLiouville
    {x : ℝ} :
    IsAlgebraic ℚ x →
      ∃ d : ℕ,
        (∀ᶠ n : ℕ in atTop,
          evalReal x (splitMachinScalarTaylorApproxPolynomial n) ≠ 0 →
            1 / (splitMachinScalarTaylorHeight n : ℝ) ^ d ≤
              |evalReal x (splitMachinScalarTaylorApproxPolynomial n)|) ∧
        (∀ᶠ n : ℕ in atTop,
          evalReal x (splitMachinScalarTaylorApproxPolynomial n) ≠ 0 →
            1 / (splitMachinScalarTaylorHeight n : ℝ) ^ d ≤
              |evalReal x (splitMachinScalarTaylorApproxPolynomial n)|) := by
  refine @hLiouville_of_integerized_height_degree_bounds
    x splitMachinScalarTaylorApproxPolynomial
      splitMachinScalarTaylorApproxPolynomial splitMachinScalarTaylorHeight
      1 1 1 splitMachinScalarTaylorIntegerizedSequence
      splitMachinScalarTaylorIntegerizedSequence ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall splitMachinScalarTaylorHeight_ge_two
  · filter_upwards [] with n
    intro i
    simpa only [pow_one] using splitMachinScalarTaylor_coefficient_height_bound n i
  · filter_upwards [] with n
    intro i
    simpa only [pow_one] using splitMachinScalarTaylor_coefficient_height_bound n i
  · filter_upwards [] with n
    simpa only [pow_one] using splitMachinScalarTaylor_degree_height_bound n
  · filter_upwards [] with n
    simpa only [pow_one] using splitMachinScalarTaylor_degree_height_bound n
  · filter_upwards [] with n
    simpa only [pow_one] using splitMachinScalarTaylor_denominator_height_bound n
  · filter_upwards [] with n
    simpa only [pow_one] using splitMachinScalarTaylor_denominator_height_bound n

#print axioms splitMachinScalarTaylor_has_concrete_hLiouville
#print axioms splitMachinScalarTaylorIntegerNumerator_map_eq

end EPlusPiApproximation
