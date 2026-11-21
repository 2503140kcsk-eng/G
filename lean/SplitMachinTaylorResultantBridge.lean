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
  choose z hz using hterm
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
def splitMachinScalarTaylorApproxPolynomial (N : ℕ) : Polynomial ℚ :=
  Polynomial.X - Polynomial.C (splitMachinScalarTaylorPartialSum N)

/-- Integer numerator polynomial for X-r_N after denominator clearing. -/
def splitMachinScalarTaylorIntegerNumeratorPolynomial (N : ℕ) :
    Polynomial ℤ :=
  Polynomial.C (-(splitMachinScalarTaylorPartialSumInteger N)) +
    Polynomial.monomial 1 (splitMachinScalarTaylorCommonDenominator N : ℤ)

theorem splitMachinScalarTaylorIntegerNumerator_map_eq (N : ℕ) :
    (splitMachinScalarTaylorIntegerNumeratorPolynomial N).map
        (algebraMap ℤ ℚ) =
      Polynomial.C (splitMachinScalarTaylorCommonDenominator N : ℚ) *
        splitMachinScalarTaylorApproxPolynomial N := by
  classical
  simp [splitMachinScalarTaylorIntegerNumeratorPolynomial,
    splitMachinScalarTaylorApproxPolynomial,
    Polynomial.map_monomial,
    splitMachinScalarTaylorPartialSumInteger_spec]
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
  2 ^ (splitMachinScalarTaylorIntegerNumeratorPolynomial N).natDegree +
    splitMachinScalarTaylorCommonDenominator N +
    Int.natAbs (splitMachinScalarTaylorPartialSumInteger N) + 2

/--
The coefficient height of the integerized scalar Taylor polynomial is
bounded by the explicit H_N above.
-/
theorem splitMachinScalarTaylor_coefficient_height_bound (N : ℕ) :
    ∀ i,
      ‖((splitMachinScalarTaylorIntegerizedSequence.numerator N).map
        (algebraMap ℤ ℂ)).coeff i‖ ≤
          (splitMachinScalarTaylorHeight N : ℝ) := by
  intro i
  let a := splitMachinScalarTaylorPartialSumInteger N
  let D := splitMachinScalarTaylorCommonDenominator N
  have hformula :
      ((splitMachinScalarTaylorIntegerizedSequence.numerator N).map
        (algebraMap ℤ ℂ)).coeff i =
          (if i = 0 then (-(a : ℂ))
           else if i = 1 then (D : ℂ) else 0) := by
    by_cases hi0 : i = 0
    · subst i
      simp [splitMachinScalarTaylorIntegerizedSequence,
        splitMachinScalarTaylorIntegerNumeratorPolynomial]
    · by_cases hi1 : i = 1
      · subst i
        simp [splitMachinScalarTaylorIntegerizedSequence,
          splitMachinScalarTaylorIntegerNumeratorPolynomial]
      · simp [splitMachinScalarTaylorIntegerizedSequence,
          splitMachinScalarTaylorIntegerNumeratorPolynomial, hi0, hi1]
  rw [hformula]
  dsimp [splitMachinScalarTaylorHeight, a, D]
  split_ifs with hi0 hi1
  · simp
    exact_mod_cast (Nat.le_add_right
      (2 ^ (splitMachinScalarTaylorIntegerNumeratorPolynomial N).natDegree +
        splitMachinScalarTaylorCommonDenominator N)
      (Int.natAbs (splitMachinScalarTaylorPartialSumInteger N) + 2))
  · simp
    exact_mod_cast (Nat.le_add_right
      (2 ^ (splitMachinScalarTaylorIntegerNumeratorPolynomial N).natDegree +
        splitMachinScalarTaylorCommonDenominator N)
      (Int.natAbs (splitMachinScalarTaylorPartialSumInteger N) + 2))
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
  omega

/-- The degree contribution is controlled by the same height. -/
theorem splitMachinScalarTaylor_degree_height_bound (N : ℕ) :
    2 ^ (splitMachinScalarTaylorIntegerizedSequence.numerator N).natDegree ≤
      splitMachinScalarTaylorHeight N := by
  dsimp [splitMachinScalarTaylorIntegerizedSequence,
    splitMachinScalarTaylorHeight]
  omega

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
  apply hLiouville_of_integerized_height_degree_bounds
    (A := 1) (B := 1) (c := 1)
    (SP := splitMachinScalarTaylorIntegerizedSequence)
    (SQ := splitMachinScalarTaylorIntegerizedSequence)
  · exact Filter.Eventually.of_forall splitMachinScalarTaylorHeight_ge_two
  · exact Filter.Eventually.of_forall splitMachinScalarTaylor_coefficient_height_bound
  · exact Filter.Eventually.of_forall splitMachinScalarTaylor_coefficient_height_bound
  · exact Filter.Eventually.of_forall splitMachinScalarTaylor_degree_height_bound
  · exact Filter.Eventually.of_forall splitMachinScalarTaylor_degree_height_bound
  · exact Filter.Eventually.of_forall splitMachinScalarTaylor_denominator_height_bound
  · exact Filter.Eventually.of_forall splitMachinScalarTaylor_denominator_height_bound

#print axioms splitMachinScalarTaylor_has_concrete_hLiouville
#print axioms splitMachinScalarTaylorIntegerNumerator_map_eq

end EPlusPiApproximation
