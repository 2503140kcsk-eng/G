module
public import Mathlib

@[expose] public section

/-!
# Exact coefficient denominators for the Split–Machin arctangent series

For
  G(z) = 16 atan(z/5) - 4 atan(z/239),
the coefficient of z^k is zero for even k and, for odd k, is
  (-1)^((k-1)/2) * (16/5^k - 4/239^k) / k.

The definitions below encode that coefficient as an exact integer numerator
over an explicit positive natural denominator. The finite product of these
denominators is a common denominator for every coefficient in the truncated
series. No floating-point calculation or asymptotic claim is used here.
-/

namespace EPlusPiApproximation

/-- Signed integer numerator of the k-th Split–Machin Taylor coefficient. -/
def splitMachinTaylorNumerator (k : ℕ) : ℤ :=
  if k % 2 = 1 then
    (if k / 2 % 2 = 0 then 1 else -1) *
      (16 * (239 : ℤ) ^ k - 4 * (5 : ℤ) ^ k)
  else 0

/-- Explicit positive denominator of the k-th Split–Machin coefficient. -/
def splitMachinTaylorDenominator (k : ℕ) : ℕ :=
  if k % 2 = 1 then k * 5 ^ k * 239 ^ k else 1

/-- Exact rational coefficient of z^k in the Split–Machin series. -/
def splitMachinTaylorCoefficient (k : ℕ) : ℚ :=
  (splitMachinTaylorNumerator k : ℚ) /
    (splitMachinTaylorDenominator k : ℚ)

/-- Product common denominator for all coefficients of degrees 0 through N. -/
def splitMachinTaylorCommonDenominator (N : ℕ) : ℕ :=
  ∏ k ∈ Finset.range (N + 1), splitMachinTaylorDenominator k

/-- Every individual coefficient denominator is positive. -/
theorem splitMachinTaylorDenominator_pos (k : ℕ) :
    0 < splitMachinTaylorDenominator k := by
  by_cases hk : k % 2 = 1
  · have hkpos : 0 < k := by omega
    simp [splitMachinTaylorDenominator, hk]
    positivity
  · simp [splitMachinTaylorDenominator, hk]

/-- The product common denominator is positive. -/
theorem splitMachinTaylorCommonDenominator_pos (N : ℕ) :
    0 < splitMachinTaylorCommonDenominator N := by
  classical
  unfold splitMachinTaylorCommonDenominator
  apply Finset.prod_pos
  intro k hk
  exact splitMachinTaylorDenominator_pos k

/-- Each coefficient denominator divides the common denominator of a truncation. -/
theorem splitMachinTaylorDenominator_dvd_common
    (N k : ℕ) (hk : k ≤ N) :
    splitMachinTaylorDenominator k ∣
      splitMachinTaylorCommonDenominator N := by
  classical
  unfold splitMachinTaylorCommonDenominator
  exact Finset.dvd_prod_of_mem splitMachinTaylorDenominator
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

/--
After multiplying by the exact common denominator of the degree-N truncation,
each Split–Machin Taylor coefficient of degree at most N is an integer.
This is the basic denominator-clearing statement needed before any height
estimate can be applied to a polynomial sequence.
-/
theorem splitMachinTaylor_commonDenominator_clears_coefficient
    (N k : ℕ) (hk : k ≤ N) :
    ∃ z : ℤ,
      (splitMachinTaylorCommonDenominator N : ℚ) *
        splitMachinTaylorCoefficient k = z := by
  let d := splitMachinTaylorDenominator k
  let D := splitMachinTaylorCommonDenominator N
  have hdpos : 0 < d := splitMachinTaylorDenominator_pos k
  have hdvd : d ∣ D := by
    exact splitMachinTaylorDenominator_dvd_common N k hk
  have hmulNat : d * (D / d) = D :=
    Nat.mul_div_cancel' hdvd
  have hmul : (d : ℚ) * (D / d : ℚ) = (D : ℚ) := by
    exact_mod_cast hmulNat
  refine ⟨(D / d : ℕ) * splitMachinTaylorNumerator k, ?_⟩
  dsimp [splitMachinTaylorCoefficient, d, D]
  rw [← hmul]
  push_cast
  have hdq : (d : ℚ) ≠ 0 := by
    exact_mod_cast hdpos.ne'
  field_simp [hdq]
  <;> ring_nf

/-- Exact first nonzero coefficient, retained as a small arithmetic regression. -/
theorem splitMachinTaylorCoefficient_one :
    splitMachinTaylorCoefficient 1 = (3804 : ℚ) / 1195 := by
  norm_num [splitMachinTaylorCoefficient, splitMachinTaylorNumerator,
    splitMachinTaylorDenominator]

#print axioms splitMachinTaylor_commonDenominator_clears_coefficient

end EPlusPiApproximation
