module
public import Mathlib.NumberTheory.Transcendental.Liouville.Basic
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Topology.Basic

@[expose] public section

open Filter
open scoped Topology

/-!
# Integer linear forms and a super-polynomial approximation criterion

This module proves a general implication. It does not assert the existence of
the required approximants for e + π.

A form is written with a positive integer coefficient:
  L = a * x + b,  a ∈ ℕ, b ∈ ℤ.
Its coefficient height is max(a, |b|). If a tends to infinity, the
forms are eventually nonzero, and their absolute values are smaller than
every fixed inverse power of this height, then x is a Liouville number.
Mathlib's Liouville theorem then gives transcendence.

The positive coefficient convention is harmless: replace A*x+B by
|A|*x + sign(A)*B after multiplying the original form by -1 when needed.
-/

namespace EPlusPiApproximation

/-- The real value of the integer linear form a * x + b. -/
def integerLinearFormValue (x : ℝ) (a : ℕ) (b : ℤ) : ℝ :=
  (a : ℝ) * x + b

/-- The coefficient height of a * x + b. -/
def integerLinearFormHeight (a : ℕ) (b : ℤ) : ℕ :=
  max a b.natAbs


/-- The real value of a signed integer linear form A * x + B. -/
def signedIntegerLinearFormValue (x : ℝ) (A B : ℤ) : ℝ :=
  (A : ℝ) * x + B

/--
A nonzero integer-linear-form sequence converging to zero is an irrationality
certificate. This is the elementary Apéry-type criterion: if x were p/q,
then q * (A_n*x+B_n) would be a nonzero integer and hence have absolute value
at least one.
-/
theorem irrational_of_tendsto_zero_signed_integer_linear_forms
    {x : ℝ} {A B : ℕ → ℤ}
    (hnz : ∀ᶠ n : ℕ in atTop,
      signedIntegerLinearFormValue x (A n) (B n) ≠ 0)
    (hsmall : Tendsto
      (fun n : ℕ => |signedIntegerLinearFormValue x (A n) (B n)|)
      atTop (𝓝 0)) :
    Irrational x := by
  apply (irrational_iff_ne_rational x).2
  intro p q hq hEq
  have hqR : (q : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hq
  have hbound : 0 < 1 / |(q : ℝ)| :=
    one_div_pos.mpr (abs_pos.mpr hqR)
  have hevent : ∀ᶠ n : ℕ in atTop,
      |signedIntegerLinearFormValue x (A n) (B n)| < 1 / |(q : ℝ)| :=
    hsmall.eventually (Iio_mem_nhds hbound)
  obtain ⟨n, hnz, hevent⟩ := (hnz.and hevent).exists
  let C : ℤ := A n * p + q * B n
  have hFormEq :
      signedIntegerLinearFormValue x (A n) (B n) =
        (C : ℝ) / (q : ℝ) := by
    dsimp [signedIntegerLinearFormValue, C]
    rw [hEq]
    push_cast
    field_simp
  have hC : C ≠ 0 := by
    intro hC
    apply hnz
    rw [hFormEq, hC]
    norm_num
  have hCabs : (1 : ℝ) ≤ |(C : ℝ)| := by
    exact_mod_cast (Int.one_le_abs hC)
  have hAbsEq :
      |(C : ℝ)| =
        |signedIntegerLinearFormValue x (A n) (B n)| * |(q : ℝ)| := by
    rw [hFormEq, abs_div]
    field_simp
  have hCabsLt : |(C : ℝ)| < 1 := by
    rw [hAbsEq]
    calc
      |signedIntegerLinearFormValue x (A n) (B n)| * |(q : ℝ)|
          < (1 / |(q : ℝ)|) * |(q : ℝ)| :=
        mul_lt_mul_of_pos_right hevent (abs_pos.mpr hqR)
      _ = 1 := by field_simp
  linarith

/--
Super-polynomial integer linear forms make x a Liouville number.

No coprimality assumption is needed. The positive leading coefficient makes
the rational denominator positive, and the height dominates that denominator.
-/
theorem liouville_of_superpolynomial_integer_linear_forms
    {x : ℝ} {a : ℕ → ℕ} {b : ℕ → ℤ}
    (ha : Tendsto a atTop atTop)
    (hnz : ∀ᶠ n : ℕ in atTop,
      integerLinearFormValue x (a n) (b n) ≠ 0)
    (hsmall : ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
      |integerLinearFormValue x (a n) (b n)| <
        1 / (integerLinearFormHeight (a n) (b n) : ℝ) ^ k) :
    Liouville x := by
  intro k
  have hden : ∀ᶠ n : ℕ in atTop, 1 < a n :=
    ha.eventually (eventually_gt_atTop 1)
  obtain ⟨n, hden, hnz, hsmall⟩ :=
    (hden.and (hnz.and (hsmall k))).exists
  refine ⟨-b n, (a n : ℤ), ?_, ?_, ?_⟩
  · exact_mod_cast hden
  · intro hEq
    apply hnz
    change (a n : ℝ) * x + (b n : ℝ) = 0
    have hEq' : x = -(b n : ℝ) / (a n : ℝ) := by
      exact_mod_cast hEq
    rw [hEq']
    field_simp
    ring
  · have haPos : (0 : ℝ) < (a n : ℝ) :=
      Nat.cast_pos.mpr (Nat.zero_lt_of_lt hden)
    have hHeight : a n ≤ integerLinearFormHeight (a n) (b n) := by
      exact le_max_left _ _
    have hPowNat :
        (a n) ^ k ≤ integerLinearFormHeight (a n) (b n) ^ k := by
      gcongr
    have hPow : (a n : ℝ) ^ k ≤
        (integerLinearFormHeight (a n) (b n) : ℝ) ^ k := by
      exact_mod_cast hPowNat
    have hRecip :
        1 / (integerLinearFormHeight (a n) (b n) : ℝ) ^ k ≤
          1 / (a n : ℝ) ^ k :=
      one_div_le_one_div_of_le (by positivity) hPow
    have hForm :
        x - (-(b n : ℝ) / (a n : ℝ)) =
          integerLinearFormValue x (a n) (b n) / (a n : ℝ) := by
      unfold integerLinearFormValue
      field_simp
      ring
    have hNum : ((-b n : ℤ) : ℝ) = -(b n : ℝ) := by norm_cast
    have hDenCast : ((a n : ℤ) : ℝ) = (a n : ℝ) := by norm_cast
    rw [hNum, hDenCast, hForm, abs_div, abs_of_pos haPos]
    calc
      |integerLinearFormValue x (a n) (b n)| / (a n : ℝ)
          < (1 / (integerLinearFormHeight (a n) (b n) : ℝ) ^ k) /
              (a n : ℝ) :=
            div_lt_div_of_pos_right hsmall haPos
      _ ≤ (1 / (a n : ℝ) ^ k) / (a n : ℝ) :=
        div_le_div_of_nonneg_right hRecip (le_of_lt haPos)
      _ ≤ 1 / (a n : ℝ) ^ k := by
        apply div_le_self (by positivity)
        exact_mod_cast (Nat.one_le_of_lt hden)

/--
A super-polynomial sequence of nonzero integer linear forms proves
transcendence over ℚ. The proof uses Mathlib's Liouville theorem and the
algebraicity of the extension ℚ/ℤ.
-/
theorem transcendental_of_superpolynomial_integer_linear_forms
    {x : ℝ} {a : ℕ → ℕ} {b : ℕ → ℤ}
    (ha : Tendsto a atTop atTop)
    (hnz : ∀ᶠ n : ℕ in atTop,
      integerLinearFormValue x (a n) (b n) ≠ 0)
    (hsmall : ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
      |integerLinearFormValue x (a n) (b n)| <
        1 / (integerLinearFormHeight (a n) (b n) : ℝ) ^ k) :
    Transcendental ℚ x := by
  have hL : Liouville x :=
    liouville_of_superpolynomial_integer_linear_forms ha hnz hsmall
  have hZ : Transcendental ℤ x := Liouville.transcendental hL
  have hAlg : Algebra.IsAlgebraic ℤ ℚ :=
    IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have hExtend [inst : Algebra.IsAlgebraic ℤ ℚ] :
      Transcendental ℚ x := hZ.extendScalars ℚ
  exact @hExtend hAlg

#print axioms liouville_of_superpolynomial_integer_linear_forms
#print axioms transcendental_of_superpolynomial_integer_linear_forms

end EPlusPiApproximation
