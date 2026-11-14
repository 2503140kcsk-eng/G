module
public import ApproximationCriteria

@[expose] public section

open Filter
open scoped Topology

namespace EPlusPiApproximation

/-- The real value of the integer linear form A * x - C. -/
def pairedIntegerLinearFormValue (x : ℝ) (A C : ℤ) : ℝ :=
  (A : ℝ) * x - (C : ℝ)

/--
A pair of adjacent integer linear forms is an irrationality certificate
when its coefficient determinant is eventually nonzero and the sum of
the two absolute errors tends to zero.

Unlike the one-form criterion, this theorem does not require either
individual form to be nonzero at every sufficiently large index. The
determinant guarantees that the two adjacent forms cannot both vanish.
-/
theorem irrational_of_tendsto_zero_paired_integer_linear_forms
    {x : ℝ} {A C : ℕ → ℤ}
    (hdet : ∀ᶠ n : ℕ in atTop,
      A n * C (n + 1) - A (n + 1) * C n ≠ 0)
    (hsmall : Tendsto
      (fun n : ℕ =>
        |(A n : ℝ) * x - (C n : ℝ)| +
          |(A (n + 1) : ℝ) * x - (C (n + 1) : ℝ)|)
      atTop (𝓝 0)) :
    Irrational x := by
  apply (irrational_iff_ne_rational x).2
  intro p q hq hEq
  have hqR : (q : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hq
  have hbound : 0 < 1 / |(q : ℝ)| :=
    one_div_pos.mpr (abs_pos.mpr hqR)
  have hevent : ∀ᶠ n : ℕ in atTop,
      |pairedIntegerLinearFormValue x (A n) (C n)| +
        |pairedIntegerLinearFormValue x (A (n + 1)) (C (n + 1))| <
          1 / |(q : ℝ)| :=
    (by simpa [pairedIntegerLinearFormValue] using
      hsmall.eventually (Iio_mem_nhds hbound))
  obtain ⟨n, hd, hevent⟩ := (hdet.and hevent).exists
  let L : ℕ → ℝ := fun k =>
    pairedIntegerLinearFormValue x (A k) (C k)
  let a : ℤ := if L n ≠ 0 then A n else A (n + 1)
  let c : ℤ := if L n ≠ 0 then C n else C (n + 1)
  have hselected :
      pairedIntegerLinearFormValue x a c =
        if L n ≠ 0 then L n else L (n + 1) := by
    by_cases h : L n ≠ 0 <;>
      simp [pairedIntegerLinearFormValue, a, c, L, h]
  have hselected_nz :
      pairedIntegerLinearFormValue x a c ≠ 0 := by
    rw [hselected]
    by_cases hzero : L n = 0
    · have hnext : L (n + 1) ≠ 0 := by
        intro hnext
        apply hd
        have hfirst : (A n : ℝ) * x = (C n : ℝ) := by
          dsimp [L, pairedIntegerLinearFormValue] at hzero
          linarith
        have hsecond : (A (n + 1) : ℝ) * x = (C (n + 1) : ℝ) := by
          dsimp [L, pairedIntegerLinearFormValue] at hnext
          linarith
        have hdetR :
            ((A n * C (n + 1) - A (n + 1) * C n : ℤ) : ℝ) = 0 := by
          push_cast
          linear_combination
            (A (n + 1) : ℝ) * hfirst - (A n : ℝ) * hsecond
        exact_mod_cast hdetR
      simp [hzero, hnext]
    · simp [hzero]
  have hselected_abs_le :
      |pairedIntegerLinearFormValue x a c| ≤ |L n| + |L (n + 1)| := by
    rw [hselected]
    by_cases hzero : L n = 0
    · simp [hzero]
    · simp only [if_pos hzero]
      exact le_add_of_nonneg_right (abs_nonneg _)
  have hselected_lt :
      |pairedIntegerLinearFormValue x a c| < 1 / |(q : ℝ)| :=
    lt_of_le_of_lt hselected_abs_le hevent
  let T : ℤ := a * p - c * q
  have hFormEq :
      pairedIntegerLinearFormValue x a c = (T : ℝ) / (q : ℝ) := by
    dsimp [pairedIntegerLinearFormValue, T]
    rw [hEq]
    push_cast
    field_simp
  have hT : T ≠ 0 := by
    intro hT
    apply hselected_nz
    rw [hFormEq, hT]
    norm_num
  have hTabs : (1 : ℝ) ≤ |(T : ℝ)| := by
    exact_mod_cast (Int.one_le_abs hT)
  have hAbsEq :
      |(T : ℝ)| =
        |pairedIntegerLinearFormValue x a c| * |(q : ℝ)| := by
    rw [hFormEq, abs_div]
    field_simp
  have hTabsLt : |(T : ℝ)| < 1 := by
    rw [hAbsEq]
    calc
      |pairedIntegerLinearFormValue x a c| * |(q : ℝ)|
          < (1 / |(q : ℝ)|) * |(q : ℝ)| :=
        mul_lt_mul_of_pos_right hselected_lt (abs_pos.mpr hqR)
      _ = 1 := by field_simp
  linarith

#print axioms irrational_of_tendsto_zero_paired_integer_linear_forms

end EPlusPiApproximation
