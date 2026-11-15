import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Holonomic Chebyshev kernel

This module uses Mathlib's integral-coefficient Chebyshev families as a
first certified test case for a recurrence -> determinant -> asymptotic
pipeline. No external axiom or approximation oracle is used.
-/

open Filter
open scoped Topology
open Polynomial

noncomputable section

namespace HolonomicHDA

/-- The coefficient of degree k in the n-th first-kind Chebyshev polynomial. -/
def tCoeff (n k : ℕ) : ℚ :=
  (Polynomial.Chebyshev.T ℚ (n : ℤ)).coeff k

/-- The coefficient of degree k in the n-th second-kind Chebyshev polynomial. -/
def uCoeff (n k : ℕ) : ℚ :=
  (Polynomial.Chebyshev.U ℚ (n : ℤ)).coeff k

/-- First-kind coefficient recurrence, away from the constant coefficient. -/
theorem tCoeff_succ_succ (n k : ℕ) :
    tCoeff (n + 2) (k + 1) =
      2 * tCoeff (n + 1) k - tCoeff n (k + 1) := by
  simp [tCoeff, Polynomial.Chebyshev.T_add_two, ← mul_assoc]

/-- Boundary case of the first-kind coefficient recurrence. -/
theorem tCoeff_succ_succ_zero (n : ℕ) :
    tCoeff (n + 2) 0 = -tCoeff n 0 := by
  simp [tCoeff, Polynomial.Chebyshev.T_add_two, ← mul_assoc]

/-- Second-kind coefficient recurrence, away from the constant coefficient. -/
theorem uCoeff_succ_succ (n k : ℕ) :
    uCoeff (n + 2) (k + 1) =
      2 * uCoeff (n + 1) k - uCoeff n (k + 1) := by
  simp [uCoeff, Polynomial.Chebyshev.U_add_two, ← mul_assoc]

/-- Boundary case of the second-kind coefficient recurrence. -/
theorem uCoeff_succ_succ_zero (n : ℕ) :
    uCoeff (n + 2) 0 = -uCoeff n 0 := by
  simp [uCoeff, Polynomial.Chebyshev.U_add_two, ← mul_assoc]

/-- The discrete Wronskian (Casoratian) of the two Chebyshev solutions. -/
def casoratian (n : ℕ) : Polynomial ℚ :=
  Polynomial.Chebyshev.T ℚ ((n : ℤ) + 1) *
      Polynomial.Chebyshev.U ℚ (n : ℤ) -
    Polynomial.Chebyshev.T ℚ (n : ℤ) *
      Polynomial.Chebyshev.U ℚ ((n : ℤ) + 1)

/-- The Casoratian is invariant under the common second-order recurrence. -/
theorem casoratian_succ (n : ℕ) :
    casoratian (n + 1) = casoratian n := by
  simp only [casoratian, Nat.cast_add, Nat.cast_one]
  have hT :
      Polynomial.Chebyshev.T ℚ ((n : ℤ) + 1 + 1) =
        2 * Polynomial.X * Polynomial.Chebyshev.T ℚ ((n : ℤ) + 1) -
          Polynomial.Chebyshev.T ℚ (n : ℤ) := by
    convert Polynomial.Chebyshev.T_add_two ℚ (n : ℤ) using 1 <;> congr 1 <;> ring
  have hU :
      Polynomial.Chebyshev.U ℚ ((n : ℤ) + 1 + 1) =
        2 * Polynomial.X * Polynomial.Chebyshev.U ℚ ((n : ℤ) + 1) -
          Polynomial.Chebyshev.U ℚ (n : ℤ) := by
    convert Polynomial.Chebyshev.U_add_two ℚ (n : ℤ) using 1 <;> congr 1 <;> ring
  rw [hT, hU]
  ring

/-- Exact determinant invariant for the first- and second-kind families. -/
theorem casoratian_eq_neg_X (n : ℕ) :
    casoratian n = -Polynomial.X := by
  induction n with
  | zero =>
      simp [casoratian, Polynomial.Chebyshev.T_zero,
        Polynomial.Chebyshev.T_one, Polynomial.Chebyshev.U_zero,
        Polynomial.Chebyshev.U_one]
      ring
  | succ n ih =>
      rw [casoratian_succ, ih]

/-- The explicit 2x2 determinant polynomial a*d - b*c. -/
def det2 {R : Type*} [CommRing R] (a b c d : R) : R := a * d - b * c

/-- Fundamental matrix determinant of the two adjacent Chebyshev states. -/
def fundamentalDet (n : ℕ) : Polynomial ℚ :=
  det2
    (Polynomial.Chebyshev.T ℚ (n : ℤ))
    (Polynomial.Chebyshev.T ℚ ((n : ℤ) + 1))
    (Polynomial.Chebyshev.U ℚ (n : ℤ))
    (Polynomial.Chebyshev.U ℚ ((n : ℤ) + 1))

/-- The displayed determinant is the negative of the Casoratian. -/
theorem fundamentalDet_eq_neg_casoratian (n : ℕ) :
    fundamentalDet n = -casoratian n := by
  simp [fundamentalDet, det2, casoratian]
  ring

/-- The 2x2 fundamental determinant is exactly X, independently of n. -/
theorem fundamentalDet_eq_X (n : ℕ) :
    fundamentalDet n = Polynomial.X := by
  rw [fundamentalDet_eq_neg_casoratian, casoratian_eq_neg_X]
  simp

/-- Real scaled second-kind Chebyshev values at the Mehler-Heine scale. -/
def scaledU (t : ℝ) (n : ℕ) : ℝ :=
  ((Polynomial.Chebyshev.U ℝ (n : ℤ)).eval
      (Real.cos (t / ((n : ℝ) + 1)))) / ((n : ℝ) + 1)

/-- The nonzero angle t/(n+1) tends to zero through nonzero values. -/
theorem tendsto_scaledAngle_punctured (t : ℝ) (ht : t ≠ 0) :
    Tendsto (fun n : ℕ => t / ((n : ℝ) + 1)) atTop (𝓝[≠] 0) := by
  have hzero : Tendsto (fun n : ℕ => t / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds (x := t)).mul hinv
  have hne : ∀ᶠ n : ℕ in atTop, t / ((n : ℝ) + 1) ≠ 0 := by
    filter_upwards with n
    exact div_ne_zero ht (by positivity)
  exact (tendsto_nhdsWithin_iff).2 ⟨hzero, hne⟩

/-- Mehler-Heine limit for the second-kind Chebyshev family:
    U_n(cos(t/(n+1)))/(n+1) tends to sin(t)/t for t ≠ 0. -/
theorem scaledU_tendsto (t : ℝ) (ht : t ≠ 0) :
    Tendsto (fun n : ℕ => scaledU t n) atTop (𝓝 (Real.sin t / t)) := by
  let θ : ℕ → ℝ := fun n => t / ((n : ℝ) + 1)
  have hθ : Tendsto θ atTop (𝓝[≠] 0) := by
    simpa [θ] using tendsto_scaledAngle_punctured t ht
  have hratio : Tendsto (fun n : ℕ => Real.sin (θ n) / θ n)
      atTop (𝓝 1) :=
    Real.tendsto_sin_div_nhdsNE_zero.comp hθ
  have hden : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * Real.sin (θ n))
      atTop (𝓝 t) := by
    have heq : ∀ n : ℕ,
        ((n : ℝ) + 1) * Real.sin (θ n) =
          t * (Real.sin (θ n) / θ n) := by
      intro n
      have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
      have hθn : θ n = t / ((n : ℝ) + 1) := rfl
      rw [hθn]
      field_simp
    simpa only [heq, mul_one] using (tendsto_const_nhds (x := t)).mul hratio
  have hden_ne : ∀ᶠ n : ℕ in atTop,
      ((n : ℝ) + 1) * Real.sin (θ n) ≠ 0 :=
    hden.eventually_ne ht
  have hquot : Tendsto
      (fun n : ℕ => Real.sin t /
        (((n : ℝ) + 1) * Real.sin (θ n)))
      atTop (𝓝 (Real.sin t / t)) :=
    (tendsto_const_nhds (x := Real.sin t)).div hden ht
  have heventual : ∀ᶠ n : ℕ in atTop,
      scaledU t n =
        Real.sin t / (((n : ℝ) + 1) * Real.sin (θ n)) := by
    filter_upwards [hden_ne] with n hne
    have htrig :
        (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval (Real.cos (θ n)) *
          Real.sin (θ n) = Real.sin (((n : ℝ) + 1) * θ n) := by
      simpa using
        (Polynomial.Chebyshev.U_real_cos (θ n) (n : ℤ))
    have harg : ((n : ℝ) + 1) * θ n = t := by
      dsimp [θ]
      field_simp
    rw [harg] at htrig
    have htrig' :
        (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval
            (Real.cos (t / ((n : ℝ) + 1))) *
          Real.sin (t / ((n : ℝ) + 1)) = Real.sin t := by
      simpa [θ] using htrig
    dsimp [scaledU]
    field_simp [hne]
    rw [mul_assoc, htrig']
    ring
  exact hquot.congr' (heventual.mono fun n h => h.symm)

#print axioms tCoeff_succ_succ
#print axioms uCoeff_succ_succ
#print axioms casoratian_eq_neg_X
#print axioms fundamentalDet_eq_X
#print axioms scaledU_tendsto

end HolonomicHDA
