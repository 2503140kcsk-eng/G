module
public import Mathlib

@[expose] public section

/-!
# Primitive rank-one endpoint arithmetic

A Bezout identity certifies that the pair (a,b) is primitive. If another
integer pair (c,d) is collinear with it (zero 2x2 determinant), then that
pair is an integer multiple of (a,b). This is the elementary saturation
step used when identifying rank-one endpoint kernels.
-/

namespace EPlusPiApproximation

/--
If (a,b) is primitive in the Bezout sense and (c,d) is collinear with it,
then (c,d) is an integer multiple of (a,b).

The determinant hypothesis is a*d = b*c. The Bezout witness is the
integral certificate of primitivity. In lattice applications, the determinant
condition is obtained from rational rank one, while the Bezout witness comes
from gcd normalization.
-/
theorem integer_pair_multiple_of_bezout_and_determinant
    {a b c d : ℤ}
    (hbez : ∃ u v : ℤ, u * a + v * b = 1)
    (hdet : a * d = b * c) :
    ∃ k : ℤ, c = k * a ∧ d = k * b := by
  obtain ⟨u, v, hbez⟩ := hbez
  refine ⟨u * c + v * d, ?_, ?_⟩
  · have h : (u * c + v * d) * a = c := by
      calc
        (u * c + v * d) * a = u * (a * c) + v * (a * d) := by ring
        _ = u * (a * c) + v * (b * c) := by rw [hdet]
        _ = (u * a + v * b) * c := by ring
        _ = c := by rw [hbez]; ring
    exact h.symm
  · have h : (u * c + v * d) * b = d := by
      calc
        (u * c + v * d) * b = u * (b * c) + v * (b * d) := by ring
        _ = u * (a * d) + v * (b * d) := by rw [← hdet]
        _ = (u * a + v * b) * d := by ring
        _ = d := by rw [hbez]; ring
    exact h.symm

#print axioms integer_pair_multiple_of_bezout_and_determinant


/--
A pair of integers with gcd one is Bezout-primitive, so every collinear
integer pair is an integral multiple of it.
-/
theorem integer_pair_multiple_of_gcd_one_and_determinant
    {a b c d : ℤ}
    (hcoprime : Int.gcd a b = 1)
    (hdet : a * d = b * c) :
    ∃ k : ℤ, c = k * a ∧ d = k * b := by
  have hgcd : (Int.gcd a b : ℤ) = 1 := by
    exact_mod_cast hcoprime
  have hbezsum : (1 : ℤ) = a * Int.gcdA a b + b * Int.gcdB a b := by
    calc
      (1 : ℤ) = (Int.gcd a b : ℤ) := hgcd.symm
      _ = a * Int.gcdA a b + b * Int.gcdB a b :=
        Int.gcd_eq_gcd_ab a b
  have hbez : ∃ u v : ℤ, u * a + v * b = 1 := by
    refine ⟨Int.gcdA a b, Int.gcdB a b, ?_⟩
    nlinarith [hbezsum]
  exact integer_pair_multiple_of_bezout_and_determinant hbez hdet

/--
For a finite or infinite family of integer rows, if every row is collinear
with a Bezout-primitive anchor row and that anchor row occurs in the family,
then the common kernel of all rows is exactly the kernel of the anchor.
This is the abstract rank-one kernel reduction used before inserting the
specific Split–Machin endpoint matrix.
-/
theorem integer_row_kernel_iff_anchor
    {ι : Type*} (i₀ : ι) {a b : ℤ} (A B : ι → ℤ)
    (hA₀ : A i₀ = a) (hB₀ : B i₀ = b)
    (hbez : ∃ u v : ℤ, u * a + v * b = 1)
    (hcollinear : ∀ i, a * B i = b * A i)
    (x y : ℤ) :
    (∀ i, A i * x + B i * y = 0) ↔ a * x + b * y = 0 := by
  constructor
  · intro hall
    have h := hall i₀
    simpa [hA₀, hB₀] using h
  · intro hanchor i
    obtain ⟨k, hA, hB⟩ :=
      integer_pair_multiple_of_bezout_and_determinant
        hbez (hcollinear i)
    calc
      A i * x + B i * y = (k * a) * x + (k * b) * y := by rw [hA, hB]
      _ = k * (a * x + b * y) := by ring
      _ = 0 := by rw [hanchor]; ring

/-- The row-kernel reduction with primitivity expressed as gcd one. -/
theorem integer_row_kernel_iff_anchor_of_gcd_one
    {ι : Type*} (i₀ : ι) {a b : ℤ} (A B : ι → ℤ)
    (hA₀ : A i₀ = a) (hB₀ : B i₀ = b)
    (hcoprime : Int.gcd a b = 1)
    (hcollinear : ∀ i, a * B i = b * A i)
    (x y : ℤ) :
    (∀ i, A i * x + B i * y = 0) ↔ a * x + b * y = 0 :=
  integer_row_kernel_iff_anchor i₀ A B hA₀ hB₀
    (by
      obtain ⟨u, v, hbez⟩ :=
        (show ∃ u v : ℤ, u * a + v * b = 1 from by
          have hgcd : (Int.gcd a b : ℤ) = 1 := by exact_mod_cast hcoprime
          have hbezsum : (1 : ℤ) =
              a * Int.gcdA a b + b * Int.gcdB a b := by
            calc
              (1 : ℤ) = (Int.gcd a b : ℤ) := hgcd.symm
              _ = a * Int.gcdA a b + b * Int.gcdB a b :=
                Int.gcd_eq_gcd_ab a b
          exact ⟨Int.gcdA a b, Int.gcdB a b, by nlinarith [hbezsum]⟩)
      exact ⟨u, v, hbez⟩)
    hcollinear x y

#print axioms integer_pair_multiple_of_gcd_one_and_determinant
#print axioms integer_row_kernel_iff_anchor
#print axioms integer_row_kernel_iff_anchor_of_gcd_one

end EPlusPiApproximation
