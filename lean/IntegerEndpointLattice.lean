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
A gcd-one pair admits an explicit integer Bezout witness. This packages the
fixed Mathlib extended-gcd API for later lattice arguments.
-/
theorem exists_bezout_of_int_gcd_eq_one
    {a b : ℤ} (hcoprime : Int.gcd a b = 1) :
    ∃ u v : ℤ, u * a + v * b = 1 := by
  have hgcd : (Int.gcd a b : ℤ) = 1 := by
    exact_mod_cast hcoprime
  have hbezsum : (1 : ℤ) = a * Int.gcdA a b + b * Int.gcdB a b := by
    calc
      (1 : ℤ) = (Int.gcd a b : ℤ) := hgcd.symm
      _ = a * Int.gcdA a b + b * Int.gcdB a b :=
        Int.gcd_eq_gcd_ab a b
  exact ⟨Int.gcdA a b, Int.gcdB a b, by nlinarith [hbezsum]⟩

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
  exact integer_pair_multiple_of_bezout_and_determinant
    (exists_bezout_of_int_gcd_eq_one hcoprime) hdet

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
    (∀ i, A i * x + B i * y = 0) ↔ a * x + b * y = 0 := by
  exact integer_row_kernel_iff_anchor i₀ A B hA₀ hB₀
    (exists_bezout_of_int_gcd_eq_one hcoprime) hcollinear x y


/--
For a two-column integer matrix, if every 2x2 minor formed with a primitive
anchor row vanishes, then the matrix kernel is exactly the anchor-row kernel.
This is the concrete matrix interface for the endpoint source.
-/
theorem integer_two_column_matrix_kernel_iff_anchor
    {ι : Type*} (i₀ : ι) (M : Matrix ι (Fin 2) ℤ)
    {a b : ℤ}
    (hA₀ : M i₀ 0 = a) (hB₀ : M i₀ 1 = b)
    (hbez : ∃ u v : ℤ, u * a + v * b = 1)
    (hminor : ∀ i, a * M i 1 = b * M i 0)
    (x y : ℤ) :
    (∀ i, M i 0 * x + M i 1 * y = 0) ↔ a * x + b * y = 0 :=
  integer_row_kernel_iff_anchor i₀
    (fun i => M i 0) (fun i => M i 1) hA₀ hB₀ hbez hminor x y

/--
The gcd-one condition is essential: the nonprimitive row (2,2) is collinear
with (1,1), but (1,1) is not an integer multiple of (2,2).
-/
theorem nonprimitive_pair_counterexample :
    (2 : ℤ) * 1 = 2 * 1 ∧
      ¬ ∃ k : ℤ, (1 : ℤ) = k * 2 ∧ 1 = k * 2 := by
  constructor
  · norm_num
  · rintro ⟨k, hk, _⟩
    omega

#print axioms exists_bezout_of_int_gcd_eq_one
#print axioms integer_two_column_matrix_kernel_iff_anchor
#print axioms nonprimitive_pair_counterexample

#print axioms integer_pair_multiple_of_gcd_one_and_determinant
#print axioms integer_row_kernel_iff_anchor
#print axioms integer_row_kernel_iff_anchor_of_gcd_one

end EPlusPiApproximation
