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


/--
The integer kernel of a primitive row (a,b) is generated by the primitive
perpendicular vector (-b,a). The witness u*a+v*b=1 gives the explicit
multiplier u*y-v*x.
-/
theorem integer_pair_kernel_iff_primitive_generator
    {a b x y : ℤ}
    (hbez : ∃ u v : ℤ, u * a + v * b = 1) :
    a * x + b * y = 0 ↔
      ∃ k : ℤ, x = -b * k ∧ y = a * k := by
  constructor
  · intro hkernel
    obtain ⟨u, v, hbez⟩ := hbez
    have hax : a * x = -b * y := by linarith [hkernel]
    have hby : b * y = -a * x := by linarith [hkernel]
    refine ⟨u * y - v * x, ?_, ?_⟩
    · calc
        x = (u * a + v * b) * x := by rw [hbez]; ring
        _ = u * (a * x) + v * (b * x) := by ring
        _ = u * (-b * y) + v * (b * x) := by rw [hax]
        _ = -b * (u * y - v * x) := by ring
    · calc
        y = (u * a + v * b) * y := by rw [hbez]; ring
        _ = u * (a * y) + v * (b * y) := by ring
        _ = u * (a * y) + v * (-a * x) := by rw [hby]
        _ = a * (u * y - v * x) := by ring
  · rintro ⟨k, rfl, rfl⟩
    ring

/--
If all rows are collinear with a Bezout-primitive anchor direction and at
least one matrix row is nonzero, then the common kernel equals the anchor
kernel. Unlike the anchor-included variant, the primitive anchor need not
itself occur as a row; this fits saturated source matrices whose rows may
all have nontrivial common content.
-/
theorem integer_row_kernel_iff_anchor_of_nonzero
    {ι : Type*} {a b : ℤ} (A B : ι → ℤ)
    (hbez : ∃ u v : ℤ, u * a + v * b = 1)
    (hcollinear : ∀ i, a * B i = b * A i)
    (hnonzero : ∃ i, A i ≠ 0 ∨ B i ≠ 0)
    (x y : ℤ) :
    (∀ i, A i * x + B i * y = 0) ↔ a * x + b * y = 0 := by
  constructor
  · intro hall
    obtain ⟨i, hi⟩ := hnonzero
    obtain ⟨k, hA, hB⟩ :=
      integer_pair_multiple_of_bezout_and_determinant hbez (hcollinear i)
    have hk : k ≠ 0 := by
      intro hk
      have hAz : A i = 0 := by simpa [hk] using hA
      have hBz : B i = 0 := by simpa [hk] using hB
      exact hi.elim (fun h => h hAz) (fun h => h hBz)
    have hmul : k * (a * x + b * y) = 0 := by
      calc
        k * (a * x + b * y) = (k * a) * x + (k * b) * y := by ring
        _ = A i * x + B i * y := by rw [← hA, ← hB]
        _ = 0 := hall i
    exact (mul_eq_zero.mp hmul).resolve_left hk
  · intro hanchor i
    obtain ⟨k, hA, hB⟩ :=
      integer_pair_multiple_of_bezout_and_determinant hbez (hcollinear i)
    calc
      A i * x + B i * y = (k * a) * x + (k * b) * y := by rw [hA, hB]
      _ = k * (a * x + b * y) := by ring
      _ = 0 := by rw [hanchor]; ring

/-- A two-column matrix with one nonzero row and all anchor minors zero has
    common integer kernel equal to the anchor-row kernel. The primitive anchor
    need not appear among the original rows. -/
theorem integer_two_column_matrix_kernel_iff_anchor_of_nonzero
    {ι : Type*} (M : Matrix ι (Fin 2) ℤ)
    {a b : ℤ}
    (hbez : ∃ u v : ℤ, u * a + v * b = 1)
    (hminor : ∀ i, a * M i 1 = b * M i 0)
    (hnonzero : ∃ i, M i 0 ≠ 0 ∨ M i 1 ≠ 0)
    (x y : ℤ) :
    (∀ i, M i 0 * x + M i 1 * y = 0) ↔ a * x + b * y = 0 :=
  integer_row_kernel_iff_anchor_of_nonzero
    (fun i => M i 0) (fun i => M i 1) hbez hminor hnonzero x y

/-- If the anchor is primitive, the nonzero-row matrix kernel is precisely
    the Z-span of its perpendicular vector. -/
theorem integer_two_column_matrix_kernel_eq_zsmul_anchor_of_nonzero
    {ι : Type*} (M : Matrix ι (Fin 2) ℤ)
    {a b : ℤ}
    (hbez : ∃ u v : ℤ, u * a + v * b = 1)
    (hminor : ∀ i, a * M i 1 = b * M i 0)
    (hnonzero : ∃ i, M i 0 ≠ 0 ∨ M i 1 ≠ 0)
    (x y : ℤ) :
    (∀ i, M i 0 * x + M i 1 * y = 0) ↔
      ∃ k : ℤ, x = -b * k ∧ y = a * k :=
  (integer_two_column_matrix_kernel_iff_anchor_of_nonzero
    M hbez hminor hnonzero x y).trans
    (integer_pair_kernel_iff_primitive_generator hbez)

/-- Gcd-one variant when the primitive direction need not occur as a row. -/
theorem integer_two_column_matrix_kernel_eq_zsmul_anchor_of_nonzero_gcd_one
    {ι : Type*} (M : Matrix ι (Fin 2) ℤ)
    {a b : ℤ}
    (hcoprime : Int.gcd a b = 1)
    (hminor : ∀ i, a * M i 1 = b * M i 0)
    (hnonzero : ∃ i, M i 0 ≠ 0 ∨ M i 1 ≠ 0)
    (x y : ℤ) :
    (∀ i, M i 0 * x + M i 1 * y = 0) ↔
      ∃ k : ℤ, x = -b * k ∧ y = a * k :=
  integer_two_column_matrix_kernel_eq_zsmul_anchor_of_nonzero
    M (exists_bezout_of_int_gcd_eq_one hcoprime) hminor hnonzero x y

#print axioms integer_row_kernel_iff_anchor_of_nonzero
#print axioms integer_two_column_matrix_kernel_iff_anchor_of_nonzero
#print axioms integer_two_column_matrix_kernel_eq_zsmul_anchor_of_nonzero
#print axioms integer_two_column_matrix_kernel_eq_zsmul_anchor_of_nonzero_gcd_one

theorem integer_two_column_matrix_kernel_eq_zsmul_anchor
    {ι : Type*} (i₀ : ι) (M : Matrix ι (Fin 2) ℤ)
    {a b : ℤ}
    (hA₀ : M i₀ 0 = a) (hB₀ : M i₀ 1 = b)
    (hbez : ∃ u v : ℤ, u * a + v * b = 1)
    (hminor : ∀ i, a * M i 1 = b * M i 0)
    (x y : ℤ) :
    (∀ i, M i 0 * x + M i 1 * y = 0) ↔
      ∃ k : ℤ, x = -b * k ∧ y = a * k := by
  exact
    (integer_two_column_matrix_kernel_iff_anchor
      i₀ M hA₀ hB₀ hbez hminor x y).trans
    (integer_pair_kernel_iff_primitive_generator hbez)

/--
The gcd-one form of the matrix-kernel theorem. In particular, the integer
kernel is exactly the Z-span of (-b,a), not merely a rational line.
-/
theorem integer_two_column_matrix_kernel_eq_zsmul_anchor_of_gcd_one
    {ι : Type*} (i₀ : ι) (M : Matrix ι (Fin 2) ℤ)
    {a b : ℤ}
    (hA₀ : M i₀ 0 = a) (hB₀ : M i₀ 1 = b)
    (hcoprime : Int.gcd a b = 1)
    (hminor : ∀ i, a * M i 1 = b * M i 0)
    (x y : ℤ) :
    (∀ i, M i 0 * x + M i 1 * y = 0) ↔
      ∃ k : ℤ, x = -b * k ∧ y = a * k :=
  integer_two_column_matrix_kernel_eq_zsmul_anchor
    i₀ M hA₀ hB₀
    (exists_bezout_of_int_gcd_eq_one hcoprime) hminor x y

/-- A nonprimitive row (2,0) has kernel {(0,y)}, which is larger than the
    Z-span of its nonprimitive perpendicular vector (0,2). -/
theorem nonprimitive_row_kernel_counterexample :
    (2 : ℤ) * 0 + 0 * 1 = 0 ∧
      ¬ ∃ k : ℤ, (0 : ℤ) = -0 * k ∧ 1 = 2 * k := by
  constructor
  · norm_num
  · rintro ⟨k, _, hk⟩
    omega


/--
The old success-coordinate equation for a row forces that row to be
collinear with the primitive perpendicular direction (δ,-b₀).
-/
theorem endpoint_success_row_implies_anchor_minor
    {b₀ δ A B : ℤ}
    (hsuccess : A * b₀ + B * δ = 0) :
    δ * B = (-b₀) * A := by
  nlinarith [hsuccess]

/-- Family version of the success-coordinate to anchor-minor identity. -/
theorem endpoint_success_rows_imply_anchor_minors
    {ι : Type*} {b₀ δ : ℤ} (A B : ι → ℤ)
    (hsuccess : ∀ i, A i * b₀ + B i * δ = 0) :
    ∀ i, δ * B i = (-b₀) * A i := by
  intro i
  exact endpoint_success_row_implies_anchor_minor (hsuccess i)

/--
Endpoint-lattice specialization matching the Split–Machin notation.

The vector (b₀, δ) is assumed to be an old success relation, so every
source row annihilates it. The gcd-one condition makes the perpendicular
row direction (δ, -b₀) primitive. A nonzero source row rules out the
rank-zero case. Consequently the full integer kernel is exactly the
Z-span of the old success vector (b₀, δ).

This theorem isolates the precise source-specific inputs needed from the
Split–Machin endpoint map; it does not assume that a primitive row itself
occurs in the matrix.
-/
theorem integer_endpoint_kernel_from_primitive_success
    {ι : Type*} (M : Matrix ι (Fin 2) ℤ)
    {b₀ δ : ℤ}
    (hcoprime : Int.gcd b₀ δ = 1)
    (hsuccess : ∀ i, M i 0 * b₀ + M i 1 * δ = 0)
    (hnonzero : ∃ i, M i 0 ≠ 0 ∨ M i 1 ≠ 0)
    (x y : ℤ) :
    (∀ i, M i 0 * x + M i 1 * y = 0) ↔
      ∃ k : ℤ, x = b₀ * k ∧ y = δ * k := by
  obtain ⟨u, v, hbezBase⟩ :=
    exists_bezout_of_int_gcd_eq_one hcoprime
  have hbez : ∃ u' v' : ℤ, u' * δ + v' * (-b₀) = 1 := by
    refine ⟨v, -u, ?_⟩
    nlinarith [hbezBase]
  have hminor : ∀ i, δ * M i 1 = (-b₀) * M i 0 :=
    endpoint_success_rows_imply_anchor_minors
      (fun i => M i 0) (fun i => M i 1) hsuccess
  have h := integer_two_column_matrix_kernel_eq_zsmul_anchor_of_nonzero
    M hbez hminor hnonzero x y
  simpa only [neg_neg] using h


/--
Rearrange the integer pairing of a row functional with a matrix-column
combination. This exact finite-sum identity is the algebraic core of modular
dual certificates for integer column lattices.
-/
theorem integer_matrix_dual_sum_rearrange
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ)
    (s : Fin m → ℤ) (c : Fin n → ℤ) :
    (∑ i : Fin m, s i * (∑ j : Fin n, A i j * c j)) =
      ∑ j : Fin n, c j * (∑ i : Fin m, s i * A i j) := by
  classical
  calc
    _ = ∑ i : Fin m, ∑ j : Fin n, s i * (A i j * c j) := by
      simp only [Finset.mul_sum]
    _ = ∑ j : Fin n, ∑ i : Fin m, c j * (s i * A i j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = ∑ j : Fin n, c j * (∑ i : Fin m, s i * A i j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.mul_sum]

/--
A modular dual certificate excludes an integer column-lattice relation.

If a row functional s annihilates every column modulo q, but does not
annihilate the target vector modulo q, then the target cannot be an
integer linear combination of the columns. The modulus need not be prime;
this directly covers the prime-power certificates in Appendix D.
-/
theorem not_mem_integer_column_span_of_modular_dual
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ)
    (y : Fin m → ℤ) (q : ℤ) (s : Fin m → ℤ)
    (hcolumns : ∀ j : Fin n, q ∣ ∑ i : Fin m, s i * A i j)
    (htarget : ¬ q ∣ ∑ i : Fin m, s i * y i) :
    ¬ ∃ c : Fin n → ℤ,
        ∀ i : Fin m, y i = ∑ j : Fin n, A i j * c j := by
  rintro ⟨c, hc⟩
  apply htarget
  have hspanPairing :
      (∑ i : Fin m, s i * y i) =
        ∑ j : Fin n, c j * (∑ i : Fin m, s i * A i j) := by
    calc
      _ = ∑ i : Fin m, s i * (∑ j : Fin n, A i j * c j) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hc i]
      _ = _ := integer_matrix_dual_sum_rearrange A s c
  have hdiv :
      q ∣ ∑ j : Fin n, c j * (∑ i : Fin m, s i * A i j) := by
    refine Finset.dvd_sum fun j hj => ?_
    obtain ⟨k, hk⟩ := hcolumns j
    refine ⟨c j * k, ?_⟩
    rw [hk]
    ring
  rw [hspanPairing]
  exact hdiv

#print axioms integer_matrix_dual_sum_rearrange
#print axioms not_mem_integer_column_span_of_modular_dual

#print axioms endpoint_success_row_implies_anchor_minor
#print axioms endpoint_success_rows_imply_anchor_minors
#print axioms integer_endpoint_kernel_from_primitive_success

#print axioms integer_pair_kernel_iff_primitive_generator
#print axioms integer_two_column_matrix_kernel_eq_zsmul_anchor
#print axioms integer_two_column_matrix_kernel_eq_zsmul_anchor_of_gcd_one
#print axioms nonprimitive_row_kernel_counterexample

#print axioms exists_bezout_of_int_gcd_eq_one
#print axioms integer_two_column_matrix_kernel_iff_anchor
#print axioms nonprimitive_pair_counterexample

#print axioms integer_pair_multiple_of_gcd_one_and_determinant
#print axioms integer_row_kernel_iff_anchor
#print axioms integer_row_kernel_iff_anchor_of_gcd_one

end EPlusPiApproximation
