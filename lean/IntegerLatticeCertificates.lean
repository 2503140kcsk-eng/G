module
public import Mathlib
public import Mathlib.LinearAlgebra.FreeModule.Int
public import IntegerEndpointLattice

@[expose] public section

/-!
# Exact certificates for integer column lattices

This file separates certificate data from the propositions they certify.
A membership witness is checked by an exact integer matrix equation. A
nonmembership witness is a modular dual functional. The prime-power and
localized variants match the two different local proof patterns in Appendix D.

The final section records the denominator/content factor that survives
integerization and primitive reduction inside one fixed saturated lattice.
It deliberately does not infer decay from rational approximation error alone.
-/

namespace EPlusPiApproximation

/-- An exact certificate that y belongs to the integer column lattice of A. -/
structure IntegerLatticeMembershipCertificate
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (y : Fin m → ℤ) where
  coefficients : Fin n → ℤ
  verifies : ∀ i, y i = ∑ j, A i j * coefficients j

/-- Soundness of an exact integer membership certificate. -/
theorem IntegerLatticeMembershipCertificate.sound
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℤ} {y : Fin m → ℤ}
    (C : IntegerLatticeMembershipCertificate A y) :
    ∃ c : Fin n → ℤ, ∀ i, y i = ∑ j, A i j * c j :=
  ⟨C.coefficients, C.verifies⟩

/-- A modular dual certificate for exclusion from an integer column lattice. -/
structure IntegerLatticeNonmembershipCertificate
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (y : Fin m → ℤ) where
  modulus : ℤ
  modulus_ne_zero : modulus ≠ 0
  separator : Fin m → ℤ
  annihilates_columns :
    ∀ j, modulus ∣ ∑ i, separator i * A i j
  detects_target : ¬ modulus ∣ ∑ i, separator i * y i

/-- Soundness of a modular dual nonmembership certificate. -/
theorem IntegerLatticeNonmembershipCertificate.sound
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℤ} {y : Fin m → ℤ}
    (C : IntegerLatticeNonmembershipCertificate A y) :
    ¬ ∃ c : Fin n → ℤ, ∀ i, y i = ∑ j, A i j * c j :=
  not_mem_integer_column_span_of_modular_dual
    A y C.modulus C.separator C.annihilates_columns C.detects_target

/-- The Appendix-D nonmembership format: a dual functional modulo p^k. -/
structure PrimePowerNonmembershipCertificate
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (y : Fin m → ℤ)
    (p : ℕ) where
  prime : p.Prime
  exponent : ℕ
  exponent_pos : 0 < exponent
  separator : Fin m → ℤ
  annihilates_columns :
    ∀ j, ((p : ℤ) ^ exponent) ∣ ∑ i, separator i * A i j
  detects_target :
    ¬ ((p : ℤ) ^ exponent) ∣ ∑ i, separator i * y i

/-- Every prime-power dual certificate proves nonmembership over ℤ. -/
theorem PrimePowerNonmembershipCertificate.sound
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℤ} {y : Fin m → ℤ}
    {p : ℕ} (C : PrimePowerNonmembershipCertificate A y p) :
    ¬ ∃ c : Fin n → ℤ, ∀ i, y i = ∑ j, A i j * c j :=
  not_mem_integer_column_span_of_modular_dual
    A y ((p : ℤ) ^ C.exponent) C.separator
    C.annihilates_columns C.detects_target

/--
A localized membership witness at the prime p.

It consists of an integer denominator which is a unit at p and an exact
integer equation denominator * y = A * coefficients. This is the concrete
fraction-free form of membership in the column lattice after localizing at
the prime ideal (p).
-/
structure PrimeLocalizedMembershipCertificate
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (y : Fin m → ℤ)
    (p : ℕ) where
  prime : p.Prime
  denominator : ℤ
  denominator_is_p_unit : ¬ (p : ℤ) ∣ denominator
  coefficients : Fin n → ℤ
  verifies :
    ∀ i, denominator * y i = ∑ j, A i j * coefficients j

/-- The fraction-free witness contained in a localized membership certificate. -/
theorem PrimeLocalizedMembershipCertificate.sound
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℤ} {y : Fin m → ℤ}
    {p : ℕ} (C : PrimeLocalizedMembershipCertificate A y p) :
    ∃ u : ℤ, (¬ (p : ℤ) ∣ u) ∧
      ∃ c : Fin n → ℤ, ∀ i, u * y i = ∑ j, A i j * c j :=
  ⟨C.denominator, C.denominator_is_p_unit, C.coefficients, C.verifies⟩

/-! ## Smith diagonal factors and full-rank lattice index -/

/-- The diagonal coefficients in Mathlib's Smith-normal-form basis for L. -/
noncomputable def smithDiagonalCoefficients
    {m : ℕ} (L : Submodule ℤ (Fin m → ℤ))
    (hRank : Module.finrank ℤ L = m) : Fin m → ℤ :=
  Submodule.smithNormalFormCoeffs
    (Module.Free.chooseBasis ℤ (Fin m → ℤ)) hRank

/--
For a full-rank sublattice of ℤ^m, its additive index is the product of the
absolute values of its Smith diagonal coefficients.

Mathlib supplies the Smith basis and the index formula for a Smith-normal-form
submodule; this theorem specializes it to the standard free module Fin m → ℤ.
-/
theorem index_eq_product_smith_diagonal_coefficients
    {m : ℕ} (L : Submodule ℤ (Fin m → ℤ))
    (hRank : Module.finrank ℤ L = m) :
    L.toAddSubgroup.index =
      ∏ i : Fin m, Int.natAbs (smithDiagonalCoefficients L hRank i) := by
  classical
  let b : Basis (Fin m) ℤ (Fin m → ℤ) :=
    Module.Free.chooseBasis ℤ (Fin m → ℤ)
  let snf := L.smithNormalFormOfRankEq b hRank
  rw [snf.toAddSubgroup_index_eq_ite]
  simp [smithDiagonalCoefficients, b, snf,
    Ideal.span_singleton_toAddSubgroup_eq_zmultiples,
    Int.index_zmultiples]

/-! ## Fixed primitive lattice and denominator clearing -/

/--
A saturated (primitive) integer lattice: if a nonzero integer multiple of an
integer vector belongs to L, then the vector itself belongs to L.
This is the torsion-free quotient characterization of a primitive sublattice.
-/
def IsPrimitiveIntegerLattice
    {m : ℕ} (L : Submodule ℤ (Fin m → ℤ)) : Prop :=
  ∀ ⦃d : ℤ⦄, d ≠ 0 → ∀ v : Fin m → ℤ, d • v ∈ L → v ∈ L

/--
A rational vector together with its denominator-cleared integer vector and
its primitive integer representative.

content is the exact positive common factor removed from the cleared vector:
the quotient vector is primitive in the divisibility sense. cleared_mem
records that integerization occurs inside the same fixed lattice L.
-/
structure PrimitiveIntegerization
    {m : ℕ} (L : Submodule ℤ (Fin m → ℤ)) (x : Fin m → ℚ) where
  denominator : ℕ
  denominator_pos : 0 < denominator
  clearedVector : Fin m → ℤ
  clears_denominators :
    ∀ i, (clearedVector i : ℚ) = (denominator : ℚ) * x i
  content : ℕ
  content_pos : 0 < content
  primitiveVector : Fin m → ℤ
  cleared_eq_content_mul_primitive :
    ∀ i, clearedVector i = (content : ℤ) * primitiveVector i
  primitive :
    ∀ d : ℕ, 0 < d →
      (∀ i, (d : ℤ) ∣ primitiveVector i) → d = 1
  cleared_mem : clearedVector ∈ L

/-- Primitive reduction remains in the same lattice when that lattice is saturated. -/
theorem PrimitiveIntegerization.primitive_mem
    {m : ℕ} {L : Submodule ℤ (Fin m → ℤ)} {x : Fin m → ℚ}
    (C : PrimitiveIntegerization L x)
    (hL : IsPrimitiveIntegerLattice L) :
    C.primitiveVector ∈ L := by
  have hcontent : (C.content : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt C.content_pos)
  have hdecomp :
      (C.content : ℤ) • C.primitiveVector = C.clearedVector := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact (C.cleared_eq_content_mul_primitive i).symm
  exact hL hcontent C.primitiveVector (by rw [hdecomp]; exact C.cleared_mem)

/-- Evaluation of a real linear functional on an integer vector. -/
def integerVectorPairing
    {m : ℕ} (a : Fin m → ℝ) (v : Fin m → ℤ) : ℝ :=
  ∑ i, a i * (v i : ℝ)

/-- Evaluation of the same coefficient vector on a rational vector. -/
def rationalVectorPairing
    {m : ℕ} (a : Fin m → ℝ) (v : Fin m → ℚ) : ℝ :=
  ∑ i, a i * (v i : ℝ)

/-- Integer-vector evaluation respects integer scalar multiplication. -/
theorem integerVectorPairing_smul
    {m : ℕ} (a : Fin m → ℝ) (d : ℤ) (v : Fin m → ℤ) :
    integerVectorPairing a (d • v) =
      (d : ℝ) * integerVectorPairing a v := by
  classical
  unfold integerVectorPairing
  simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/--
Clearing a common denominator multiplies the rational evaluation by that
denominator, exactly and without approximation.
-/
theorem PrimitiveIntegerization.cleared_pairing
    {m : ℕ} {L : Submodule ℤ (Fin m → ℤ)} {x : Fin m → ℚ}
    (C : PrimitiveIntegerization L x) (a : Fin m → ℝ) :
    integerVectorPairing a C.clearedVector =
      (C.denominator : ℝ) * rationalVectorPairing a x := by
  classical
  unfold integerVectorPairing rationalVectorPairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hcast : (C.clearedVector i : ℝ) =
      (C.denominator : ℝ) * (x i : ℝ) := by
    exact_mod_cast C.clears_denominators i
  rw [hcast]
  ring

/--
The exact scaling identity after removing the common content. The primitive
error is the original rational error multiplied by denominator / content.
Thus the denominator/content ratio is the precise quantity that must be
controlled; rational error tending to zero by itself is insufficient.
-/
theorem PrimitiveIntegerization.primitive_pairing_eq_scaled_rational
    {m : ℕ} {L : Submodule ℤ (Fin m → ℤ)} {x : Fin m → ℚ}
    (C : PrimitiveIntegerization L x) (a : Fin m → ℝ) :
    integerVectorPairing a C.primitiveVector =
      ((C.denominator : ℝ) / (C.content : ℝ)) *
        rationalVectorPairing a x := by
  have hdecomp :
      (C.content : ℤ) • C.primitiveVector = C.clearedVector := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact (C.cleared_eq_content_mul_primitive i).symm
  have hprimitive :
      integerVectorPairing a C.clearedVector =
        (C.content : ℝ) * integerVectorPairing a C.primitiveVector := by
    calc
      integerVectorPairing a C.clearedVector =
          integerVectorPairing a ((C.content : ℤ) • C.primitiveVector) := by
            rw [hdecomp]
      _ = (C.content : ℝ) * integerVectorPairing a C.primitiveVector :=
        integerVectorPairing_smul a (C.content : ℤ) C.primitiveVector
  have hclear := C.cleared_pairing a
  have hrel :
      (C.content : ℝ) * integerVectorPairing a C.primitiveVector =
        (C.denominator : ℝ) * rationalVectorPairing a x :=
    hprimitive.symm.trans hclear
  have hc : (C.content : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt C.content_pos)
  calc
    integerVectorPairing a C.primitiveVector =
        (C.content : ℝ) * integerVectorPairing a C.primitiveVector /
          (C.content : ℝ) := by
            field_simp
    _ = (C.denominator : ℝ) * rationalVectorPairing a x /
          (C.content : ℝ) := by rw [hrel]
    _ = ((C.denominator : ℝ) / (C.content : ℝ)) *
          rationalVectorPairing a x := by ring

/--
A convergence transfer theorem for one fixed primitive lattice.

The hypothesis is the cross-weighted error after clearing denominators and
removing content. Under precisely this quantitative condition, the primitive
integer errors converge to zero. The saturation hypothesis ensures that all
primitive representatives stay in the same lattice L.
-/
theorem PrimitiveIntegerization.tendsto_primitive_errors_of_weighted
    {m : ℕ} {L : Submodule ℤ (Fin m → ℤ)}
    {x : ℕ → (Fin m → ℚ)} (C : ∀ n, PrimitiveIntegerization L (x n))
    (hL : IsPrimitiveIntegerLattice L) (a : Fin m → ℝ)
    (hweighted : Tendsto
      (fun n =>
        ((C n).denominator : ℝ) / ((C n).content : ℝ) *
          |rationalVectorPairing a (x n)|) atTop (𝓝 0)) :
    Tendsto
      (fun n => |integerVectorPairing a (C n).primitiveVector|)
      atTop (𝓝 0) := by
  have hsame : ∀ n, (C n).primitiveVector ∈ L := by
    intro n
    exact (C n).primitive_mem hL
  have hfun :
      (fun n => |integerVectorPairing a (C n).primitiveVector|) =
        (fun n =>
          ((C n).denominator : ℝ) / ((C n).content : ℝ) *
            |rationalVectorPairing a (x n)|) := by
    funext n
    rw [(C n).primitive_pairing_eq_scaled_rational]
    rw [abs_mul, abs_of_pos]
    exact div_pos
      (Nat.cast_pos.mpr ((C n).denominator_pos))
      (Nat.cast_pos.mpr ((C n).content_pos))
  rw [hfun]
  exact hweighted

#print axioms IntegerLatticeMembershipCertificate.sound
#print axioms IntegerLatticeNonmembershipCertificate.sound
#print axioms PrimePowerNonmembershipCertificate.sound
#print axioms PrimeLocalizedMembershipCertificate.sound
#print axioms index_eq_product_smith_diagonal_coefficients
#print axioms PrimitiveIntegerization.primitive_mem
#print axioms PrimitiveIntegerization.primitive_pairing_eq_scaled_rational
#print axioms PrimitiveIntegerization.tendsto_primitive_errors_of_weighted

end EPlusPiApproximation
