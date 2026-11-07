import Mathlib.RingTheory.Algebraic.Integral

/-!
# Closure properties of algebraic elements

This development packages Mathlib's algebraic-closure subalgebra and
algebraicity-descent machinery into reusable theorem statements.

The general root theorem uses the following proof architecture:
1. Put every coefficient into the subalgebra of elements algebraic over K.
2. Reinterpret the original polynomial as a polynomial over that subalgebra.
3. The root is algebraic over the intermediate subalgebra.
4. Restrict scalars along the algebraic extension back to K.

The file introduces no axioms, sorry, or admit.
-/

namespace AlgebraicNumberClosureFormalization

open Polynomial

/-! ## Addition and multiplication -/

/-- The sum of two elements algebraic over a field is algebraic. -/
theorem isAlgebraic_add
    {K A : Type*} [Field K] [Field A] [Algebra K A]
    {x y : A} (hx : IsAlgebraic K x) (hy : IsAlgebraic K y) :
    IsAlgebraic K (x + y) :=
  hx.add hy

/-- The product of two elements algebraic over a field is algebraic. -/
theorem isAlgebraic_mul
    {K A : Type*} [Field K] [Field A] [Algebra K A]
    {x y : A} (hx : IsAlgebraic K x) (hy : IsAlgebraic K y) :
    IsAlgebraic K (x * y) :=
  hx.mul hy

/-- The algebraic elements inside a field extension form a subalgebra. -/
def algebraicNumbersSubalgebra (K A : Type*) [Field K] [Field A] [Algebra K A] :
    Subalgebra K A :=
  Subalgebra.algebraicClosure K A

@[simp]
theorem mem_algebraicNumbersSubalgebra
    {K A : Type*} [Field K] [Field A] [Algebra K A] {x : A} :
    x ∈ algebraicNumbersSubalgebra K A ↔ IsAlgebraic K x :=
  Subalgebra.mem_algebraicClosure

/-- Closure under addition, expressed internally in the algebraic-number subalgebra. -/
theorem algebraicNumbers_add
    {K A : Type*} [Field K] [Field A] [Algebra K A]
    {x y : A}
    (hx : x ∈ algebraicNumbersSubalgebra K A)
    (hy : y ∈ algebraicNumbersSubalgebra K A) :
    x + y ∈ algebraicNumbersSubalgebra K A :=
  (algebraicNumbersSubalgebra K A).add_mem hx hy

/-- Closure under multiplication, expressed internally in the algebraic-number subalgebra. -/
theorem algebraicNumbers_mul
    {K A : Type*} [Field K] [Field A] [Algebra K A]
    {x y : A}
    (hx : x ∈ algebraicNumbersSubalgebra K A)
    (hy : y ∈ algebraicNumbersSubalgebra K A) :
    x * y ∈ algebraicNumbersSubalgebra K A :=
  (algebraicNumbersSubalgebra K A).mul_mem hx hy

/-! ## Roots of polynomials with algebraic coefficients -/

/--
If every coefficient of a nonzero polynomial over A is algebraic over K,
then every root of that polynomial in A is algebraic over K.

The proof uses the subalgebra of all elements algebraic over K as the
intermediate coefficient ring. It therefore works for arbitrary finite-degree
polynomials and does not require explicitly constructing minimal polynomials.
-/
theorem isAlgebraic_of_root_of_algebraic_coefficients
    {K A : Type*} [Field K] [Field A] [Algebra K A]
    {p : A[X]} {x : A}
    (hp : p ≠ 0)
    (hcoeff : ∀ n : ℕ, IsAlgebraic K (p.coeff n))
    (hroot : aeval x p = 0) :
    IsAlgebraic K x := by
  classical

  -- All algebraic elements in A form a subalgebra over K.
  let S : Subalgebra K A := Subalgebra.algebraicClosure K A

  -- Every coefficient of p belongs to that intermediate subalgebra.
  have hcoeffS : (↑p.coeffs : Set A) ⊆ S.toSubring := by
    intro c hc
    obtain ⟨n, hn, rfl⟩ := mem_coeffs_iff.mp hc
    exact (Subalgebra.mem_algebraicClosure).2 (hcoeff n)

  -- Reinterpret p as a polynomial over S.
  let q : S[X] := p.toSubring S.toSubring hcoeffS

  have hq_map : q.map (algebraMap S A) = p := by
    simpa [q, Subalgebra.algebraMap_eq] using
      (p.map_toSubring S.toSubring hcoeffS)

  have hq_ne_map : q.map (algebraMap S A) ≠ 0 := by
    rw [hq_map]
    exact hp

  have hq_ne : q ≠ 0 :=
    (Polynomial.map_ne_zero_iff (f := algebraMap S A) (p := q)
      Subtype.val_injective).mp hq_ne_map

  -- The root equation transfers to the polynomial over S.
  have hq_root : aeval x q = 0 := by
    rw [← eval_map_algebraMap, hq_map, aeval_def]
    exact hroot

  have hxS : IsAlgebraic S x := ⟨q, hq_ne, hq_root⟩

  -- Mathlib knows that S/K is algebraic, so algebraicity descends to K.
  exact hxS.restrictScalars K

/-! ## A reusable algebraic-tower lemma -/

/--
If S is algebraic over K and x is algebraic over S, then x is algebraic
over K. The no-zero-divisors hypothesis on S is the standard condition in
Mathlib's scalar-restriction theorem.
-/
theorem isAlgebraic_of_root_over_algebraic_extension
    {K S A : Type*} [CommRing K] [CommRing S] [Ring A]
    [Algebra K S] [Algebra S A] [Algebra K A] [IsScalarTower K S A]
    [NoZeroDivisors S] [Algebra.IsAlgebraic K S]
    {p : S[X]} {x : A}
    (hp : p ≠ 0)
    (hroot : aeval x p = 0) :
    IsAlgebraic K x := by
  exact (show IsAlgebraic S x from ⟨p, hp, hroot⟩).restrictScalars K

/-!
## Kernel audit

The CI workflow runs axiom-audit on the AlgebraicClosure library. The
following commands also make the dependencies of the principal declarations
visible in the Lean build log.
-/
#print axioms isAlgebraic_add
#print axioms isAlgebraic_mul
#print axioms isAlgebraic_of_root_of_algebraic_coefficients
#print axioms isAlgebraic_of_root_over_algebraic_extension

end AlgebraicNumberClosureFormalization
