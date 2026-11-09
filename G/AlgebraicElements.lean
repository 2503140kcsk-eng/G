module

public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# The field of algebraic elements and its algebraic-closure structure

For a field extension E / K, the elements of E algebraic over K
form the relative algebraic closure algebraicClosure K E.

The key design is to represent the set as an IntermediateField, rather
than re-prove the field axioms separately. Its carrier is identified with
IsAlgebraic K, so the ordinary field operations yield the requested
closure theorems. If E is algebraically closed, mathlib's construction
also supplies the full IsAlgClosure structure.
-/

noncomputable section

universe u v w

namespace G.AlgebraicElements

open Polynomial Module

variable (K : Type u) (E : Type v)
variable [Field K] [Field E] [Algebra K E]

/-- The subfield of E consisting of exactly the elements algebraic over K. -/
abbrev field : IntermediateField K E :=
  algebraicClosure K E

/-- The algebraic elements carry the inherited field structure. -/
def field_structure : Field (field K E) :=
  inferInstance

/-- Membership in this intermediate field is equivalent to algebraicity. -/
theorem mem_iff {x : E} :
    x ∈ field K E ↔ IsAlgebraic K x := by
  change x ∈ algebraicClosure K E ↔ IsAlgebraic K x
  exact mem_algebraicClosure_iff

/-- The carrier of the field is precisely the set of algebraic elements. -/
def carrier : Set E := {x | IsAlgebraic K x}

theorem carrier_eq :
    carrier K E = (field K E : Set E) := by
  ext x
  exact (mem_iff K E).symm

/-- Algebraic elements are closed under addition. -/
theorem add_closed {x y : E}
    (hx : IsAlgebraic K x) (hy : IsAlgebraic K y) :
    IsAlgebraic K (x + y) :=
  (mem_iff K E).mp <|
    (field K E).add_mem ((mem_iff K E).mpr hx) ((mem_iff K E).mpr hy)

/-- Algebraic elements are closed under additive inverses. -/
theorem neg_closed {x : E}
    (hx : IsAlgebraic K x) :
    IsAlgebraic K (-x) :=
  (mem_iff K E).mp <|
    (field K E).neg_mem ((mem_iff K E).mpr hx)

/-- Algebraic elements are closed under subtraction. -/
theorem sub_closed {x y : E}
    (hx : IsAlgebraic K x) (hy : IsAlgebraic K y) :
    IsAlgebraic K (x - y) :=
  (mem_iff K E).mp <|
    (field K E).sub_mem ((mem_iff K E).mpr hx) ((mem_iff K E).mpr hy)

/-- Algebraic elements are closed under multiplication. -/
theorem mul_closed {x y : E}
    (hx : IsAlgebraic K x) (hy : IsAlgebraic K y) :
    IsAlgebraic K (x * y) :=
  (mem_iff K E).mp <|
    (field K E).mul_mem ((mem_iff K E).mpr hx) ((mem_iff K E).mpr hy)

/-- The inverse of every algebraic element is algebraic, including the zero case. -/
theorem inv_closed {x : E}
    (hx : IsAlgebraic K x) :
    IsAlgebraic K x⁻¹ :=
  (mem_iff K E).mp <|
    (field K E).inv_mem ((mem_iff K E).mpr hx)

/-- Algebraic elements are closed under division. -/
theorem div_closed {x y : E}
    (hx : IsAlgebraic K x) (hy : IsAlgebraic K y) :
    IsAlgebraic K (x / y) :=
  (mem_iff K E).mp <|
    (field K E).div_mem ((mem_iff K E).mpr hx) ((mem_iff K E).mpr hy)

/-- Algebraic elements are closed under all integer powers. -/
theorem zpow_closed {x : E}
    (hx : IsAlgebraic K x) (n : ℤ) :
    IsAlgebraic K (x ^ n) :=
  (mem_iff K E).mp <|
    (field K E).pow_mem ((mem_iff K E).mpr hx) n

/-- The relative algebraic closure is an algebraic field extension of the base. -/
theorem field_is_algebraic :
    Algebra.IsAlgebraic K (field K E) := by
  infer_instance

/-- Maximality: every algebraic intermediate field lies in the algebraic-elements field. -/
theorem maximality (L : IntermediateField K E) :
    L ≤ field K E ↔ Algebra.IsAlgebraic K L := by
  simpa [field] using (le_algebraicClosure_iff K E L)

/-- If the ambient extension field is algebraically closed, the relative closure
is an algebraic closure of the base field. -/
theorem isAlgClosure_of_algClosed_ambient [IsAlgClosed E] :
    IsAlgClosure K (field K E) := by
  simpa [field] using (algebraicClosure.isAlgClosure K E)

/-- In particular, the field of algebraic elements is itself algebraically closed
when the ambient extension field is algebraically closed. -/
theorem field_isAlgClosed [IsAlgClosed E] :
    IsAlgClosed (field K E) :=
  (isAlgClosure_of_algClosed_ambient K E).isAlgClosed

/-- Every polynomial over the algebraic-elements field splits when the ambient
extension field is algebraically closed. -/
theorem every_polynomial_splits [IsAlgClosed E]
    (p : Polynomial (field K E)) :
    p.Splits :=
  (field_isAlgClosed K E).splits p

/-- Every nonconstant polynomial over the algebraic-elements field has a root. -/
theorem exists_root [IsAlgClosed E]
    (p : Polynomial (field K E)) (hp : p.degree ≠ 0) :
    ∃ x : field K E, IsRoot p x :=
  @IsAlgClosed.exists_root (field K E) inferInstance (field_isAlgClosed K E) p hp

/-- Any two algebraic closures of the same base field are isomorphic over that field. -/
theorem uniqueness_up_to_algEquiv
    (A B : Type w)
    [Field A] [Field B]
    [Algebra K A] [Algebra K B]
    [IsTorsionFree K A] [IsTorsionFree K B]
    [IsAlgClosure K A] [IsAlgClosure K B] :
    Nonempty (A ≃ₐ[K] B) :=
  ⟨IsAlgClosure.equiv K A B⟩

end G.AlgebraicElements
