module
public import AlgebraicClosure
public import AlgebraicElements
public import AlgebraicFieldClosure
public import LindemannBasic
public import HermiteLindemannBridge
public import EPlusPi
public import SchanuelConditional
public import ApproximationCriteria

@[expose] public section

open Filter
open scoped Topology

/-!
# Central proof-dependency audit

The declarations below restate the project's key theorems with explicit types.
CI audits their transitive axiom dependencies, including the algebraic-closure
lemmas, the vendored Lindemann–Weierstrass proof, Mathlib's analytic estimate,
the Schanuel field-theory argument, the relative algebraic-elements field,
and finite-extension results.

No new mathematical assumption is introduced here. The open unconditional
e + pi target is intentionally not stated as a proved theorem.
-/

namespace ProofAudit

/-- The complex exponential value exp(1) is transcendental over ℤ. -/
theorem complex_e_transcendental :
    Transcendental ℤ (Complex.exp (1 : ℂ)) :=
  Complex.transcendental_e

/-- The real number π is transcendental over ℤ. -/
theorem real_pi_transcendental :
    Transcendental ℤ Real.pi :=
  Real.transcendental_pi

/-- The rational-base Hermite–Lindemann consequence for e. -/
theorem rational_e_transcendental :
    Transcendental ℚ (Real.exp 1) :=
  HermiteLindemannBridge.transcendental_e

/-- The rational-base Lindemann consequence for π. -/
theorem rational_pi_transcendental :
    Transcendental ℚ Real.pi :=
  HermiteLindemannBridge.transcendental_pi

/-- Unconditionally, at least one of e+π and eπ is transcendental. -/
theorem e_add_pi_or_mul_transcendental :
    Transcendental ℚ ePlusPi ∨ Transcendental ℚ eTimesPi :=
  _root_.e_add_pi_or_mul_transcendental

/-- Schanuel's conjecture conditionally implies transcendence of e+π. -/
theorem schanuel_implies_e_plus_pi_transcendental
    (hSC : SchanuelConditional.SchanuelConjecture) :
    Transcendental ℚ ePlusPi :=
  SchanuelConditional.transcendental_ePlusPi_of_schanuel hSC

/-- Super-polynomial decay of nonzero integer forms forces transcendence. -/
theorem superpolynomial_forms_imply_transcendence
    {x : ℝ} {a : ℕ → ℕ} {b : ℕ → ℤ}
    (ha : Tendsto a atTop atTop)
    (hnz : ∀ᶠ n : ℕ in atTop,
      EPlusPiApproximation.integerLinearFormValue x (a n) (b n) ≠ 0)
    (hsmall : ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
      |EPlusPiApproximation.integerLinearFormValue x (a n) (b n)| <
        1 / (EPlusPiApproximation.integerLinearFormHeight (a n) (b n) : ℝ) ^ k) :
    Transcendental ℚ x :=
  EPlusPiApproximation.transcendental_of_superpolynomial_integer_linear_forms
    ha hnz hsmall

/-- A nonzero integer-linear-form sequence tending to zero proves irrationality. -/
theorem integer_forms_tending_to_zero_imply_irrationality
    {x : ℝ} {A B : ℕ → ℤ}
    (hnz : ∀ᶠ n : ℕ in atTop,
      EPlusPiApproximation.signedIntegerLinearFormValue x (A n) (B n) ≠ 0)
    (hsmall : Tendsto
      (fun n : ℕ =>
        |EPlusPiApproximation.signedIntegerLinearFormValue x (A n) (B n)|)
      atTop (𝓝 0)) :
    Irrational x :=
  EPlusPiApproximation.irrational_of_tendsto_zero_signed_integer_linear_forms
    hnz hsmall

/-! ## Relative algebraic closure as an intermediate field -/

noncomputable def algebraic_elements_field_structure
    (K E : Type*) [Field K] [Field E] [Algebra K E] :
    Field (G.AlgebraicElements.field K E) :=
  G.AlgebraicElements.field_structure K E

theorem algebraic_elements_mem_iff
    (K E : Type*) [Field K] [Field E] [Algebra K E] {x : E} :
    x ∈ G.AlgebraicElements.field K E ↔ IsAlgebraic K x :=
  G.AlgebraicElements.mem_iff K E

theorem algebraic_elements_carrier_eq
    (K E : Type*) [Field K] [Field E] [Algebra K E] :
    G.AlgebraicElements.carrier K E =
      (G.AlgebraicElements.field K E : Set E) :=
  G.AlgebraicElements.carrier_eq K E

theorem algebraic_elements_add_closed
    (K E : Type*) [Field K] [Field E] [Algebra K E] {x y : E}
    (hx : IsAlgebraic K x) (hy : IsAlgebraic K y) :
    IsAlgebraic K (x + y) :=
  G.AlgebraicElements.add_closed K E hx hy

theorem algebraic_elements_neg_closed
    (K E : Type*) [Field K] [Field E] [Algebra K E] {x : E}
    (hx : IsAlgebraic K x) :
    IsAlgebraic K (-x) :=
  G.AlgebraicElements.neg_closed K E hx

theorem algebraic_elements_sub_closed
    (K E : Type*) [Field K] [Field E] [Algebra K E] {x y : E}
    (hx : IsAlgebraic K x) (hy : IsAlgebraic K y) :
    IsAlgebraic K (x - y) :=
  G.AlgebraicElements.sub_closed K E hx hy

theorem algebraic_elements_mul_closed
    (K E : Type*) [Field K] [Field E] [Algebra K E] {x y : E}
    (hx : IsAlgebraic K x) (hy : IsAlgebraic K y) :
    IsAlgebraic K (x * y) :=
  G.AlgebraicElements.mul_closed K E hx hy

theorem algebraic_elements_inv_closed
    (K E : Type*) [Field K] [Field E] [Algebra K E] {x : E}
    (hx : IsAlgebraic K x) :
    IsAlgebraic K x⁻¹ :=
  G.AlgebraicElements.inv_closed K E hx

theorem algebraic_elements_div_closed
    (K E : Type*) [Field K] [Field E] [Algebra K E] {x y : E}
    (hx : IsAlgebraic K x) (hy : IsAlgebraic K y) :
    IsAlgebraic K (x / y) :=
  G.AlgebraicElements.div_closed K E hx hy

theorem algebraic_elements_zpow_closed
    (K E : Type*) [Field K] [Field E] [Algebra K E] {x : E}
    (hx : IsAlgebraic K x) (n : ℤ) :
    IsAlgebraic K (x ^ n) :=
  G.AlgebraicElements.zpow_closed K E hx n

theorem algebraic_elements_field_is_algebraic
    (K E : Type*) [Field K] [Field E] [Algebra K E] :
    Algebra.IsAlgebraic K (G.AlgebraicElements.field K E) :=
  G.AlgebraicElements.field_is_algebraic K E

theorem algebraic_elements_maximality
    (K E : Type*) [Field K] [Field E] [Algebra K E]
    (L : IntermediateField K E) :
    L ≤ G.AlgebraicElements.field K E ↔
      Algebra.IsAlgebraic K L :=
  G.AlgebraicElements.maximality K E L

theorem algebraic_elements_isAlgClosure_of_algClosed_ambient
    (K E : Type*) [Field K] [Field E] [Algebra K E] [IsAlgClosed E] :
    IsAlgClosure K (G.AlgebraicElements.field K E) :=
  G.AlgebraicElements.isAlgClosure_of_algClosed_ambient K E

theorem algebraic_elements_field_isAlgClosed
    (K E : Type*) [Field K] [Field E] [Algebra K E] [IsAlgClosed E] :
    IsAlgClosed (G.AlgebraicElements.field K E) :=
  G.AlgebraicElements.field_isAlgClosed K E

theorem algebraic_elements_every_polynomial_splits
    (K E : Type*) [Field K] [Field E] [Algebra K E] [IsAlgClosed E]
    (p : Polynomial (G.AlgebraicElements.field K E)) :
    p.Splits :=
  G.AlgebraicElements.every_polynomial_splits K E p

theorem algebraic_elements_exists_root
    (K E : Type*) [Field K] [Field E] [Algebra K E] [IsAlgClosed E]
    (p : Polynomial (G.AlgebraicElements.field K E)) (hp : p.degree ≠ 0) :
    ∃ x : G.AlgebraicElements.field K E, IsRoot p x :=
  G.AlgebraicElements.exists_root K E p hp

theorem algebraic_elements_uniqueness_up_to_algEquiv
    (K : Type*) [Field K]
    (A B : Type*) [Field A] [Field B]
    [Algebra K A] [Algebra K B]
    [IsTorsionFree K A] [IsTorsionFree K B]
    [IsAlgClosure K A] [IsAlgClosure K B] :
    Nonempty (A ≃ₐ[K] B) :=
  G.AlgebraicElements.uniqueness_up_to_algEquiv K A B

/-! ## Finite generated algebraic extensions -/

theorem finiteDimensional_adjoin_of_algebraic
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    {S : Set K} [Finite S] (hS : ∀ x ∈ S, IsAlgebraic F x) :
    FiniteDimensional F (IntermediateField.adjoin F S) :=
  AlgebraicFieldClosure.finiteDimensional_adjoin_of_algebraic hS

theorem algebraic_extension_of_finiteDimensional
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] :
    Algebra.IsAlgebraic F K :=
  AlgebraicFieldClosure.algebraic_extension_of_finiteDimensional

theorem finite_iff_essFiniteType_and_algebraic
    {F K : Type*} [Field F] [Field K] [Algebra F K] :
    Module.Finite F K ↔
      Algebra.EssFiniteType F K ∧ Algebra.IsAlgebraic F K :=
  AlgebraicFieldClosure.finite_iff_essFiniteType_and_algebraic

end ProofAudit
