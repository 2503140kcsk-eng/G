module
public import AlgebraicClosure
public import AlgebraicElements
public import AlgebraicFieldClosure
public import LindemannBasic
public import HermiteLindemannBridge
public import EPlusPi
public import SchanuelConditional
public import ApproximationCriteria
public import PairedApproximationCriteria
public import MixedKernelQuotient

@[expose] public section

open Filter Module Polynomial
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
    Transcendental ℚ (Real.exp 1 + Real.pi) ∨
      Transcendental ℚ (Real.exp 1 * Real.pi) := by
  simpa [ePlusPi, eTimesPi] using _root_.e_add_pi_or_mul_transcendental

/-- Schanuel's conjecture conditionally implies transcendence of e+π. -/
theorem schanuel_implies_e_plus_pi_transcendental
    (hSC : ProofAuditDefs.SchanuelConjecture) :
    Transcendental ℚ (Real.exp 1 + Real.pi) := by
  have hSC' : SchanuelConditional.SchanuelConjecture := hSC
  simpa [ePlusPi] using
    SchanuelConditional.transcendental_ePlusPi_of_schanuel hSC'

/-- Super-polynomial decay of nonzero integer forms forces transcendence. -/
theorem superpolynomial_forms_imply_transcendence
    {x : ℝ} {a : ℕ → ℕ} {b : ℕ → ℤ}
    (ha : Tendsto a atTop atTop)
    (hnz : ∀ᶠ n : ℕ in atTop,
      (a n : ℝ) * x + (b n : ℝ) ≠ 0)
    (hsmall : ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
      |(a n : ℝ) * x + (b n : ℝ)| <
        1 / ((max (a n) (b n).natAbs : ℕ) : ℝ) ^ k) :
    Transcendental ℚ x := by
  simpa [EPlusPiApproximation.integerLinearFormValue,
    EPlusPiApproximation.integerLinearFormHeight] using
    EPlusPiApproximation.transcendental_of_superpolynomial_integer_linear_forms
      ha hnz hsmall

/-- A nonzero integer-linear-form sequence tending to zero proves irrationality. -/
theorem integer_forms_tending_to_zero_imply_irrationality
    {x : ℝ} {A B : ℕ → ℤ}
    (hnz : ∀ᶠ n : ℕ in atTop,
      (A n : ℝ) * x + (B n : ℝ) ≠ 0)
    (hsmall : Tendsto
      (fun n : ℕ => |(A n : ℝ) * x + (B n : ℝ)|)
      atTop (𝓝 0)) :
    Irrational x := by
  simpa [EPlusPiApproximation.signedIntegerLinearFormValue] using
    EPlusPiApproximation.irrational_of_tendsto_zero_signed_integer_linear_forms
      hnz hsmall

theorem paired_integer_forms_tending_to_zero_imply_irrationality
    {x : ℝ} {A C : ℕ → ℤ}
    (hdet : ∀ᶠ n : ℕ in atTop,
      A n * C (n + 1) - A (n + 1) * C n ≠ 0)
    (hsmall : Tendsto
      (fun n : ℕ =>
        |(A n : ℝ) * x - (C n : ℝ)| +
          |(A (n + 1) : ℝ) * x - (C (n + 1) : ℝ)|)
      atTop (𝓝 0)) :
    Irrational x :=
  EPlusPiApproximation.irrational_of_tendsto_zero_paired_integer_linear_forms
    hdet (by simpa [EPlusPiApproximation.pairedIntegerLinearFormValue] using hsmall)

/-! ## Relative algebraic closure as an intermediate field -/

@[instance_reducible]
noncomputable def algebraic_elements_field_structure
    (K E : Type*) [Field K] [Field E] [Algebra K E] :
    Field (G.AlgebraicElements.field K E) :=
  G.AlgebraicElements.field_structure K E

theorem algebraic_elements_mem_iff
    (K E : Type*) [Field K] [Field E] [Algebra K E] {x : E} :
    x ∈ algebraicClosure K E ↔ IsAlgebraic K x := by
  simpa [G.AlgebraicElements.field] using G.AlgebraicElements.mem_iff K E

theorem algebraic_elements_carrier_eq
    (K E : Type*) [Field K] [Field E] [Algebra K E] :
    {x : E | IsAlgebraic K x} = (algebraicClosure K E : Set E) := by
  simpa [G.AlgebraicElements.carrier, G.AlgebraicElements.field] using
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
    Algebra.IsAlgebraic K (algebraicClosure K E) := by
  simpa [G.AlgebraicElements.field] using
    G.AlgebraicElements.field_is_algebraic K E

theorem algebraic_elements_maximality
    (K E : Type*) [Field K] [Field E] [Algebra K E]
    (L : IntermediateField K E) :
    L ≤ algebraicClosure K E ↔ Algebra.IsAlgebraic K L := by
  simpa [G.AlgebraicElements.field] using
    G.AlgebraicElements.maximality K E L

theorem algebraic_elements_isAlgClosure_of_algClosed_ambient
    (K E : Type*) [Field K] [Field E] [Algebra K E] [IsAlgClosed E] :
    IsAlgClosure K (algebraicClosure K E) := by
  simpa [G.AlgebraicElements.field] using
    G.AlgebraicElements.isAlgClosure_of_algClosed_ambient K E

theorem algebraic_elements_field_isAlgClosed
    (K E : Type*) [Field K] [Field E] [Algebra K E] [IsAlgClosed E] :
    IsAlgClosed (algebraicClosure K E) := by
  simpa [G.AlgebraicElements.field] using
    G.AlgebraicElements.field_isAlgClosed K E

theorem algebraic_elements_every_polynomial_splits
    (K E : Type*) [Field K] [Field E] [Algebra K E] [IsAlgClosed E]
    (p : Polynomial (algebraicClosure K E)) :
    p.Splits :=
  G.AlgebraicElements.every_polynomial_splits K E p

theorem algebraic_elements_exists_root
    (K E : Type*) [Field K] [Field E] [Algebra K E] [IsAlgClosed E]
    (p : Polynomial (algebraicClosure K E)) (hp : p.degree ≠ 0) :
    ∃ x : algebraicClosure K E, IsRoot p x :=
  G.AlgebraicElements.exists_root K E p hp

universe u v

theorem algebraic_elements_uniqueness_up_to_algEquiv
    (K : Type u) [Field K]
    (A B : Type v) [Field A] [Field B]
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

/-! ## Mixed-kernel quotient and mixed-integral factorization -/

noncomputable def mixed_endpoint_split_kernel :
    Polynomial ℤ ≃ₗ[ℤ]
      LinearMap.ker MixedKernelQuotient.endpointSignature × (ℤ × ℤ) :=
  MixedKernelQuotient.endpointSplitEquiv

noncomputable def mixed_endpoint_kernel_quotient :
    (Polynomial ℤ ⧸ LinearMap.ker MixedKernelQuotient.endpointSignature) ≃ₗ[ℤ]
      ℤ × ℤ :=
  MixedKernelQuotient.endpointQuotientEquiv

theorem mixed_integral_identity (p : Polynomial ℤ) :
    MixedKernelQuotient.mixedIntegralValue p =
      MixedKernelQuotient.mixedPairValue
        (MixedKernelQuotient.endpointSignature p) :=
  MixedKernelQuotient.mixedIntegral_identity p

theorem mixed_integral_factorization :
    MixedKernelQuotient.mixedIntegralQuotientFactor.comp
        ((LinearMap.ker MixedKernelQuotient.endpointSignature).mkQ) =
      MixedKernelQuotient.mixedPairValue.comp
        MixedKernelQuotient.endpointSignature :=
  MixedKernelQuotient.mixedIntegral_factorization_map

theorem mixed_integral_factors_through_quotient (p : Polynomial ℤ) :
    MixedKernelQuotient.mixedIntegralQuotientFactor
        ((LinearMap.ker MixedKernelQuotient.endpointSignature).mkQ p) =
      MixedKernelQuotient.mixedIntegralValue p :=
  MixedKernelQuotient.mixedIntegral_factors_through_quotient p

#print axioms mixed_endpoint_split_kernel
#print axioms mixed_endpoint_kernel_quotient
#print axioms mixed_integral_identity
#print axioms mixed_integral_factorization
#print axioms mixed_integral_factors_through_quotient

end ProofAudit
