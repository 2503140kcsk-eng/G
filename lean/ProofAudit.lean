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
public import IntegerEndpointLattice
public import IntegerLatticeCertificates
public import MixedKernelQuotient
public import ProofAuditApprox
public import CommonDenominatorApproximation
public import FactorialTaylorFusion

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


/-! ## Common-denominator fusion for separate rational approximants -/

/-- The cross-multiplied error budget is sufficient for an irrationality
    certificate after the two integer denominators are fused. -/
theorem irrational_of_common_denominator_approximations
    {x y : ℝ} {q r : ℕ → ℕ} {p s : ℕ → ℤ}
    (hnz : ∀ᶠ n : ℕ in Filter.atTop,
      EPlusPiApproximation.signedIntegerLinearFormValue (x + y)
        (EPlusPiApproximation.commonDenominatorCoefficient (q n) (r n))
        (EPlusPiApproximation.commonDenominatorConstant
          (q n) (r n) (p n) (s n)) ≠ 0)
    (hsmall : Filter.Tendsto
      (fun n : ℕ =>
        EPlusPiApproximation.commonDenominatorScaledError
          x y (q n) (r n) (p n) (s n))
      Filter.atTop (𝓝 0)) :
    Irrational (x + y) :=
  EPlusPiApproximation.irrational_of_common_denominator_approximations
    hnz hsmall

#print axioms irrational_of_common_denominator_approximations



/-! ## Factorial Taylor approximation and fusion obstruction -/

/-- The current factorial Taylor approximants to e force every fused pi denominator
    to be sublinear in the Taylor index. -/
theorem factorial_taylor_fusion_forces_sublinear_pi_denominators
    {r : ℕ → ℕ} {s : ℕ → ℤ}
    (hsmall : Filter.Tendsto
      (FactorialTaylorFusion.factorialTaylorFusionError r s)
      Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n : ℕ => (r n : ℝ) / (n + 1 : ℝ))
      Filter.atTop (𝓝 0) :=
  FactorialTaylorFusion.factorialTaylor_denominator_sublinear_of_fusion_tendsto_zero
    hsmall

#print axioms factorial_taylor_fusion_forces_sublinear_pi_denominators



/-! ## A conditional no-go theorem from an explicit Diophantine lower bound for pi -/

/-- Under a uniform lower bound of order r^(-7) for the pi-side integer forms,
    the current factorial Taylor family cannot have vanishing cross-weighted error. -/
theorem factorial_taylor_fusion_no_go_from_pi_measure_lower_bound
    {r : ℕ → ℕ} {s : ℕ → ℤ} {c : ℝ}
    (hc : 0 < c)
    (hrpos : ∀ n, 0 < r n)
    (hpi : ∀ n,
      c / (r n : ℝ) ^ 7 ≤
        |(r n : ℝ) * Real.pi - (s n : ℝ)|) :
    ¬ Filter.Tendsto (FactorialTaylorFusion.factorialTaylorFusionError r s)
      Filter.atTop (𝓝 0) :=
  FactorialTaylorFusion.factorialTaylor_fusion_not_tendsto_zero_of_pi_lower_bound
    hc hrpos hpi

#print axioms factorial_taylor_fusion_no_go_from_pi_measure_lower_bound



/-! ## Primitive rank-one endpoint lattice arithmetic -/

/-- A Bezout-primitive endpoint pair spans every integral pair on its rational
    line. This is the saturation lemma used by the Split–Machin endpoint
    intersection problem. -/
theorem integer_pair_multiple_of_bezout_and_determinant
    {a b c d : ℤ}
    (hbez : ∃ u v : ℤ, u * a + v * b = 1)
    (hdet : a * d = b * c) :
    ∃ k : ℤ, c = k * a ∧ d = k * b :=
  EPlusPiApproximation.integer_pair_multiple_of_bezout_and_determinant
    hbez hdet

#print axioms integer_pair_multiple_of_bezout_and_determinant



/-- Replacing a Bezout witness by the equivalent gcd-one condition gives the
    same primitive rank-one endpoint conclusion. -/
theorem integer_pair_multiple_of_gcd_one_and_determinant
    {a b c d : ℤ}
    (hcoprime : Int.gcd a b = 1)
    (hdet : a * d = b * c) :
    ∃ k : ℤ, c = k * a ∧ d = k * b :=
  EPlusPiApproximation.integer_pair_multiple_of_gcd_one_and_determinant
    hcoprime hdet

/-- If every row of an integer two-column matrix is collinear with a
    Bezout-primitive anchor row that occurs in the matrix, then the common
    kernel equals the kernel of that anchor row. -/
theorem integer_row_kernel_iff_anchor
    {ι : Type*} (i₀ : ι) {a b : ℤ} (A B : ι → ℤ)
    (hA₀ : A i₀ = a) (hB₀ : B i₀ = b)
    (hbez : ∃ u v : ℤ, u * a + v * b = 1)
    (hcollinear : ∀ i, a * B i = b * A i)
    (x y : ℤ) :
    (∀ i, A i * x + B i * y = 0) ↔ a * x + b * y = 0 :=
  EPlusPiApproximation.integer_row_kernel_iff_anchor
    i₀ A B hA₀ hB₀ hbez hcollinear x y

/-- The row-kernel reduction with the anchor row's primitivity expressed as
    Int.gcd a b = 1. -/
theorem integer_row_kernel_iff_anchor_of_gcd_one
    {ι : Type*} (i₀ : ι) {a b : ℤ} (A B : ι → ℤ)
    (hA₀ : A i₀ = a) (hB₀ : B i₀ = b)
    (hcoprime : Int.gcd a b = 1)
    (hcollinear : ∀ i, a * B i = b * A i)
    (x y : ℤ) :
    (∀ i, A i * x + B i * y = 0) ↔ a * x + b * y = 0 :=
  EPlusPiApproximation.integer_row_kernel_iff_anchor_of_gcd_one
    i₀ A B hA₀ hB₀ hcoprime hcollinear x y

#print axioms integer_pair_multiple_of_gcd_one_and_determinant
#print axioms integer_row_kernel_iff_anchor
#print axioms integer_row_kernel_iff_anchor_of_gcd_one


/-! ## Exact matrix interface for primitive endpoint kernels -/

/-- Derive a Bezout witness directly from the integer gcd-one hypothesis. -/
theorem exists_bezout_of_int_gcd_eq_one
    {a b : ℤ} (hcoprime : Int.gcd a b = 1) :
    ∃ u v : ℤ, u * a + v * b = 1 :=
  EPlusPiApproximation.exists_bezout_of_int_gcd_eq_one hcoprime

/-- A two-column integer matrix whose rows are all collinear with a primitive
    anchor row has exactly the anchor row's integer kernel. -/
theorem integer_two_column_matrix_kernel_iff_anchor
    {ι : Type*} (i₀ : ι) (M : Matrix ι (Fin 2) ℤ)
    {a b : ℤ}
    (hA₀ : M i₀ 0 = a) (hB₀ : M i₀ 1 = b)
    (hbez : ∃ u v : ℤ, u * a + v * b = 1)
    (hminor : ∀ i, a * M i 1 = b * M i 0)
    (x y : ℤ) :
    (∀ i, M i 0 * x + M i 1 * y = 0) ↔ a * x + b * y = 0 :=
  EPlusPiApproximation.integer_two_column_matrix_kernel_iff_anchor
    i₀ M hA₀ hB₀ hbez hminor x y

/-- The collinearity conclusion fails without a primitive anchor: (2,2) and
    (1,1) have zero determinant, but (1,1) is not an integer multiple of (2,2). -/
theorem nonprimitive_pair_counterexample :
    (2 : ℤ) * 1 = 2 * 1 ∧
      ¬ ∃ k : ℤ, (1 : ℤ) = k * 2 ∧ 1 = k * 2 :=
  EPlusPiApproximation.nonprimitive_pair_counterexample

#print axioms exists_bezout_of_int_gcd_eq_one
#print axioms integer_two_column_matrix_kernel_iff_anchor
#print axioms nonprimitive_pair_counterexample


/-! ## Exact integer generator for rank-one endpoint kernels -/

/-- A primitive integer row has its integer kernel generated by its
    perpendicular primitive vector. -/
theorem integer_pair_kernel_iff_primitive_generator
    {a b x y : ℤ}
    (hbez : ∃ u v : ℤ, u * a + v * b = 1) :
    a * x + b * y = 0 ↔
      ∃ k : ℤ, x = -b * k ∧ y = a * k :=
  EPlusPiApproximation.integer_pair_kernel_iff_primitive_generator hbez

/-- The matrix-level endpoint kernel is the cyclic lattice generated by
    the primitive perpendicular to an anchor row. -/
theorem integer_two_column_matrix_kernel_eq_zsmul_anchor
    {ι : Type*} (i₀ : ι) (M : Matrix ι (Fin 2) ℤ)
    {a b : ℤ}
    (hA₀ : M i₀ 0 = a) (hB₀ : M i₀ 1 = b)
    (hbez : ∃ u v : ℤ, u * a + v * b = 1)
    (hminor : ∀ i, a * M i 1 = b * M i 0)
    (x y : ℤ) :
    (∀ i, M i 0 * x + M i 1 * y = 0) ↔
      ∃ k : ℤ, x = -b * k ∧ y = a * k :=
  EPlusPiApproximation.integer_two_column_matrix_kernel_eq_zsmul_anchor
    i₀ M hA₀ hB₀ hbez hminor x y

/-- The cyclic matrix-kernel result using gcd one as the primitivity condition. -/
theorem integer_two_column_matrix_kernel_eq_zsmul_anchor_of_gcd_one
    {ι : Type*} (i₀ : ι) (M : Matrix ι (Fin 2) ℤ)
    {a b : ℤ}
    (hA₀ : M i₀ 0 = a) (hB₀ : M i₀ 1 = b)
    (hcoprime : Int.gcd a b = 1)
    (hminor : ∀ i, a * M i 1 = b * M i 0)
    (x y : ℤ) :
    (∀ i, M i 0 * x + M i 1 * y = 0) ↔
      ∃ k : ℤ, x = -b * k ∧ y = a * k :=
  EPlusPiApproximation.integer_two_column_matrix_kernel_eq_zsmul_anchor_of_gcd_one
    i₀ M hA₀ hB₀ hcoprime hminor x y

/-- A nonprimitive row need not generate its full integer kernel through its
    perpendicular vector. -/
theorem nonprimitive_row_kernel_counterexample :
    (2 : ℤ) * 0 + 0 * 1 = 0 ∧
      ¬ ∃ k : ℤ, (0 : ℤ) = -0 * k ∧ 1 = 2 * k :=
  EPlusPiApproximation.nonprimitive_row_kernel_counterexample

#print axioms integer_pair_kernel_iff_primitive_generator
#print axioms integer_two_column_matrix_kernel_eq_zsmul_anchor
#print axioms integer_two_column_matrix_kernel_eq_zsmul_anchor_of_gcd_one
#print axioms nonprimitive_row_kernel_counterexample


/-! ## Rank-one source matrices without an actual primitive row -/

/-- Nonzero-row form of the rank-one kernel reduction; the primitive anchor
    direction need not itself be a matrix row. -/
theorem integer_row_kernel_iff_anchor_of_nonzero
    {ι : Type*} {a b : ℤ} (A B : ι → ℤ)
    (hbez : ∃ u v : ℤ, u * a + v * b = 1)
    (hcollinear : ∀ i, a * B i = b * A i)
    (hnonzero : ∃ i, A i ≠ 0 ∨ B i ≠ 0)
    (x y : ℤ) :
    (∀ i, A i * x + B i * y = 0) ↔ a * x + b * y = 0 :=
  EPlusPiApproximation.integer_row_kernel_iff_anchor_of_nonzero
    A B hbez hcollinear hnonzero x y

/-- Two-column matrix form of the nonzero-row rank-one kernel reduction. -/
theorem integer_two_column_matrix_kernel_iff_anchor_of_nonzero
    {ι : Type*} (M : Matrix ι (Fin 2) ℤ)
    {a b : ℤ}
    (hbez : ∃ u v : ℤ, u * a + v * b = 1)
    (hminor : ∀ i, a * M i 1 = b * M i 0)
    (hnonzero : ∃ i, M i 0 ≠ 0 ∨ M i 1 ≠ 0)
    (x y : ℤ) :
    (∀ i, M i 0 * x + M i 1 * y = 0) ↔ a * x + b * y = 0 :=
  EPlusPiApproximation.integer_two_column_matrix_kernel_iff_anchor_of_nonzero
    M hbez hminor hnonzero x y

/-- The integer kernel is the cyclic lattice generated by the perpendicular
    primitive vector even when that vector is not one of the matrix rows. -/
theorem integer_two_column_matrix_kernel_eq_zsmul_anchor_of_nonzero
    {ι : Type*} (M : Matrix ι (Fin 2) ℤ)
    {a b : ℤ}
    (hbez : ∃ u v : ℤ, u * a + v * b = 1)
    (hminor : ∀ i, a * M i 1 = b * M i 0)
    (hnonzero : ∃ i, M i 0 ≠ 0 ∨ M i 1 ≠ 0)
    (x y : ℤ) :
    (∀ i, M i 0 * x + M i 1 * y = 0) ↔
      ∃ k : ℤ, x = -b * k ∧ y = a * k :=
  EPlusPiApproximation.integer_two_column_matrix_kernel_eq_zsmul_anchor_of_nonzero
    M hbez hminor hnonzero x y

/-- Gcd-one version of the nonzero-row cyclic-kernel theorem. -/
theorem integer_two_column_matrix_kernel_eq_zsmul_anchor_of_nonzero_gcd_one
    {ι : Type*} (M : Matrix ι (Fin 2) ℤ)
    {a b : ℤ}
    (hcoprime : Int.gcd a b = 1)
    (hminor : ∀ i, a * M i 1 = b * M i 0)
    (hnonzero : ∃ i, M i 0 ≠ 0 ∨ M i 1 ≠ 0)
    (x y : ℤ) :
    (∀ i, M i 0 * x + M i 1 * y = 0) ↔
      ∃ k : ℤ, x = -b * k ∧ y = a * k :=
  EPlusPiApproximation.integer_two_column_matrix_kernel_eq_zsmul_anchor_of_nonzero_gcd_one
    M hcoprime hminor hnonzero x y

#print axioms integer_row_kernel_iff_anchor_of_nonzero
#print axioms integer_two_column_matrix_kernel_iff_anchor_of_nonzero
#print axioms integer_two_column_matrix_kernel_eq_zsmul_anchor_of_nonzero
#print axioms integer_two_column_matrix_kernel_eq_zsmul_anchor_of_nonzero_gcd_one


/-! ## Split–Machin endpoint kernel from the old success coordinates -/

/-- If the old success vector (b₀,δ) is primitive and lies in the endpoint
    kernel, and the endpoint matrix is nonzero, it generates the full
    integer kernel. -/
theorem integer_endpoint_kernel_from_primitive_success
    {ι : Type*} (M : Matrix ι (Fin 2) ℤ)
    {b₀ δ : ℤ}
    (hcoprime : Int.gcd b₀ δ = 1)
    (hsuccess : ∀ i, M i 0 * b₀ + M i 1 * δ = 0)
    (hnonzero : ∃ i, M i 0 ≠ 0 ∨ M i 1 ≠ 0)
    (x y : ℤ) :
    (∀ i, M i 0 * x + M i 1 * y = 0) ↔
      ∃ k : ℤ, x = b₀ * k ∧ y = δ * k :=
  EPlusPiApproximation.integer_endpoint_kernel_from_primitive_success
    M hcoprime hsuccess hnonzero x y

#print axioms integer_endpoint_kernel_from_primitive_success


/-! ## Success coordinates force endpoint anchor minors -/

/-- A single endpoint row annihilating the old success vector is collinear
    with the primitive perpendicular anchor direction. -/
theorem endpoint_success_row_implies_anchor_minor
    {b₀ δ A B : ℤ}
    (hsuccess : A * b₀ + B * δ = 0) :
    δ * B = (-b₀) * A :=
  EPlusPiApproximation.endpoint_success_row_implies_anchor_minor hsuccess

/-- The same anchor-minor identity for every row of the endpoint matrix. -/
theorem endpoint_success_rows_imply_anchor_minors
    {ι : Type*} {b₀ δ : ℤ} (A B : ι → ℤ)
    (hsuccess : ∀ i, A i * b₀ + B i * δ = 0) :
    ∀ i, δ * B i = (-b₀) * A i :=
  EPlusPiApproximation.endpoint_success_rows_imply_anchor_minors
    A B hsuccess

#print axioms endpoint_success_row_implies_anchor_minor
#print axioms endpoint_success_rows_imply_anchor_minors


/-! ## Modular-dual certificates for integer column lattices -/

/-- A modular row functional that annihilates every matrix column but not
    the target proves that the target is outside the integer column span. -/
theorem not_mem_integer_column_span_of_modular_dual
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ)
    (y : Fin m → ℤ) (q : ℤ) (s : Fin m → ℤ)
    (hcolumns : ∀ j : Fin n, q ∣ ∑ i : Fin m, s i * A i j)
    (htarget : ¬ q ∣ ∑ i : Fin m, s i * y i) :
    ¬ ∃ c : Fin n → ℤ,
        ∀ i : Fin m, y i = ∑ j : Fin n, A i j * c j :=
  EPlusPiApproximation.not_mem_integer_column_span_of_modular_dual
    A y q s hcolumns htarget

#print axioms not_mem_integer_column_span_of_modular_dual



/-! ## Typed integer-lattice certificate interfaces -/

/-- Exact integer-column membership certificates are sound. -/
theorem integer_lattice_membership_certificate_sound
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℤ} {y : Fin m → ℤ}
    (C : EPlusPiApproximation.IntegerLatticeMembershipCertificate A y) :
    ∃ c : Fin n → ℤ, ∀ i, y i = ∑ j, A i j * c j :=
  C.sound

/-- General modular-dual certificates prove integer-column nonmembership. -/
theorem integer_lattice_nonmembership_certificate_sound
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℤ} {y : Fin m → ℤ}
    (C : EPlusPiApproximation.IntegerLatticeNonmembershipCertificate A y) :
    ¬ ∃ c : Fin n → ℤ, ∀ i, y i = ∑ j, A i j * c j :=
  C.sound

/-- Prime-power dual certificates prove integer-column nonmembership. -/
theorem prime_power_nonmembership_certificate_sound
    {m n p : ℕ} {A : Matrix (Fin m) (Fin n) ℤ} {y : Fin m → ℤ}
    (C : EPlusPiApproximation.PrimePowerNonmembershipCertificate A y p) :
    ¬ ∃ c : Fin n → ℤ, ∀ i, y i = ∑ j, A i j * c j :=
  C.sound

/-- Localized membership certificates carry an exact denominator-cleared witness. -/
theorem prime_localized_membership_certificate_sound
    {m n p : ℕ} {A : Matrix (Fin m) (Fin n) ℤ} {y : Fin m → ℤ}
    (C : EPlusPiApproximation.PrimeLocalizedMembershipCertificate A y p) :
    ∃ u : ℤ, (¬ (p : ℤ) ∣ u) ∧
      ∃ c : Fin n → ℤ, ∀ i, u * y i = ∑ j, A i j * c j :=
  C.sound

/-- The full-rank lattice index is the product of its Smith diagonal coefficients. -/
theorem smith_diagonal_index_product
    {m : ℕ} (L : Submodule ℤ (Fin m → ℤ))
    (hRank : Module.finrank ℤ L = m) :
    L.toAddSubgroup.index =
      ∏ i : Fin (Fintype.card (Fin m)),
        Int.natAbs (EPlusPiApproximation.smithDiagonalCoefficients L hRank i) :=
  EPlusPiApproximation.index_eq_product_smith_diagonal_coefficients L hRank

/-- Primitive reduction stays in the same saturated lattice and preserves weighted decay. -/
theorem primitive_integerization_tendsto_zero
    {m : ℕ} {L : Submodule ℤ (Fin m → ℤ)}
    {x : ℕ → (Fin m → ℚ)}
    (C : ∀ n, EPlusPiApproximation.PrimitiveIntegerization L (x n))
    (hL : EPlusPiApproximation.IsPrimitiveIntegerLattice L)
    (a : Fin m → ℝ)
    (hweighted : Tendsto
      (fun n =>
        ((C n).denominator : ℝ) / ((C n).content : ℝ) *
          |EPlusPiApproximation.rationalVectorPairing a (x n)|) atTop (𝓝 0)) :
    Tendsto
      (fun n =>
        |EPlusPiApproximation.integerVectorPairing a (C n).primitiveVector|)
      atTop (𝓝 0) ∧
      ∀ n, (C n).primitiveVector ∈ L :=
  EPlusPiApproximation.PrimitiveIntegerization.tendsto_primitive_errors_of_weighted
    C hL a hweighted

#print axioms integer_lattice_membership_certificate_sound
#print axioms integer_lattice_nonmembership_certificate_sound
#print axioms prime_power_nonmembership_certificate_sound
#print axioms prime_localized_membership_certificate_sound
#print axioms smith_diagonal_index_product
#print axioms primitive_integerization_tendsto_zero

/-- A finite-limit scale times a null error remains a null weighted error.
    This is the scalar convergence step used by primitive integerization. -/
theorem finite_ratio_weighted_error_tendsto_zero
    {ratio error : ℕ → ℝ} {b : ℝ}
    (hratio : Tendsto ratio atTop (𝓝 b))
    (herr : Tendsto error atTop (𝓝 0)) :
    Tendsto (fun n => ratio n * error n) atTop (𝓝 0) := by
  simpa using hratio.mul herr

#print axioms finite_ratio_weighted_error_tendsto_zero

end ProofAudit
