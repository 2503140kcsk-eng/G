module
public import AlgebraicClosure
public import AlgebraicElements
public import AlgebraicFieldClosure
public import LindemannBasic
public import HermiteLindemannBridge
public import EPlusPi
public import SchanuelConditional
public import ApproximationCriteria
public import ResultantSuperpolynomial
public import ResultantPairedCriterion
public import ResultantHeightBound
public import SplitMachinTaylorArithmetic
public import SplitMachinTaylorResultantBridge
public import PairedApproximationCriteria
public import MixedKernelQuotient
public import ProofAuditApprox

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

/-- A fixed-power lower bound contradicts super-polynomial decay. -/
theorem superpolynomial_decay_conflicts_with_fixed_power_lower_bound
    {H : ℕ → ℕ} {u : ℕ → ℝ} (d : ℕ)
    (hH : ∀ᶠ n : ℕ in atTop, 1 < H n)
    (hLower : ∀ᶠ n : ℕ in atTop,
      1 / (H n : ℝ) ^ d ≤ |u n|)
    (hSmall : ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
      |u n| < 1 / (H n : ℝ) ^ k) :
    False :=
  EPlusPiApproximation.no_superpolynomial_smallness_with_fixed_power_lower_bound
    d hH hLower hSmall

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

/-- Bézout-coprime rational polynomials cannot share a real root. -/
theorem coprime_polynomials_not_both_zero_at_real
    {p q : Polynomial ℚ} (hcop : IsCoprime p q) (x : ℝ) :
    p.eval₂ (algebraMap ℚ ℝ) x ≠ 0 ∨
      q.eval₂ (algebraMap ℚ ℝ) x ≠ 0 := by
  simpa [EPlusPiApproximation.evalReal] using
    EPlusPiApproximation.coprime_polynomials_not_both_zero_at_real hcop x

/-- Pairwise coprime polynomials have at most one index vanishing at a fixed point. -/
theorem pairwise_coprime_family_has_at_most_one_zero
    {ι : Type*} (R : ι → Polynomial ℚ) (x : ℝ)
    (hcop : ∀ i j, i ≠ j → IsCoprime (R i) (R j)) :
    ∀ i j, (R i).eval₂ (algebraMap ℚ ℝ) x = 0 →
      (R j).eval₂ (algebraMap ℚ ℝ) x = 0 → i = j := by
  simpa [EPlusPiApproximation.evalReal] using
    EPlusPiApproximation.pairwise_coprime_family_has_at_most_one_zero R x hcop

/-- All but finitely many members of a pairwise-coprime polynomial sequence are nonzero at a fixed point. -/
theorem pairwise_coprime_family_eventually_nonzero_at_real
    (R : ℕ → Polynomial ℚ) (x : ℝ)
    (hcop : ∀ i j, i ≠ j → IsCoprime (R i) (R j)) :
    ∀ᶠ n : ℕ in atTop, (R n).eval₂ (algebraMap ℚ ℝ) x ≠ 0 := by
  simpa [EPlusPiApproximation.evalReal] using
    EPlusPiApproximation.pairwise_coprime_family_eventually_nonzero_at_real R x hcop

/-- The paired small-value criterion's final contradiction from a fixed-power bound. -/
theorem paired_superpolynomial_smallness_conflicts_with_fixed_power_lower_bound
    {x : ℝ} {P Q : ℕ → Polynomial ℚ} {H : ℕ → ℕ} (d : ℕ)
    (hH : ∀ᶠ n : ℕ in atTop, 1 < H n)
    (hCoprimeP : ∀ i j, i ≠ j → IsCoprime (P i) (P j))
    (hCoprimeQ : ∀ i j, i ≠ j → IsCoprime (Q i) (Q j))
    (hLowerP : ∀ᶠ n : ℕ in atTop,
      (P n).eval₂ (algebraMap ℚ ℝ) x ≠ 0 →
        1 / (H n : ℝ) ^ d ≤ |(P n).eval₂ (algebraMap ℚ ℝ) x|)
    (hLowerQ : ∀ᶠ n : ℕ in atTop,
      (Q n).eval₂ (algebraMap ℚ ℝ) x ≠ 0 →
        1 / (H n : ℝ) ^ d ≤ |(Q n).eval₂ (algebraMap ℚ ℝ) x|)
    (hSmall : ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
      min |(P n).eval₂ (algebraMap ℚ ℝ) x|
          |(Q n).eval₂ (algebraMap ℚ ℝ) x| <
        1 / (H n : ℝ) ^ k) :
    False := by
  simpa [EPlusPiApproximation.evalReal] using
    EPlusPiApproximation.paired_superpolynomial_smallness_conflicts_with_fixed_power_lower_bound
      d hH hCoprimeP hCoprimeQ hLowerP hLowerQ hSmall

#print axioms coprime_polynomials_not_both_zero_at_real
#print axioms pairwise_coprime_family_has_at_most_one_zero
#print axioms paired_superpolynomial_smallness_conflicts_with_fixed_power_lower_bound
/-- Paired super-polynomial approximation proves transcendence once the
algebraic resultant lower bound is supplied for each algebraic candidate. -/
theorem transcendental_of_paired_superpolynomial_approximation_of_algebraic_lower_bound
    {x : ℝ} {P Q : ℕ → Polynomial ℚ} {H : ℕ → ℕ}
    (hH : ∀ᶠ n : ℕ in atTop, 1 < H n)
    (hCoprimeP : ∀ i j, i ≠ j → IsCoprime (P i) (P j))
    (hCoprimeQ : ∀ i j, i ≠ j → IsCoprime (Q i) (Q j))
    (hSmall : ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
      min |(P n).eval₂ (algebraMap ℚ ℝ) x|
          |(Q n).eval₂ (algebraMap ℚ ℝ) x| <
        1 / (H n : ℝ) ^ k)
    (hLiouville : IsAlgebraic ℚ x →
      ∃ d : ℕ,
        (∀ᶠ n : ℕ in atTop,
          (P n).eval₂ (algebraMap ℚ ℝ) x ≠ 0 →
            1 / (H n : ℝ) ^ d ≤ |(P n).eval₂ (algebraMap ℚ ℝ) x|) ∧
        (∀ᶠ n : ℕ in atTop,
          (Q n).eval₂ (algebraMap ℚ ℝ) x ≠ 0 →
            1 / (H n : ℝ) ^ d ≤ |(Q n).eval₂ (algebraMap ℚ ℝ) x|)) :
    Transcendental ℚ x := by
  simpa [EPlusPiApproximation.evalReal] using
    EPlusPiApproximation.transcendental_of_paired_superpolynomial_approximation_of_algebraic_lower_bound
      hH hCoprimeP hCoprimeQ hSmall hLiouville

#print axioms transcendental_of_paired_superpolynomial_approximation_of_algebraic_lower_bound


/-- A rationally coprime pair of integer polynomials has nonzero integer resultant. -/
theorem int_resultant_ne_zero_of_rat_coprime
    (f g : Polynomial ℤ)
    (hcop : IsCoprime
      (f.map (algebraMap ℤ ℚ))
      (g.map (algebraMap ℤ ℚ))) :
    Polynomial.resultant f g ≠ 0 :=
  EPlusPiApproximation.int_resultant_ne_zero_of_rat_coprime f g hcop

/-- The resultant product formula gives a lower bound at a selected root. -/
theorem resultant_eval_lower_bound_of_other_roots
    (f g : Polynomial ℤ) (α : ℂ) (B : ℝ)
    (hcop : IsCoprime
      (f.map (algebraMap ℤ ℚ))
      (g.map (algebraMap ℤ ℚ)))
    (hα : α ∈ (f.map (algebraMap ℤ ℂ)).roots)
    (hB : 0 ≤ B)
    (hOther : ∀ z ∈ ((f.map (algebraMap ℤ ℂ)).roots.erase α),
      ‖(g.map (algebraMap ℤ ℂ)).eval z‖ ≤ B) :
    1 ≤
      ‖(f.map (algebraMap ℤ ℂ)).leadingCoeff‖ ^ g.natDegree *
        ‖(g.map (algebraMap ℤ ℂ)).eval α‖ *
          B ^ ((f.map (algebraMap ℤ ℂ)).natDegree - 1) :=
  EPlusPiApproximation.resultant_eval_lower_bound_of_other_roots
    f g α B hcop hα hB hOther

/-- Cauchy's root bound and a coefficient-height bound control all conjugate evaluations. -/
theorem resultant_eval_lower_bound_of_cauchy_and_coefficient_bound
    (f g : Polynomial ℤ) (α : ℂ) (H : ℝ)
    (hcop : IsCoprime
      (f.map (algebraMap ℤ ℚ))
      (g.map (algebraMap ℤ ℚ)))
    (hα : α ∈ (f.map (algebraMap ℤ ℂ)).roots)
    (hH : 0 ≤ H)
    (hcoeff : ∀ i,
      ‖(g.map (algebraMap ℤ ℂ)).coeff i‖ ≤ H) :
    1 ≤
      ‖(f.map (algebraMap ℤ ℂ)).leadingCoeff‖ ^
          (g.map (algebraMap ℤ ℂ)).natDegree *
        ‖(g.map (algebraMap ℤ ℂ)).eval α‖ *
          (((((g.map (algebraMap ℤ ℂ)).natDegree + 1 : ℕ) : ℝ) * H *
              (Polynomial.cauchyBound (f.map (algebraMap ℤ ℂ)) : ℝ) ^
                (g.map (algebraMap ℤ ℂ)).natDegree) ^
            ((f.map (algebraMap ℤ ℂ)).natDegree - 1)) :=
  EPlusPiApproximation.resultant_eval_lower_bound_of_cauchy_and_coefficient_bound
    f g α H hcop hα hH hcoeff

/-- Algebraicity over Q yields a nonzero integer polynomial relation. -/
theorem exists_primitive_irreducible_integer_polynomial_vanishing_of_algebraic
    {x : ℝ} (hx : IsAlgebraic ℚ x) :
    ∃ f : Polynomial ℤ, f ≠ 0 ∧ f.IsPrimitive ∧
      Irreducible f ∧ Polynomial.aeval x f = 0 :=
  EPlusPiApproximation.exists_primitive_irreducible_integer_polynomial_vanishing_of_algebraic hx

#print axioms exists_primitive_irreducible_integer_polynomial_vanishing_of_algebraic

theorem exists_nonzero_integer_polynomial_vanishing_of_algebraic
    {x : ℝ} (hx : IsAlgebraic ℚ x) :
    ∃ f : Polynomial ℤ, f ≠ 0 ∧ Polynomial.aeval x f = 0 :=
  EPlusPiApproximation.exists_nonzero_integer_polynomial_vanishing_of_algebraic hx

#print axioms int_resultant_ne_zero_of_rat_coprime
#print axioms resultant_eval_lower_bound_of_other_roots
#print axioms resultant_eval_lower_bound_of_cauchy_and_coefficient_bound
#print axioms exists_nonzero_integer_polynomial_vanishing_of_algebraic

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


/-! ## Exact denominator bridge for the Split–Machin Taylor coefficients -/

/-- A single explicit integer denominator clears each coefficient up to the
chosen Taylor degree. This is a formal arithmetic input for later height
bounds; it does not assert that the resulting endpoint form is small. -/
theorem split_machin_taylor_coefficients_have_an_exact_common_denominator
    (N k : ℕ) (hk : k ≤ N) :
    ∃ z : ℤ,
      (EPlusPiApproximation.splitMachinTaylorCommonDenominator N : ℚ) *
        EPlusPiApproximation.splitMachinTaylorCoefficient k = z :=
  EPlusPiApproximation.splitMachinTaylor_commonDenominator_clears_coefficient
    N k hk

#print axioms split_machin_taylor_coefficients_have_an_exact_common_denominator


/-! ## Scalar Split–Machin approximation through the resultant-height bridge -/

/-- The actual rational endpoint Taylor truncations have integerized
coefficients, a concrete height, and therefore the fixed-power algebraic
lower bound supplied by the resultant theorem. -/
theorem split_machin_scalar_taylor_has_concrete_hLiouville
    {x : ℝ} :
    IsAlgebraic ℚ x →
      ∃ d : ℕ,
        (∀ᶠ n : ℕ in atTop,
          evalReal x
            (EPlusPiApproximation.splitMachinScalarTaylorApproxPolynomial n) ≠ 0 →
            1 / (EPlusPiApproximation.splitMachinScalarTaylorHeight n : ℝ) ^ d ≤
              |evalReal x
                (EPlusPiApproximation.splitMachinScalarTaylorApproxPolynomial n)|) ∧
        (∀ᶠ n : ℕ in atTop,
          evalReal x
            (EPlusPiApproximation.splitMachinScalarTaylorApproxPolynomial n) ≠ 0 →
            1 / (EPlusPiApproximation.splitMachinScalarTaylorHeight n : ℝ) ^ d ≤
              |evalReal x
                (EPlusPiApproximation.splitMachinScalarTaylorApproxPolynomial n)|) :=
  EPlusPiApproximation.splitMachinScalarTaylor_has_concrete_hLiouville

#print axioms split_machin_scalar_taylor_has_concrete_hLiouville

end ProofAudit
