module
public import Mathlib
public import ProofAuditDefs
public import PolynomialApproximationDefs
public import CommonDenominatorApproximationDefs
public import FactorialTaylorFusionDefs

@[expose] public section

/-!
# Independent statement baseline for the project's public theorem surface

This module intentionally imports Mathlib only. It contains no project-local
definitions in theorem types. The solution module proves these exact public
statements by bridging to the project's named developments.

The sorry placeholders are challenge specifications only; the solution
module is checked by Lake Comparator, its permitted-axiom policy, Lean's
kernel, and every checker enabled by paranoid mode.
-/

open Filter Module Polynomial
open scoped Topology

namespace ProofAudit

theorem complex_e_transcendental :
    Transcendental ℤ (Complex.exp (1 : ℂ)) := by
  sorry

theorem real_pi_transcendental :
    Transcendental ℤ Real.pi := by
  sorry

theorem rational_e_transcendental :
    Transcendental ℚ (Real.exp 1) := by
  sorry

theorem rational_pi_transcendental :
    Transcendental ℚ Real.pi := by
  sorry

theorem e_add_pi_or_mul_transcendental :
    Transcendental ℚ (Real.exp 1 + Real.pi) ∨
      Transcendental ℚ (Real.exp 1 * Real.pi) := by
  sorry

theorem schanuel_implies_e_plus_pi_transcendental
    (hSC : ProofAuditDefs.SchanuelConjecture) :
    Transcendental ℚ (Real.exp 1 + Real.pi) := by
  sorry

theorem superpolynomial_forms_imply_transcendence
    {x : ℝ} {a : ℕ → ℕ} {b : ℕ → ℤ}
    (ha : Tendsto a atTop atTop)
    (hnz : ∀ᶠ n : ℕ in atTop,
      (a n : ℝ) * x + (b n : ℝ) ≠ 0)
    (hsmall : ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
      |(a n : ℝ) * x + (b n : ℝ)| <
        1 / ((max (a n) (b n).natAbs : ℕ) : ℝ) ^ k) :
    Transcendental ℚ x := by
  sorry

theorem integer_forms_tending_to_zero_imply_irrationality
    {x : ℝ} {A B : ℕ → ℤ}
    (hnz : ∀ᶠ n : ℕ in atTop,
      (A n : ℝ) * x + (B n : ℝ) ≠ 0)
    (hsmall : Tendsto
      (fun n : ℕ => |(A n : ℝ) * x + (B n : ℝ)|)
      atTop (𝓝 0)) :
    Irrational x := by
  sorry

theorem paired_integer_forms_tending_to_zero_imply_irrationality
    {x : ℝ} {A C : ℕ → ℤ}
    (hdet : ∀ᶠ n : ℕ in atTop,
      A n * C (n + 1) - A (n + 1) * C n ≠ 0)
    (hsmall : Tendsto
      (fun n : ℕ =>
        |(A n : ℝ) * x - (C n : ℝ)| +
          |(A (n + 1) : ℝ) * x - (C (n + 1) : ℝ)|)
      atTop (𝓝 0)) :
    Irrational x := by
  sorry

theorem algebraic_elements_mem_iff
    (K E : Type*) [Field K] [Field E] [Algebra K E] {x : E} :
    x ∈ algebraicClosure K E ↔ IsAlgebraic K x := by
  sorry

theorem algebraic_elements_carrier_eq
    (K E : Type*) [Field K] [Field E] [Algebra K E] :
    {x : E | IsAlgebraic K x} = (algebraicClosure K E : Set E) := by
  sorry

theorem algebraic_elements_add_closed
    (K E : Type*) [Field K] [Field E] [Algebra K E] {x y : E}
    (hx : IsAlgebraic K x) (hy : IsAlgebraic K y) :
    IsAlgebraic K (x + y) := by
  sorry

theorem algebraic_elements_neg_closed
    (K E : Type*) [Field K] [Field E] [Algebra K E] {x : E}
    (hx : IsAlgebraic K x) :
    IsAlgebraic K (-x) := by
  sorry

theorem algebraic_elements_sub_closed
    (K E : Type*) [Field K] [Field E] [Algebra K E] {x y : E}
    (hx : IsAlgebraic K x) (hy : IsAlgebraic K y) :
    IsAlgebraic K (x - y) := by
  sorry

theorem algebraic_elements_mul_closed
    (K E : Type*) [Field K] [Field E] [Algebra K E] {x y : E}
    (hx : IsAlgebraic K x) (hy : IsAlgebraic K y) :
    IsAlgebraic K (x * y) := by
  sorry

theorem algebraic_elements_inv_closed
    (K E : Type*) [Field K] [Field E] [Algebra K E] {x : E}
    (hx : IsAlgebraic K x) :
    IsAlgebraic K x⁻¹ := by
  sorry

theorem algebraic_elements_div_closed
    (K E : Type*) [Field K] [Field E] [Algebra K E] {x y : E}
    (hx : IsAlgebraic K x) (hy : IsAlgebraic K y) :
    IsAlgebraic K (x / y) := by
  sorry

theorem algebraic_elements_zpow_closed
    (K E : Type*) [Field K] [Field E] [Algebra K E] {x : E}
    (hx : IsAlgebraic K x) (n : ℤ) :
    IsAlgebraic K (x ^ n) := by
  sorry

theorem algebraic_elements_field_is_algebraic
    (K E : Type*) [Field K] [Field E] [Algebra K E] :
    Algebra.IsAlgebraic K (algebraicClosure K E) := by
  sorry

theorem algebraic_elements_maximality
    (K E : Type*) [Field K] [Field E] [Algebra K E]
    (L : IntermediateField K E) :
    L ≤ algebraicClosure K E ↔ Algebra.IsAlgebraic K L := by
  sorry

theorem algebraic_elements_isAlgClosure_of_algClosed_ambient
    (K E : Type*) [Field K] [Field E] [Algebra K E] [IsAlgClosed E] :
    IsAlgClosure K (algebraicClosure K E) := by
  sorry

theorem algebraic_elements_field_isAlgClosed
    (K E : Type*) [Field K] [Field E] [Algebra K E] [IsAlgClosed E] :
    IsAlgClosed (algebraicClosure K E) := by
  sorry

theorem algebraic_elements_every_polynomial_splits
    (K E : Type*) [Field K] [Field E] [Algebra K E] [IsAlgClosed E]
    (p : Polynomial (algebraicClosure K E)) :
    p.Splits := by
  sorry

theorem algebraic_elements_exists_root
    (K E : Type*) [Field K] [Field E] [Algebra K E] [IsAlgClosed E]
    (p : Polynomial (algebraicClosure K E)) (hp : p.degree ≠ 0) :
    ∃ x : algebraicClosure K E, IsRoot p x := by
  sorry

universe u v

theorem algebraic_elements_uniqueness_up_to_algEquiv
    (K : Type u) [Field K]
    (A B : Type v) [Field A] [Field B]
    [Algebra K A] [Algebra K B]
    [IsTorsionFree K A] [IsTorsionFree K B]
    [IsAlgClosure K A] [IsAlgClosure K B] :
    Nonempty (A ≃ₐ[K] B) := by
  sorry

theorem finiteDimensional_adjoin_of_algebraic
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    {S : Set K} [Finite S] (hS : ∀ x ∈ S, IsAlgebraic F x) :
    FiniteDimensional F (IntermediateField.adjoin F S) := by
  sorry

theorem algebraic_extension_of_finiteDimensional
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] :
    Algebra.IsAlgebraic F K := by
  sorry

theorem finite_iff_essFiniteType_and_algebraic
    {F K : Type*} [Field F] [Field K] [Algebra F K] :
    Module.Finite F K ↔
      Algebra.EssFiniteType F K ∧ Algebra.IsAlgebraic F K := by
  sorry


/-- The explicit simultaneous approximation family has integer endpoint data,
    nonzero endpoint determinant, exact reciprocal representation, and a
    uniform exponential error tending to zero. -/
theorem simultaneous_polynomial_approximation_certificate
    (n : ℕ) (hn : 1 ≤ n) :
    (SimultaneousPolynomialApproximation.endpointMatrix n).det ≠ 0 ∧
    (∀ x ∈ Set.Icc (-1) 1,
      |SimultaneousPolynomialApproximation.evalReal
          (SimultaneousPolynomialApproximation.denominator n) x * Real.exp x -
        SimultaneousPolynomialApproximation.evalReal
          (SimultaneousPolynomialApproximation.numerator n) x|
          ≤ 4 / (n + 1 : ℝ)) ∧
    (∀ x : ℝ,
      SimultaneousPolynomialApproximation.evalReal
          (SimultaneousPolynomialApproximation.denominator n) x *
            (1 + x ^ 2)⁻¹ =
        SimultaneousPolynomialApproximation.evalReal
          (SimultaneousPolynomialApproximation.reciprocalNumerator n) x) ∧
    (∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
        (4 : ℝ) / (m + 1 : ℝ) < ε) := by
  sorry


/-- Separate rational approximants can be fused into an integer form for
    the sum only when the cross-multiplied error budget tends to zero. -/
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
    Irrational (x + y) := by
  sorry


/-- Any rational pi denominators compatible with the current factorial Taylor
    approximants to e must be sublinear in the Taylor index if the fused errors
    are to tend to zero. -/
theorem factorial_taylor_fusion_forces_sublinear_pi_denominators
    {r : ℕ → ℕ} {s : ℕ → ℤ}
    (hsmall : Filter.Tendsto
      (FactorialTaylorFusion.factorialTaylorFusionError r s)
      Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n : ℕ => (r n : ℝ) / (n + 1 : ℝ))
      Filter.atTop (𝓝 0) := by
  sorry


/-- A uniform lower bound for pi-side integer linear forms rules out vanishing
    cross-weighted error for the current factorial Taylor approximants to e. -/
theorem factorial_taylor_fusion_no_go_from_pi_measure_lower_bound
    {r : ℕ → ℕ} {s : ℕ → ℤ} {c : ℝ}
    (hc : 0 < c)
    (hrpos : ∀ n, 0 < r n)
    (hpi : ∀ n,
      c / (r n : ℝ) ^ 7 ≤
        |(r n : ℝ) * Real.pi - (s n : ℝ)|) :
    ¬ Filter.Tendsto (FactorialTaylorFusion.factorialTaylorFusionError r s)
      Filter.atTop (𝓝 0) := by
  sorry


/-- A Bezout-primitive integer pair spans every integer pair on its rational line.
    This is the rank-one arithmetic kernel lemma needed for endpoint-lattice
    intersections: the determinant condition expresses collinearity, while
    the Bezout identity supplies saturation. -/
theorem integer_pair_multiple_of_bezout_and_determinant
    {a b c d : ℤ}
    (hbez : ∃ u v : ℤ, u * a + v * b = 1)
    (hdet : a * d = b * c) :
    ∃ k : ℤ, c = k * a ∧ d = k * b := by
  sorry


/-- Gcd one is an intrinsic arithmetic form of Bezout primitivity. -/
theorem integer_pair_multiple_of_gcd_one_and_determinant
    {a b c d : ℤ}
    (hcoprime : Int.gcd a b = 1)
    (hdet : a * d = b * c) :
    ∃ k : ℤ, c = k * a ∧ d = k * b := by
  sorry

/-- The common kernel of rows collinear with a primitive anchor row is
    exactly the kernel of that anchor row. -/
theorem integer_row_kernel_iff_anchor
    {ι : Type*} (i₀ : ι) {a b : ℤ} (A B : ι → ℤ)
    (hA₀ : A i₀ = a) (hB₀ : B i₀ = b)
    (hbez : ∃ u v : ℤ, u * a + v * b = 1)
    (hcollinear : ∀ i, a * B i = b * A i)
    (x y : ℤ) :
    (∀ i, A i * x + B i * y = 0) ↔ a * x + b * y = 0 := by
  sorry

/-- The row-kernel theorem with primitivity expressed by gcd one. -/
theorem integer_row_kernel_iff_anchor_of_gcd_one
    {ι : Type*} (i₀ : ι) {a b : ℤ} (A B : ι → ℤ)
    (hA₀ : A i₀ = a) (hB₀ : B i₀ = b)
    (hcoprime : Int.gcd a b = 1)
    (hcollinear : ∀ i, a * B i = b * A i)
    (x y : ℤ) :
    (∀ i, A i * x + B i * y = 0) ↔ a * x + b * y = 0 := by
  sorry



/-- Gcd one yields an explicit integer Bezout witness. -/
theorem exists_bezout_of_int_gcd_eq_one
    {a b : ℤ} (hcoprime : Int.gcd a b = 1) :
    ∃ u v : ℤ, u * a + v * b = 1 := by
  sorry

/-- A two-column integer matrix whose rows are all collinear with a primitive
    anchor row has exactly the anchor row's integer kernel. -/
theorem integer_two_column_matrix_kernel_iff_anchor
    {ι : Type*} (i₀ : ι) (M : Matrix ι (Fin 2) ℤ)
    {a b : ℤ}
    (hA₀ : M i₀ 0 = a) (hB₀ : M i₀ 1 = b)
    (hbez : ∃ u v : ℤ, u * a + v * b = 1)
    (hminor : ∀ i, a * M i 1 = b * M i 0)
    (x y : ℤ) :
    (∀ i, M i 0 * x + M i 1 * y = 0) ↔ a * x + b * y = 0 := by
  sorry

/-- Without anchor primitivity, the integer-multiple conclusion is false. -/
theorem nonprimitive_pair_counterexample :
    (2 : ℤ) * 1 = 2 * 1 ∧
      ¬ ∃ k : ℤ, (1 : ℤ) = k * 2 ∧ 1 = k * 2 := by
  sorry


/-- A primitive integer row has its kernel generated by the perpendicular
    primitive vector. -/
theorem integer_pair_kernel_iff_primitive_generator
    {a b x y : ℤ}
    (hbez : ∃ u v : ℤ, u * a + v * b = 1) :
    a * x + b * y = 0 ↔
      ∃ k : ℤ, x = -b * k ∧ y = a * k := by
  sorry

/-- The common kernel of a primitive rank-one two-column integer matrix is
    exactly the Z-span of the perpendicular anchor vector. -/
theorem integer_two_column_matrix_kernel_eq_zsmul_anchor
    {ι : Type*} (i₀ : ι) (M : Matrix ι (Fin 2) ℤ)
    {a b : ℤ}
    (hA₀ : M i₀ 0 = a) (hB₀ : M i₀ 1 = b)
    (hbez : ∃ u v : ℤ, u * a + v * b = 1)
    (hminor : ∀ i, a * M i 1 = b * M i 0)
    (x y : ℤ) :
    (∀ i, M i 0 * x + M i 1 * y = 0) ↔
      ∃ k : ℤ, x = -b * k ∧ y = a * k := by
  sorry

/-- The same cyclic kernel theorem with primitivity expressed by gcd one. -/
theorem integer_two_column_matrix_kernel_eq_zsmul_anchor_of_gcd_one
    {ι : Type*} (i₀ : ι) (M : Matrix ι (Fin 2) ℤ)
    {a b : ℤ}
    (hA₀ : M i₀ 0 = a) (hB₀ : M i₀ 1 = b)
    (hcoprime : Int.gcd a b = 1)
    (hminor : ∀ i, a * M i 1 = b * M i 0)
    (x y : ℤ) :
    (∀ i, M i 0 * x + M i 1 * y = 0) ↔
      ∃ k : ℤ, x = -b * k ∧ y = a * k := by
  sorry

/-- Without a primitive row, the perpendicular vector need not generate the
    entire integer kernel. -/
theorem nonprimitive_row_kernel_counterexample :
    (2 : ℤ) * 0 + 0 * 1 = 0 ∧
      ¬ ∃ k : ℤ, (0 : ℤ) = -0 * k ∧ 1 = 2 * k := by
  sorry


/-- If all rows are collinear with a primitive anchor direction and at least
    one row is nonzero, the common kernel equals the anchor kernel. -/
theorem integer_row_kernel_iff_anchor_of_nonzero
    {ι : Type*} {a b : ℤ} (A B : ι → ℤ)
    (hbez : ∃ u v : ℤ, u * a + v * b = 1)
    (hcollinear : ∀ i, a * B i = b * A i)
    (hnonzero : ∃ i, A i ≠ 0 ∨ B i ≠ 0)
    (x y : ℤ) :
    (∀ i, A i * x + B i * y = 0) ↔ a * x + b * y = 0 := by
  sorry

/-- Matrix form of the nonzero-row rank-one kernel reduction. -/
theorem integer_two_column_matrix_kernel_iff_anchor_of_nonzero
    {ι : Type*} (M : Matrix ι (Fin 2) ℤ)
    {a b : ℤ}
    (hbez : ∃ u v : ℤ, u * a + v * b = 1)
    (hminor : ∀ i, a * M i 1 = b * M i 0)
    (hnonzero : ∃ i, M i 0 ≠ 0 ∨ M i 1 ≠ 0)
    (x y : ℤ) :
    (∀ i, M i 0 * x + M i 1 * y = 0) ↔ a * x + b * y = 0 := by
  sorry

/-- The integer kernel is generated by the perpendicular primitive vector,
    even when that vector is not one of the actual source rows. -/
theorem integer_two_column_matrix_kernel_eq_zsmul_anchor_of_nonzero
    {ι : Type*} (M : Matrix ι (Fin 2) ℤ)
    {a b : ℤ}
    (hbez : ∃ u v : ℤ, u * a + v * b = 1)
    (hminor : ∀ i, a * M i 1 = b * M i 0)
    (hnonzero : ∃ i, M i 0 ≠ 0 ∨ M i 1 ≠ 0)
    (x y : ℤ) :
    (∀ i, M i 0 * x + M i 1 * y = 0) ↔
      ∃ k : ℤ, x = -b * k ∧ y = a * k := by
  sorry

/-- Gcd-one form of the nonzero-row cyclic matrix-kernel theorem. -/
theorem integer_two_column_matrix_kernel_eq_zsmul_anchor_of_nonzero_gcd_one
    {ι : Type*} (M : Matrix ι (Fin 2) ℤ)
    {a b : ℤ}
    (hcoprime : Int.gcd a b = 1)
    (hminor : ∀ i, a * M i 1 = b * M i 0)
    (hnonzero : ∃ i, M i 0 ≠ 0 ∨ M i 1 ≠ 0)
    (x y : ℤ) :
    (∀ i, M i 0 * x + M i 1 * y = 0) ↔
      ∃ k : ℤ, x = -b * k ∧ y = a * k := by
  sorry


/-- Split–Machin endpoint form: the primitive old success vector (b₀,δ)
    generates the full integer kernel once all rows annihilate it and the
    endpoint matrix is nonzero. -/
theorem integer_endpoint_kernel_from_primitive_success
    {ι : Type*} (M : Matrix ι (Fin 2) ℤ)
    {b₀ δ : ℤ}
    (hcoprime : Int.gcd b₀ δ = 1)
    (hsuccess : ∀ i, M i 0 * b₀ + M i 1 * δ = 0)
    (hnonzero : ∃ i, M i 0 ≠ 0 ∨ M i 1 ≠ 0)
    (x y : ℤ) :
    (∀ i, M i 0 * x + M i 1 * y = 0) ↔
      ∃ k : ℤ, x = b₀ * k ∧ y = δ * k := by
  sorry


/-- A row annihilating the old success vector satisfies the anchor minor. -/
theorem endpoint_success_row_implies_anchor_minor
    {b₀ δ A B : ℤ}
    (hsuccess : A * b₀ + B * δ = 0) :
    δ * B = (-b₀) * A := by
  sorry

/-- The anchor-minor identity holds uniformly over all endpoint rows. -/
theorem endpoint_success_rows_imply_anchor_minors
    {ι : Type*} {b₀ δ : ℤ} (A B : ι → ℤ)
    (hsuccess : ∀ i, A i * b₀ + B i * δ = 0) :
    ∀ i, δ * B i = (-b₀) * A i := by
  sorry


/-- A modular dual certificate excludes a target from the integer column
    lattice without computing a Smith normal form. -/
theorem not_mem_integer_column_span_of_modular_dual
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ)
    (y : Fin m → ℤ) (q : ℤ) (s : Fin m → ℤ)
    (hcolumns : ∀ j : Fin n, q ∣ ∑ i : Fin m, s i * A i j)
    (htarget : ¬ q ∣ ∑ i : Fin m, s i * y i) :
    ¬ ∃ c : Fin n → ℤ,
        ∀ i : Fin m, y i = ∑ j : Fin n, A i j * c j := by
  sorry

/-- A real sequence with a finite limit times a sequence tending to zero
    again tends to zero. This is the scalar convergence step used by the
    primitive integerization criterion. -/
theorem finite_ratio_weighted_error_tendsto_zero
    {ratio error : ℕ → ℝ} {b : ℝ}
    (hratio : Filter.Tendsto ratio Filter.atTop (𝓝 b))
    (herr : Filter.Tendsto error Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n => ratio n * error n) Filter.atTop (𝓝 0) := by
  sorry

/-- The index tower for adjoining a single vector to an integer lattice. -/
theorem cyclic_extension_relative_index_identity
    {m : ℕ} (L : AddSubgroup (Fin m → ℤ)) (w : Fin m → ℤ) :
    L.relIndex (L ⊔ AddSubgroup.zmultiples w) *
      (L ⊔ AddSubgroup.zmultiples w).index = L.index := by
  sorry

/-- The index after adjoining a vector divides the original finite index. -/
theorem cyclic_extension_index_dvd
    {m : ℕ} (L : AddSubgroup (Fin m → ℤ)) (w : Fin m → ℤ) :
    (L ⊔ AddSubgroup.zmultiples w).index ∣ L.index := by
  sorry

/-- A relative index is the absolute determinant of the basis-change matrix. -/
theorem relative_index_eq_natAbs_basis_change_det
    {E : Type*} [AddCommGroup E]
    (L₁ L₂ : AddSubgroup E) (hL : L₁ ≤ L₂)
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b₁ : Basis ι ℤ L₁.toIntSubmodule)
    (b₂ : Basis ι ℤ L₂.toIntSubmodule) :
    L₁.relIndex L₂ =
      (b₂.det (fun i => ⟨b₁ i, hL (SetLike.coe_mem _)⟩)).natAbs := by
  sorry

/-- A full-rank lattice index equals the absolute determinant of its basis. -/
theorem lattice_index_eq_natAbs_basis_det
    {E : Type*} [AddCommGroup E] {m : ℕ}
    (bE : Basis (Fin m) ℤ E)
    (L : AddSubgroup E)
    (bL : Basis (Fin m) ℤ L) :
    L.index = (bE.det (bL ·)).natAbs := by
  sorry

end ProofAudit
