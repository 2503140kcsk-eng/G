module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.Algebra.Field.Defs

public section

/-!
# Trusted statement baseline for AlgebraicFieldClosure

This module is the Comparator challenge side. Its six declarations fix the
exact propositions that the solution module must prove. The proof bodies
below are deliberately simple, checked proofs; the comparator compares
statement types and independently checks the corresponding declarations in
the solution module.

This file is not imported by the solution module.
-/

namespace AlgebraicFieldClosure

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

theorem isAlgebraic_inv {x : K} (hx : IsAlgebraic F x) :
    IsAlgebraic F x⁻¹ :=
  hx.inv

theorem isAlgebraic_nat_pow {x : K} (hx : IsAlgebraic F x) (n : ℕ) :
    IsAlgebraic F (x ^ n) :=
  (hx.isIntegral.pow n).isAlgebraic

theorem isAlgebraic_int_pow {x : K} (hx : IsAlgebraic F x) (n : ℤ) :
    IsAlgebraic F (x ^ n) := by
  cases n with
  | ofNat n =>
      simpa [zpow_ofNat] using (hx.isIntegral.pow n).isAlgebraic
  | negSucc n =>
      rw [zpow_negSucc]
      exact ((hx.isIntegral.pow (n + 1)).isAlgebraic).inv

theorem finiteDimensional_adjoin_of_algebraic
    {S : Set K} [Finite S] (hS : ∀ x ∈ S, IsAlgebraic F x) :
    FiniteDimensional F (IntermediateField.adjoin F S) := by
  apply IntermediateField.finiteDimensional_adjoin
  intro x hx
  exact (hS x hx).isIntegral

theorem algebraic_extension_of_finiteDimensional
    [FiniteDimensional F K] : Algebra.IsAlgebraic F K :=
  Algebra.IsAlgebraic.of_finite F K

theorem finite_iff_essFiniteType_and_algebraic :
    Module.Finite F K ↔
      Algebra.EssFiniteType F K ∧ Algebra.IsAlgebraic F K := by
  constructor
  · intro h
    let hFinite : Module.Finite F K := h
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hFiniteGeneration, hAlgebraic⟩
    let hFiniteGeneration' : Algebra.EssFiniteType F K := hFiniteGeneration
    let hAlgebraic' : Algebra.IsAlgebraic F K := hAlgebraic
    exact Algebra.finite_of_essFiniteType_of_isAlgebraic

end AlgebraicFieldClosure
