module
public import ResultantPairedCriterion
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Polynomial.CauchyBound
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Polynomial.Content
public import Mathlib.RingTheory.Polynomial.GaussLemma

@[expose] public section

open Polynomial

namespace EPlusPiApproximation

/-- A product over a finite multiset is bounded by a power when every factor is bounded. -/
private theorem norm_multiset_map_prod_le_pow
    {α : Type*} (s : Multiset α) (f : α → ℂ) (B : ℝ)
    (hB : 0 ≤ B) (hf : ∀ x ∈ s, ‖f x‖ ≤ B) :
    ‖(s.map f).prod‖ ≤ B ^ s.card := by
  classical
  induction s using Multiset.induction_on with
  | empty =>
      simp
  | @cons a s ih =>
      have ha : ‖f a‖ ≤ B := hf a (by simp)
      have hs : ∀ x ∈ s, ‖f x‖ ≤ B := by
        intro x hx
        exact hf x (by simp [hx])
      rw [Multiset.map_cons, Multiset.prod_cons, norm_mul, Multiset.card_cons]
      calc
        ‖f a‖ * ‖(s.map f).prod‖ ≤ B * B ^ s.card :=
          mul_le_mul ha (ih hs) (norm_nonneg _) hB
        _ = B ^ (s.card + 1) := by ring

/--
If an integer polynomial f and an integer polynomial g are coprime after
mapping to Q[X], their integer resultant is nonzero. The proof transports
the resultant to Q and uses Mathlib's field result.
-/
theorem int_resultant_ne_zero_of_rat_coprime
    (f g : Polynomial ℤ)
    (hcop : IsCoprime
      (f.map (algebraMap ℤ ℚ))
      (g.map (algebraMap ℤ ℚ))) :
    Polynomial.resultant f g ≠ 0 := by
  have hQ : Polynomial.resultant
      (f.map (algebraMap ℤ ℚ))
      (g.map (algebraMap ℤ ℚ)) ≠ 0 :=
    Polynomial.resultant_ne_zero _ _ hcop
  have hfi : Function.Injective (algebraMap ℤ ℚ) :=
    RingHom.injective_int (algebraMap ℤ ℚ)
  have hdegf :
      (f.map (algebraMap ℤ ℚ)).natDegree = f.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hfi f
  have hdegg :
      (g.map (algebraMap ℤ ℚ)).natDegree = g.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hfi g
  have hmapResultant :
      Polynomial.resultant (f.map (algebraMap ℤ ℚ))
          (g.map (algebraMap ℤ ℚ)) =
        algebraMap ℤ ℚ (Polynomial.resultant f g) := by
    rw [Polynomial.resultant_map_map, hdegf, hdegg]
  intro hzero
  apply hQ
  rw [hmapResultant, hzero, map_zero]

/--
A resultant lower bound at one selected complex root.

The other roots of f may be repeated; the multiset formulation keeps their
multiplicities. The hypothesis hOther bounds g at every root except the
selected occurrence alpha. The integer resultant is nonzero because f and
g are coprime over Q, so its absolute value is at least one.
-/
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
          B ^ ((f.map (algebraMap ℤ ℂ)).natDegree - 1) := by
  classical
  let fC : Polynomial ℂ := f.map (algebraMap ℤ ℂ)
  let gC : Polynomial ℂ := g.map (algebraMap ℤ ℂ)
  have hfSplits : fC.Splits := IsAlgClosed.splits fC
  have hresZ : Polynomial.resultant f g ≠ 0 :=
    int_resultant_ne_zero_of_rat_coprime f g hcop
  have hfiC : Function.Injective (Int.castRingHom ℂ) :=
    Int.cast_injective
  have hdegfC :
      (f.map (Int.castRingHom ℂ)).natDegree = f.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hfiC f
  have hdeggC :
      (g.map (Int.castRingHom ℂ)).natDegree = g.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hfiC g
  have hdegfC' :
      (f.map (algebraMap ℤ ℂ)).natDegree = f.natDegree := by
    change (f.map (Int.castRingHom ℂ)).natDegree = f.natDegree
    exact hdegfC
  have hdeggC' :
      (g.map (algebraMap ℤ ℂ)).natDegree = g.natDegree := by
    change (g.map (Int.castRingHom ℂ)).natDegree = g.natDegree
    exact hdeggC
  have hmapResultantC :
      Polynomial.resultant fC gC =
        algebraMap ℤ ℂ (Polynomial.resultant f g) := by
    change Polynomial.resultant (f.map (Int.castRingHom ℂ))
        (g.map (Int.castRingHom ℂ)) =
      (Int.castRingHom ℂ) (Polynomial.resultant f g)
    rw [Polynomial.resultant_map_map, hdegfC, hdeggC]
  have hresAbs : (1 : ℝ) ≤ ‖Polynomial.resultant fC gC‖ := by
    have hInt : (1 : ℝ) ≤ |Polynomial.resultant f g| := by
      exact_mod_cast Int.one_le_abs hresZ
    have hCast :
        ‖algebraMap ℤ ℂ (Polynomial.resultant f g)‖ =
          |Polynomial.resultant f g| := by
      simp
    calc
      (1 : ℝ) ≤ |Polynomial.resultant f g| := hInt
      _ = ‖algebraMap ℤ ℂ (Polynomial.resultant f g)‖ := hCast.symm
      _ = ‖Polynomial.resultant fC gC‖ := by rw [← hmapResultantC]
  have hαC : α ∈ fC.roots := by
    exact hα
  have hresultantFormula :
      Polynomial.resultant fC gC =
        fC.leadingCoeff ^ gC.natDegree *
          (fC.roots.map gC.eval).prod := by
    exact Polynomial.resultant_eq_prod_eval fC gC gC.natDegree le_rfl hfSplits
  have hmapRoots :
      fC.roots.map gC.eval =
        gC.eval α ::ₘ ((fC.roots.erase α).map gC.eval) := by
    calc
      fC.roots.map gC.eval =
          (α ::ₘ fC.roots.erase α).map gC.eval := by
            rw [Multiset.cons_erase hαC]
      _ = gC.eval α ::ₘ ((fC.roots.erase α).map gC.eval) := by
            simp
  have hformulaNorm :
      ‖Polynomial.resultant fC gC‖ =
        ‖fC.leadingCoeff‖ ^ gC.natDegree *
          (‖gC.eval α‖ *
            ‖((fC.roots.erase α).map gC.eval).prod‖) := by
    rw [hresultantFormula, hmapRoots, Multiset.prod_cons]
    simp only [norm_mul, norm_pow]
  have hOtherProd :
      ‖((fC.roots.erase α).map gC.eval).prod‖ ≤
        B ^ (fC.natDegree - 1) := by
    have h := norm_multiset_map_prod_le_pow (fC.roots.erase α) gC.eval B hB hOther
    have hcard :
        (fC.roots.erase α).card = fC.natDegree - 1 := by
      calc
        (fC.roots.erase α).card = fC.roots.card - 1 :=
          Multiset.card_erase_of_mem hαC
        _ = fC.natDegree - 1 := by
          rw [← hfSplits.natDegree_eq_card_roots]
    rw [hcard] at h
    exact h
  have hbound :
      (1 : ℝ) ≤
        ‖fC.leadingCoeff‖ ^ gC.natDegree *
          (‖gC.eval α‖ * B ^ (fC.natDegree - 1)) := by
    calc
      (1 : ℝ) ≤ ‖Polynomial.resultant fC gC‖ := hresAbs
      _ = ‖fC.leadingCoeff‖ ^ gC.natDegree *
            (‖gC.eval α‖ *
              ‖((fC.roots.erase α).map gC.eval).prod‖) := hformulaNorm
      _ ≤ ‖fC.leadingCoeff‖ ^ gC.natDegree *
            (‖gC.eval α‖ * B ^ (fC.natDegree - 1)) := by
        gcongr
  calc
    (1 : ℝ) ≤
        ‖(f.map (algebraMap ℤ ℂ)).leadingCoeff‖ ^ g.natDegree *
          ‖(g.map (algebraMap ℤ ℂ)).eval α‖ *
            B ^ ((f.map (algebraMap ℤ ℂ)).natDegree - 1) := by
      simpa only [fC, gC, hdegfC', hdeggC', mul_assoc] using hbound

/-- Evaluation bound from a coefficient bound and a bound on the argument. -/
private theorem norm_eval_le_of_coeff_bound
    (p : Polynomial ℂ) (z : ℂ) (H C : ℝ)
    (hH : 0 ≤ H) (hC : 1 ≤ C) (hz : ‖z‖ ≤ C)
    (hcoeff : ∀ i, ‖p.coeff i‖ ≤ H) :
    ‖p.eval z‖ ≤ ((p.natDegree + 1 : ℕ) : ℝ) * H * C ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range]
  calc
    ‖∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * z ^ i‖ ≤
        ∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i * z ^ i‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), H * C ^ p.natDegree := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ p.natDegree :=
        Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      calc
        ‖p.coeff i * z ^ i‖ = ‖p.coeff i‖ * ‖z‖ ^ i := by
          simp [norm_pow]
        _ ≤ H * C ^ i :=
          mul_le_mul (hcoeff i)
            (pow_le_pow_left₀ (norm_nonneg z) hz i)
            (pow_nonneg (norm_nonneg z) i) hH
        _ ≤ H * C ^ p.natDegree :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hC hi') hH
    _ = ((p.natDegree + 1 : ℕ) : ℝ) * H * C ^ p.natDegree := by
      simp
      ring

/--
The resultant lower bound with the other-root estimate discharged from a
uniform coefficient bound and the Cauchy root bound of the fixed polynomial.
This is the concrete bridge from coefficient height to the root-product estimate.
-/
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
            ((f.map (algebraMap ℤ ℂ)).natDegree - 1)) := by
  classical
  let fC : Polynomial ℂ := f.map (algebraMap ℤ ℂ)
  let gC : Polynomial ℂ := g.map (algebraMap ℤ ℂ)
  let C : ℝ := (Polynomial.cauchyBound fC : ℝ)
  let B : ℝ := ((gC.natDegree + 1 : ℕ) : ℝ) * H * C ^ gC.natDegree
  have hdeggC :
      (g.map (Int.castRingHom ℂ)).natDegree = g.natDegree :=
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective g
  have hC : 1 ≤ C := by
    exact_mod_cast Polynomial.one_le_cauchyBound fC
  have hfC0 : fC ≠ 0 := by
    intro hf
    have hzero : f.map (Int.castRingHom ℂ) = 0 := by
      change f.map (algebraMap ℤ ℂ) = 0
      simpa [fC] using hf
    simp [hzero] at hα
  have hRoots : ∀ z ∈ fC.roots.erase α, ‖z‖ ≤ C := by
    intro z hz
    have hz' : z ∈ fC.roots := Multiset.mem_of_mem_erase hz
    have hroot : fC.IsRoot z := (Polynomial.mem_roots hfC0).mp hz'
    have hbound := Polynomial.IsRoot.norm_lt_cauchyBound hfC0 hroot
    change ‖z‖ ≤ (Polynomial.cauchyBound fC : ℝ)
    exact_mod_cast hbound.le
  have hOther : ∀ z ∈ fC.roots.erase α, ‖gC.eval z‖ ≤ B := by
    intro z hz
    have h := norm_eval_le_of_coeff_bound gC z H C hH hC (hRoots z hz) hcoeff
    simpa [B] using h
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hMain :=
    resultant_eval_lower_bound_of_other_roots f g α B hcop hα hB hOther
  change 1 ≤
    ‖(f.map (Int.castRingHom ℂ)).leadingCoeff‖ ^
        (g.map (Int.castRingHom ℂ)).natDegree *
      ‖(g.map (Int.castRingHom ℂ)).eval α‖ *
        (((((g.map (Int.castRingHom ℂ)).natDegree + 1 : ℕ) : ℝ) * H *
            (Polynomial.cauchyBound (f.map (Int.castRingHom ℂ)) : ℝ) ^
              (g.map (Int.castRingHom ℂ)).natDegree) ^
          ((f.map (Int.castRingHom ℂ)).natDegree - 1))
  simpa [fC, gC, B, C, hdeggC] using hMain

/--
Every algebraic real has a nonzero integer-coefficient polynomial that
vanishes at it.  We obtain it by clearing the denominators of a nonzero
rational polynomial relation; integerNormalization preserves the root.
-/
theorem exists_nonzero_integer_polynomial_vanishing_of_algebraic
    {x : ℝ} (hx : IsAlgebraic ℚ x) :
    ∃ f : Polynomial ℤ, f ≠ 0 ∧ Polynomial.aeval x f = 0 := by
  obtain ⟨p, hp, hpx⟩ := hx
  let f : Polynomial ℤ :=
    IsLocalization.integerNormalization (nonZeroDivisors ℤ) p
  have hf : f ≠ 0 := by
    intro h
    apply hp
    exact (IsFractionRing.integerNormalization_eq_zero_iff
      (A := ℤ) (K := ℚ)).mp (by simpa [f] using h)
  have hfx : Polynomial.aeval x f = 0 := by
    simpa [f] using
      (IsLocalization.integerNormalization_aeval_eq_zero
        (M := nonZeroDivisors ℤ) p hpx)
  exact ⟨f, hf, hfx⟩

/--
An algebraic real number has a primitive irreducible integer polynomial
vanishing at it.  We normalize its rational minimal polynomial to integral
coefficients, remove the content, and apply Gauss's lemma.
-/
theorem exists_primitive_irreducible_integer_polynomial_vanishing_of_algebraic
    {x : ℝ} (hx : IsAlgebraic ℚ x) :
    ∃ f : Polynomial ℤ, f ≠ 0 ∧ f.IsPrimitive ∧
      Irreducible f ∧ Polynomial.aeval x f = 0 := by
  classical
  have hxI : IsIntegral ℚ x := IsAlgebraic.isIntegral hx
  let m : Polynomial ℚ := minpoly ℚ x
  have hm0 : m ≠ 0 := by
    change minpoly ℚ x ≠ 0
    exact minpoly.ne_zero hxI
  have hmIrr : Irreducible m := by
    change Irreducible (minpoly ℚ x)
    exact minpoly.irreducible hxI
  have hmRoot : Polynomial.aeval x m = 0 := by
    change Polynomial.aeval x (minpoly ℚ x) = 0
    exact minpoly.aeval ℚ x
  let n : Polynomial ℤ :=
    IsLocalization.integerNormalization (nonZeroDivisors ℤ) m
  let f : Polynomial ℤ := n.primPart
  have hn0 : n ≠ 0 := by
    intro hn
    have hmz : m = 0 :=
      (IsFractionRing.integerNormalization_eq_zero_iff
        (A := ℤ) (K := ℚ)).mp (by simpa [n] using hn)
    exact hm0 hmz
  have hf0 : f ≠ 0 := by
    exact Polynomial.primPart_ne_zero n
  have hPrim : f.IsPrimitive := by
    exact n.isPrimitive_primPart
  have hRootN : Polynomial.aeval x n = 0 := by
    dsimp [n]
    exact IsLocalization.integerNormalization_aeval_eq_zero
      (M := nonZeroDivisors ℤ) m hmRoot
  have hRootF : Polynomial.aeval x f = 0 := by
    dsimp [f]
    exact Polynomial.aeval_primPart_eq_zero hn0 hRootN
  obtain ⟨b, hb, hbNorm⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) m
  have hbQ : (algebraMap ℤ ℚ) b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hNormMap :
      n.map (algebraMap ℤ ℚ) =
        C (algebraMap ℤ ℚ b) * m := by
    calc
      n.map (algebraMap ℤ ℚ) = b • m := by
        simpa [n] using hbNorm
      _ = (algebraMap ℤ ℚ b) • m := by
        rw [← IsScalarTower.algebraMap_smul ℚ b m]
      _ = C (algebraMap ℤ ℚ b) * m :=
        Polynomial.smul_eq_C_mul (algebraMap ℤ ℚ b)
  have hContent0 : n.content ≠ 0 := by
    intro hc
    exact hn0 (Polynomial.content_eq_zero_iff.mp hc)
  have hContentQ : (algebraMap ℤ ℚ) n.content ≠ 0 := by
    intro h
    have hzero : n.content = 0 :=
      (RingHom.injective_int (algebraMap ℤ ℚ)) (by simpa using h)
    exact hContent0 hzero
  have hContentMap :
      n.map (algebraMap ℤ ℚ) =
        C (algebraMap ℤ ℚ n.content) * f.map (algebraMap ℤ ℚ) := by
    calc
      n.map (algebraMap ℤ ℚ) =
          (C n.content * n.primPart).map (algebraMap ℤ ℚ) := by
        exact congrArg (fun p : Polynomial ℤ => p.map (algebraMap ℤ ℚ))
          n.eq_C_content_mul_primPart
      _ = C (algebraMap ℤ ℚ n.content) * f.map (algebraMap ℤ ℚ) := by
        simp [f, Polynomial.map_mul]
  have hProduct :
      C (algebraMap ℤ ℚ n.content) * f.map (algebraMap ℤ ℚ) =
        C (algebraMap ℤ ℚ b) * m := by
    rw [← hContentMap, hNormMap]
  have hAssoc : Associated m (f.map (algebraMap ℤ ℚ)) :=
    (associated_unit_mul_left _ _ (isUnit_C.mpr hbQ.isUnit)).symm.trans
      ((Associated.of_eq hProduct.symm).trans
        (associated_unit_mul_left _ _ (isUnit_C.mpr hContentQ.isUnit)))
  have hMapIrr : Irreducible (f.map (Int.castRingHom ℚ)) := by
    change Irreducible (f.map (algebraMap ℤ ℚ))
    exact hAssoc.irreducible hmIrr
  have hfIrr : Irreducible f :=
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hPrim).2
      hMapIrr
  exact ⟨f, hf0, hPrim, hfIrr, hRootF⟩

#print axioms exists_primitive_irreducible_integer_polynomial_vanishing_of_algebraic

#print axioms exists_nonzero_integer_polynomial_vanishing_of_algebraic
#print axioms int_resultant_ne_zero_of_rat_coprime
#print axioms resultant_eval_lower_bound_of_other_roots


/-!
Explicit height/degree form of the algebraic lower bound.

An integerized sequence stores a rational polynomial together with an
integer polynomial numerator and a positive integer denominator.  The
following theorems turn coefficient-height, logarithmic-degree, and
denominator bounds into the concrete fixed-power lower bound required by
the paired criterion.
-/

/-- Exact integerization of a rational-polynomial sequence. -/
structure IntegerizedPolynomialSequence (P : ℕ → Polynomial ℚ) where
  numerator : ℕ → Polynomial ℤ
  denominator : ℕ → ℕ
  denominator_pos : ∀ n, 0 < denominator n
  map_eq : ∀ n,
    (numerator n).map (algebraMap ℤ ℚ) =
      C (denominator n : ℚ) * P n

/-- The elementary estimate n + 1 ≤ 2^n, used to absorb the number
of coefficients into the logarithmic degree budget. -/
private theorem nat_add_one_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
      have hp : 1 ≤ 2 ^ n := by positivity
      calc
        n + 1 + 1 ≤ 2 ^ n + 2 ^ n := by omega
        _ = 2 ^ (n + 1) := by
          rw [pow_succ]
          ring

/-- Evaluation of an integer polynomial after extending its coefficients
from the integers to the rationals and then to the reals. -/
private lemma evalReal_intMap_eq (x : ℝ) (R : Polynomial ℤ) :
    evalReal x (R.map (algebraMap ℤ ℚ)) =
      (R.map (algebraMap ℤ ℝ)).eval x := by
  rw [evalReal, Polynomial.eval₂_eq_eval_map, Polynomial.map_map]
  congr 1
  ext z
  simp

/--
Concrete single-index resultant lower bound.

Let f be the primitive irreducible integer polynomial of an algebraic real
x. Let g be an integer polynomial representing P after multiplication by
the positive denominator m. If every coefficient of g has absolute value
at most H^A, if 2^(deg g) ≤ H^c, and if m ≤ H^B, then the exact integer
resultant with f gives the fixed-power lower bound with exponent
c*K_a + (deg f - 1)*(A+c+c*K_C) + B, provided P(x) is nonzero.

The coprimality with f is not assumed: it is derived from irreducibility
of f and the nonzero evaluation of P.
-/
theorem integerized_polynomial_eval_lower_bound
    (x : ℝ) (f g : Polynomial ℤ) (P : Polynomial ℚ) (m H A B c K_a K_C : ℕ)
    (hfPrim : f.IsPrimitive)
    (hfIrr : Irreducible f)
    (hfRoot : Polynomial.aeval x f = 0)
    (hLead :
      ‖(f.map (algebraMap ℤ ℂ)).leadingCoeff‖ ≤ (2 : ℝ) ^ K_a)
    (hCauchy :
      (Polynomial.cauchyBound (f.map (algebraMap ℤ ℂ)) : ℝ) ≤
        (2 : ℝ) ^ K_C)
    (hmPos : 0 < m)
    (hScale :
      g.map (algebraMap ℤ ℚ) = C (m : ℚ) * P)
    (hH : 2 ≤ H)
    (hCoeff : ∀ i,
      ‖(g.map (algebraMap ℤ ℂ)).coeff i‖ ≤ (H : ℝ) ^ A)
    (hDegree : 2 ^ g.natDegree ≤ H ^ c)
    (hDenom : m ≤ H ^ B)
    (hEval : evalReal x P ≠ 0) :
    1 / (H : ℝ) ^
      (c * K_a + (f.natDegree - 1) * (A + c + c * K_C) + B) ≤
      |evalReal x P| := by
  classical
  let fQ : Polynomial ℚ := f.map (algebraMap ℤ ℚ)
  let gQ : Polynomial ℚ := g.map (algebraMap ℤ ℚ)
  let fC : Polynomial ℂ := f.map (algebraMap ℤ ℂ)
  let gC : Polynomial ℂ := g.map (algebraMap ℤ ℂ)
  have hfQirr : Irreducible fQ := by
    have h :=
      (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hfPrim).1 hfIrr
    simpa [fQ] using h
  have hfQroot : evalReal x fQ = 0 := by
    have hRootR : (f.map (algebraMap ℤ ℝ)).eval x = 0 := by
      change f.eval₂ (algebraMap ℤ ℝ) x = 0 at hfRoot
      simpa only [Polynomial.eval₂_eq_eval_map] using hfRoot
    simpa [fQ, evalReal_intMap_eq] using hRootR
  have hMapQC : fQ.map (algebraMap ℚ ℂ) = fC := by
    dsimp [fQ, fC]
    rw [Polynomial.map_map]
    congr 1
    ext z
    simp
  have hfC0 : fC ≠ 0 := by
    intro hz
    have hz' : fQ.map (algebraMap ℚ ℂ) = 0 := by
      rw [hMapQC]
      exact hz
    have hdeg := Polynomial.natDegree_map_eq_of_injective
      (FaithfulSMul.algebraMap_injective ℚ ℂ) fQ
    rw [hz'] at hdeg
    simp at hdeg
    have hpos := hfQirr.natDegree_pos
    omega
  have hMapC : (f.map (algebraMap ℤ ℝ)).map (algebraMap ℝ ℂ) = fC := by
    dsimp [fC]
    rw [Polynomial.map_map]
    congr 1
    ext z
    simp
  have hfRootC : fC.eval (x : ℂ) = 0 := by
    rw [← hMapC, Polynomial.eval_map_apply]
    simp [show (f.map (algebraMap ℤ ℝ)).eval x = 0 by
      change f.eval₂ (algebraMap ℤ ℝ) x = 0 at hfRoot
      simpa only [Polynomial.eval₂_eq_eval_map] using hfRoot]
  have hAlpha : (x : ℂ) ∈ fC.roots :=
    (Polynomial.mem_roots hfC0).2 hfRootC
  have hcop : IsCoprime fQ gQ := by
    rcases EuclideanDomain.dvd_or_coprime fQ gQ hfQirr with hdiv | hcop
    · rcases hdiv with ⟨t, ht⟩
      have hGroot : evalReal x gQ = 0 := by
        calc
          evalReal x gQ = evalReal x (fQ * t) := by rw [ht]
          _ = evalReal x fQ * evalReal x t := by
            simp [evalReal, Polynomial.eval₂_mul]
          _ = 0 := by simp [hfQroot]
      have hScaleEval :
          evalReal x gQ = (m : ℝ) * evalReal x P := by
        rw [hScale]
        simp [evalReal]
      have hmNe : (m : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hmPos)
      have hzero : (m : ℝ) * evalReal x P = 0 := by
        rw [← hScaleEval]
        exact hGroot
      exact (hEval ((mul_eq_zero.mp hzero).resolve_left hmNe)).elim
    · exact hcop
  have hDegreeReal : (2 : ℝ) ^ g.natDegree ≤ (H : ℝ) ^ c := by
    exact_mod_cast hDegree
  have hHpos : (0 : ℝ) < (H : ℝ) := by
    exact_mod_cast (show 0 < H by omega)
  have hNatDegG :
      gC.natDegree = g.natDegree :=
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective g
  have hNatDegF :
      fC.natDegree = f.natDegree :=
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective f
  have hNplusNat : g.natDegree + 1 ≤ H ^ c :=
    (nat_add_one_le_two_pow g.natDegree).trans hDegree
  have hNplus : ((gC.natDegree + 1 : ℕ) : ℝ) ≤ (H : ℝ) ^ c := by
    rw [hNatDegG]
    exact_mod_cast hNplusNat
  let Croot : ℝ := (Polynomial.cauchyBound fC : ℝ)
  have hCroot : Croot ≤ (2 : ℝ) ^ K_C := by
    exact hCauchy
  have hCrootNonneg : 0 ≤ Croot := by
    dsimp [Croot]
    positivity
  have hCrootPow :
      Croot ^ gC.natDegree ≤ (H : ℝ) ^ (c * K_C) := by
    calc
      Croot ^ gC.natDegree ≤ ((2 : ℝ) ^ K_C) ^ gC.natDegree := by
        gcongr
      _ = ((2 : ℝ) ^ gC.natDegree) ^ K_C := by
        simp [pow_mul, Nat.mul_comm]
      _ ≤ ((H : ℝ) ^ c) ^ K_C := by
        gcongr
      _ = (H : ℝ) ^ (c * K_C) := by
        rw [← pow_mul]
  have hLeadPow :
      ‖fC.leadingCoeff‖ ^ gC.natDegree ≤ (H : ℝ) ^ (c * K_a) := by
    calc
      ‖fC.leadingCoeff‖ ^ gC.natDegree ≤
          ((2 : ℝ) ^ K_a) ^ gC.natDegree := by
        gcongr
      _ = ((2 : ℝ) ^ gC.natDegree) ^ K_a := by
        simp [pow_mul, Nat.mul_comm]
      _ ≤ ((H : ℝ) ^ c) ^ K_a := by
        gcongr
      _ = (H : ℝ) ^ (c * K_a) := by
        rw [← pow_mul]
  let Broot : ℝ :=
    ((gC.natDegree + 1 : ℕ) : ℝ) * (H : ℝ) ^ A *
      Croot ^ gC.natDegree
  have hBroot :
      Broot ≤ (H : ℝ) ^ (A + c + c * K_C) := by
    dsimp [Broot]
    calc
      ((gC.natDegree + 1 : ℕ) : ℝ) * (H : ℝ) ^ A *
          Croot ^ gC.natDegree ≤
        (H : ℝ) ^ c * (H : ℝ) ^ A *
          (H : ℝ) ^ (c * K_C) := by
            gcongr
      _ = (H : ℝ) ^ (A + c + c * K_C) := by
            rw [← pow_add, ← pow_add]
            congr 1 <;> omega
  have hCoeffNonneg : 0 ≤ (H : ℝ) ^ A := by positivity
  have hRes0 :=
    resultant_eval_lower_bound_of_cauchy_and_coefficient_bound
      f g (x : ℂ) ((H : ℝ) ^ A) hcop hAlpha hCoeffNonneg hCoeff
  have hRes :
      1 ≤ ‖fC.leadingCoeff‖ ^ gC.natDegree *
        ‖gC.eval (x : ℂ)‖ * Broot ^ (fC.natDegree - 1) := by
    simpa [fC, gC, Broot, hNatDegF, hNatDegG, Croot] using hRes0
  let d0 : ℕ :=
    c * K_a + (f.natDegree - 1) * (A + c + c * K_C)
  have hProd :
      1 ≤ ‖gC.eval (x : ℂ)‖ * (H : ℝ) ^ d0 := by
    calc
      1 ≤ ‖fC.leadingCoeff‖ ^ gC.natDegree *
          ‖gC.eval (x : ℂ)‖ * Broot ^ (f.natDegree - 1) := by
            simpa [hNatDegF, hNatDegG] using hRes
      _ ≤ (H : ℝ) ^ (c * K_a) *
            ‖gC.eval (x : ℂ)‖ *
            ((H : ℝ) ^ (A + c + c * K_C)) ^ (f.natDegree - 1) := by
              gcongr
      _ = ‖gC.eval (x : ℂ)‖ * (H : ℝ) ^ d0 := by
            rw [pow_mul]
            dsimp [d0]
            rw [Nat.mul_comm (A + c + c * K_C) (f.natDegree - 1)]
            rw [← pow_add]
            ring
  have hLowerInteger :
      1 / (H : ℝ) ^ d0 ≤ ‖gC.eval (x : ℂ)‖ := by
    apply (div_le_iff₀ (pow_pos hHpos d0)).2
    simpa [mul_comm] using hProd
  have hMapGComplex :
      (g.map (algebraMap ℤ ℝ)).map (algebraMap ℝ ℂ) = gC := by
    dsimp [gC]
    rw [Polynomial.map_map]
    congr 1
    ext z
    simp
  have hEvalGReal :
      evalReal x gQ = (g.map (algebraMap ℤ ℝ)).eval x :=
    evalReal_intMap_eq x g
  have hNormEval :
      ‖gC.eval (x : ℂ)‖ = |evalReal x gQ| := by
    calc
      ‖gC.eval (x : ℂ)‖ =
          ‖((g.map (algebraMap ℤ ℝ)).map (algebraMap ℝ ℂ)).eval (x : ℂ)‖ := by
            rw [hMapGComplex]
      _ = ‖(algebraMap ℝ ℂ) ((g.map (algebraMap ℤ ℝ)).eval x)‖ := by
            rw [Polynomial.eval_map_apply]
      _ = |evalReal x gQ| := by rw [← hEvalGReal]; simp
  have hScaleEval :
      evalReal x gQ = (m : ℝ) * evalReal x P := by
    rw [hScale]
    simp [evalReal]
  have hNormEvalP :
      ‖gC.eval (x : ℂ)‖ = (m : ℝ) * |evalReal x P| := by
    rw [hNormEval, hScaleEval, abs_mul]
    simp
  have hDenomReal : (m : ℝ) ≤ (H : ℝ) ^ B := by
    exact_mod_cast hDenom
  have hFinalProd :
      1 ≤ (H : ℝ) ^ (d0 + B) * |evalReal x P| := by
    calc
      1 ≤ (H : ℝ) ^ d0 * ‖gC.eval (x : ℂ)‖ := by
        have h := (div_le_iff₀ (pow_pos hHpos d0)).1 hLowerInteger
        simpa [mul_comm] using h
      _ = (H : ℝ) ^ d0 * (m : ℝ) * |evalReal x P| := by
        rw [hNormEvalP]
        ring
      _ ≤ (H : ℝ) ^ d0 * (H : ℝ) ^ B * |evalReal x P| := by
        gcongr
      _ = (H : ℝ) ^ (d0 + B) * |evalReal x P| := by
        rw [← pow_add]
  exact (div_le_iff₀ (pow_pos hHpos (d0 + B))).2 hFinalProd

/--
The concrete hLiouville premise for a pair of rational-polynomial
sequences.  The integerized numerator of each sequence has coefficient
height at most H^A, degree at most c log_2(H) (expressed without
logarithms as 2^degree ≤ H^c), and denominator at most H^B.
The proof constructs one primitive minimal polynomial for the algebraic
candidate and uses the same leading-coefficient/Cauchy constants for both
channels.  Thus the exponent is common to the two channels.
-/
theorem hLiouville_of_integerized_height_degree_bounds
    {x : ℝ} {P Q : ℕ → Polynomial ℚ} {H : ℕ → ℕ}
    (A B c : ℕ)
    (SP : IntegerizedPolynomialSequence P)
    (SQ : IntegerizedPolynomialSequence Q)
    (hH : ∀ᶠ n : ℕ in atTop, 2 ≤ H n)
    (hPCoeff : ∀ᶠ n : ℕ in atTop, ∀ i,
      ‖((SP.numerator n).map (algebraMap ℤ ℂ)).coeff i‖ ≤ (H n : ℝ) ^ A)
    (hQCoeff : ∀ᶠ n : ℕ in atTop, ∀ i,
      ‖((SQ.numerator n).map (algebraMap ℤ ℂ)).coeff i‖ ≤ (H n : ℝ) ^ A)
    (hPDegree : ∀ᶠ n : ℕ in atTop,
      2 ^ (SP.numerator n).natDegree ≤ H n ^ c)
    (hQDegree : ∀ᶠ n : ℕ in atTop,
      2 ^ (SQ.numerator n).natDegree ≤ H n ^ c)
    (hPDenom : ∀ᶠ n : ℕ in atTop,
      SP.denominator n ≤ H n ^ B)
    (hQDenom : ∀ᶠ n : ℕ in atTop,
      SQ.denominator n ≤ H n ^ B) :
    IsAlgebraic ℚ x →
      ∃ d : ℕ,
        (∀ᶠ n : ℕ in atTop,
          evalReal x (P n) ≠ 0 →
            1 / (H n : ℝ) ^ d ≤ |evalReal x (P n)|) ∧
        (∀ᶠ n : ℕ in atTop,
          evalReal x (Q n) ≠ 0 →
            1 / (H n : ℝ) ^ d ≤ |evalReal x (Q n)|) := by
  intro hx
  obtain ⟨f, hf0, hfPrim, hfIrr, hfRoot⟩ :=
    exists_primitive_irreducible_integer_polynomial_vanishing_of_algebraic hx
  let fC : Polynomial ℂ := f.map (algebraMap ℤ ℂ)
  obtain ⟨K_a, hKa⟩ := exists_nat_gt ‖fC.leadingCoeff‖
  have hKaNat : K_a ≤ 2 ^ K_a := by
    have h := nat_add_one_le_two_pow K_a
    omega
  have hLead :
      ‖fC.leadingCoeff‖ ≤ (2 : ℝ) ^ K_a := by
    exact (le_of_lt hKa).trans (by exact_mod_cast hKaNat)
  let Croot : ℝ := (Polynomial.cauchyBound fC : ℝ)
  obtain ⟨K_C, hKC⟩ := exists_nat_gt Croot
  have hKCNat : K_C ≤ 2 ^ K_C := by
    have h := nat_add_one_le_two_pow K_C
    omega
  have hCauchy :
      (Polynomial.cauchyBound fC : ℝ) ≤ (2 : ℝ) ^ K_C := by
    exact (le_of_lt hKC).trans (by exact_mod_cast hKCNat)
  let d : ℕ :=
    c * K_a + (f.natDegree - 1) * (A + c + c * K_C) + B
  have hLowerP : ∀ᶠ n : ℕ in atTop,
      evalReal x (P n) ≠ 0 →
        1 / (H n : ℝ) ^ d ≤ |evalReal x (P n)| := by
    filter_upwards [hH, hPCoeff, hPDegree, hPDenom] with n hnH hnCoeff hnDeg hnDen
    intro hnEval
    have h :=
      integerized_polynomial_eval_lower_bound
        x f (SP.numerator n) (P n) (SP.denominator n) (H n) A B c K_a K_C
        hfPrim hfIrr hfRoot hLead hCauchy (SP.denominator_pos n)
        (SP.map_eq n) hnH hnCoeff hnDeg hnDen hnEval
    simpa [d] using h
  have hLowerQ : ∀ᶠ n : ℕ in atTop,
      evalReal x (Q n) ≠ 0 →
        1 / (H n : ℝ) ^ d ≤ |evalReal x (Q n)| := by
    filter_upwards [hH, hQCoeff, hQDegree, hQDenom] with n hnH hnCoeff hnDeg hnDen
    intro hnEval
    have h :=
      integerized_polynomial_eval_lower_bound
        x f (SQ.numerator n) (Q n) (SQ.denominator n) (H n) A B c K_a K_C
        hfPrim hfIrr hfRoot hLead hCauchy (SQ.denominator_pos n)
        (SQ.map_eq n) hnH hnCoeff hnDeg hnDen hnEval
    simpa [d] using h
  exact ⟨d, hLowerP, hLowerQ⟩

/--
Paired super-polynomial approximation with explicit integerized height and
degree hypotheses.  This theorem supplies the former abstract hLiouville
argument internally, so callers no longer need to postulate it.
-/
theorem transcendental_of_paired_superpolynomial_approximation_of_integerized_height_bounds
    {x : ℝ} {P Q : ℕ → Polynomial ℚ} {H : ℕ → ℕ}
    (A B c : ℕ)
    (SP : IntegerizedPolynomialSequence P)
    (SQ : IntegerizedPolynomialSequence Q)
    (hH : ∀ᶠ n : ℕ in atTop, 2 ≤ H n)
    (hCoprimeP : ∀ i j, i ≠ j → IsCoprime (P i) (P j))
    (hCoprimeQ : ∀ i j, i ≠ j → IsCoprime (Q i) (Q j))
    (hSmall : ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
      min |evalReal x (P n)| |evalReal x (Q n)| <
        1 / (H n : ℝ) ^ k)
    (hPCoeff : ∀ᶠ n : ℕ in atTop, ∀ i,
      ‖((SP.numerator n).map (algebraMap ℤ ℂ)).coeff i‖ ≤ (H n : ℝ) ^ A)
    (hQCoeff : ∀ᶠ n : ℕ in atTop, ∀ i,
      ‖((SQ.numerator n).map (algebraMap ℤ ℂ)).coeff i‖ ≤ (H n : ℝ) ^ A)
    (hPDegree : ∀ᶠ n : ℕ in atTop,
      2 ^ (SP.numerator n).natDegree ≤ H n ^ c)
    (hQDegree : ∀ᶠ n : ℕ in atTop,
      2 ^ (SQ.numerator n).natDegree ≤ H n ^ c)
    (hPDenom : ∀ᶠ n : ℕ in atTop,
      SP.denominator n ≤ H n ^ B)
    (hQDenom : ∀ᶠ n : ℕ in atTop,
      SQ.denominator n ≤ H n ^ B) :
    Transcendental ℚ x := by
  have hHgt : ∀ᶠ n : ℕ in atTop, 1 < H n := by
    filter_upwards [hH] with n hn
    omega
  exact
    transcendental_of_paired_superpolynomial_approximation_of_algebraic_lower_bound
      hHgt hCoprimeP hCoprimeQ hSmall
      (hLiouville_of_integerized_height_degree_bounds
        A B c SP SQ hH hPCoeff hQCoeff hPDegree hQDegree hPDenom hQDenom)

#print axioms integerized_polynomial_eval_lower_bound
#print axioms hLiouville_of_integerized_height_degree_bounds
#print axioms transcendental_of_paired_superpolynomial_approximation_of_integerized_height_bounds

end EPlusPiApproximation
