module
public import ResultantPairedCriterion
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Polynomial.CauchyBound
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

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
  intro hzero
  apply hQ
  have hfi : Function.Injective (algebraMap ℤ ℚ) :=
    RingHom.injective_int (algebraMap ℤ ℚ)
  have hdegf :
      (f.map (algebraMap ℤ ℚ)).natDegree = f.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hfi f
  have hdegg :
      (g.map (algebraMap ℤ ℚ)).natDegree = g.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hfi g
  have hmap := congrArg (algebraMap ℤ ℚ) hzero
  rw [Polynomial.resultant_map_map, hdegf, hdegg, map_zero] at hmap
  exact hmap

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
  have hresC : Polynomial.resultant fC gC ≠ 0 := by
    rw [fC, gC, Polynomial.resultant_map_map]
    exact map_ne_zero (algebraMap ℤ ℂ) hresZ
  have hresAbs : (1 : ℝ) ≤ ‖Polynomial.resultant fC gC‖ := by
    have hInt : (1 : ℝ) ≤ |Polynomial.resultant f g| := by
      exact_mod_cast Int.one_le_abs hresZ
    have hCast :
        ‖(Polynomial.resultant f g : ℂ)‖ = |Polynomial.resultant f g| := by
      simp [Complex.norm_intCast]
    calc
      (1 : ℝ) ≤ |Polynomial.resultant f g| := hInt
      _ = ‖Polynomial.resultant fC gC‖ := by
        rw [fC, gC, Polynomial.resultant_map_map, hCast]
  have hresultantFormula :
      Polynomial.resultant fC gC =
        fC.leadingCoeff ^ gC.natDegree *
          (fC.roots.map gC.eval).prod := by
    exact Polynomial.resultant_eq_prod_eval fC gC gC.natDegree le_rfl hfSplits
  have hmapRoots :
      fC.roots.map gC.eval =
        gC.eval α ::ₘ ((fC.roots.erase α).map gC.eval) := by
    rw [← Multiset.cons_erase hα, Multiset.map_cons]
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
    simpa [Multiset.card_erase_of_mem hα, hfSplits.natDegree_eq_card_roots] using h
  calc
    (1 : ℝ) ≤ ‖Polynomial.resultant fC gC‖ := hresAbs
    _ = ‖fC.leadingCoeff‖ ^ gC.natDegree *
          (‖gC.eval α‖ *
            ‖((fC.roots.erase α).map gC.eval).prod‖) := hformulaNorm
    _ ≤ ‖fC.leadingCoeff‖ ^ gC.natDegree *
          (‖gC.eval α‖ * B ^ (fC.natDegree - 1)) := by
      gcongr

#print axioms int_resultant_ne_zero_of_rat_coprime
#print axioms resultant_eval_lower_bound_of_other_roots

end EPlusPiApproximation
