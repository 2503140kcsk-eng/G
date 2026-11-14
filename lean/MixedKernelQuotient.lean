module
public import Mathlib.Algebra.Polynomial.SumIteratedDerivative
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Algebra.Polynomial

@[expose] public section

open Polynomial
open MeasureTheory
open scoped Topology

noncomputable section
namespace MixedKernelQuotient

variable {R : Type*} [CommRing R]

/-- Reflection of a polynomial: p(X) is sent to p(-X). -/
def reflect : Polynomial R →ₗ[R] Polynomial R :=
  (Polynomial.aeval (-Polynomial.X)).toLinearMap

@[simp] theorem reflect_apply (p : Polynomial R) :
    reflect p = p.comp (-X) := by
  change p.eval₂ C (-X) = p.eval₂ C (-X)
  rfl

theorem reflect_reflect (p : Polynomial R) :
    reflect (reflect p) = p := by
  change (p.comp (-X)).comp (-X) = p
  rw [Polynomial.comp_assoc]
  simp

/-- Alternating sum of iterated derivatives, implemented by reflection
of Mathlib's sum of iterated derivatives. -/
noncomputable def signedSumIDeriv : Polynomial R →ₗ[R] Polynomial R :=
  reflect.comp (Polynomial.sumIDeriv.comp reflect)

theorem derivative_signedSum_add (p : Polynomial R) :
    (signedSumIDeriv p).derivative + signedSumIDeriv p = p := by
  let q := reflect p
  let t := Polynomial.sumIDeriv q
  have hsum : t = q + t.derivative := by
    simpa [t] using (Polynomial.sumIDeriv_eq_self_add q)
  have hdouble : reflect q = p := by
    simpa [q] using reflect_reflect p
  have hcomp : reflect t = p + reflect t.derivative := by
    calc
      reflect t = reflect (q + t.derivative) := congrArg reflect hsum
      _ = reflect q + reflect t.derivative := map_add reflect q t.derivative
      _ = p + reflect t.derivative := by rw [hdouble]
  have hderiv : (reflect t).derivative = -reflect t.derivative := by
    rw [reflect_apply, Polynomial.derivative_comp]
    simp [reflect_apply]
  change (reflect t).derivative + reflect t = p
  rw [hderiv, hcomp]
  abel

theorem reflect_map
    {S : Type*} [CommRing S] (f : R →+* S) (p : Polynomial R) :
    reflect (p.map f) = (reflect p).map f := by
  change (p.map f).comp (-X) = (p.comp (-X)).map f
  calc
    (p.map f).comp (-X) =
        (p.map f).comp ((-X).map f) := by simp
    _ = (p.comp (-X)).map f := (Polynomial.map_comp f p (-X)).symm

theorem signedSumIDeriv_map
    {S : Type*} [CommRing S] (f : R →+* S) (p : Polynomial R) :
    signedSumIDeriv (p.map f) = (signedSumIDeriv p).map f := by
  simp only [signedSumIDeriv, LinearMap.comp_apply]
  rw [reflect_map, Polynomial.sumIDeriv_map, reflect_map]

def endpointA (p : Polynomial R) : R := (signedSumIDeriv p).eval 1
def endpointC (p : Polynomial R) : R := (signedSumIDeriv p).eval 0

/-! Split-kernel theorem for arbitrary linear maps. -/

section SplitKernel
variable {S V W : Type*}
variable [Ring S]
variable [AddCommGroup V] [Module S V]
variable [AddCommGroup W] [Module S W]

theorem splitSection_apply
    (f : V →ₗ[S] W) (s : W →ₗ[S] V)
    (hs : f.comp s = LinearMap.id) (w : W) :
    f (s w) = w := by
  have h := congrArg (fun g : W →ₗ[S] W => g w) hs
  simpa using h

def splitKerEquiv
    (f : V →ₗ[S] W) (s : W →ₗ[S] V)
    (hs : f.comp s = LinearMap.id) :
    V ≃ₗ[S] LinearMap.ker f × W where
  toFun v :=
    (⟨v - s (f v), by
      apply LinearMap.mem_ker.mpr
      rw [map_sub, splitSection_apply f s hs]
      exact sub_self (f v)⟩,
      f v)
  invFun p := (p.1 : V) + s p.2
  left_inv v := by
    change (v - s (f v)) + s (f v) = v
    abel
  right_inv p := by
    rcases p with ⟨k, w⟩
    have hk : f (k : V) = 0 := LinearMap.mem_ker.mp k.property
    apply Prod.ext
    · apply Subtype.ext
      change (k : V) + s w - s (f ((k : V) + s w)) = (k : V)
      simp [map_add, hk, splitSection_apply f s hs]
    · change f ((k : V) + s w) = w
      simp [map_add, hk, splitSection_apply f s hs]
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      change (x + y) - s (f (x + y)) =
        (x - s (f x)) + (y - s (f y))
      simp only [map_add]
      abel
    · simp
  map_smul' a x := by
    apply Prod.ext
    · apply Subtype.ext
      change a • x - s (f (a • x)) = a • (x - s (f x))
      simp only [map_smul, smul_sub]
    · simp

noncomputable def splitKerQuotientEquiv
    (f : V →ₗ[S] W) (s : W →ₗ[S] V)
    (hs : f.comp s = LinearMap.id) :
    (V ⧸ LinearMap.ker f) ≃ₗ[S] W :=
  f.quotKerEquivOfSurjective
    (fun w => ⟨s w, splitSection_apply f s hs w⟩)
end SplitKernel

/-! Endpoint signature, its explicit linear section, and the quotient. -/

def endpointSignature : Polynomial ℤ →ₗ[ℤ] ℤ × ℤ where
  toFun p := (endpointA p, endpointC p)
  map_add' p q := by simp [endpointA, endpointC]
  map_smul' a p := by
    change ((signedSumIDeriv (a • p)).eval 1,
      (signedSumIDeriv (a • p)).eval 0) =
      (a • (signedSumIDeriv p).eval 1,
        a • (signedSumIDeriv p).eval 0)
    rw [map_smul (signedSumIDeriv) a p]
    simp

/-- The affine section sending (a,c) to (a-c)X+a. -/
def endpointSection : ℤ × ℤ →ₗ[ℤ] Polynomial ℤ where
  toFun z := C (z.1 - z.2) * X + C z.1
  map_add' := by
    rintro ⟨a, c⟩ ⟨b, d⟩
    simp [sub_eq_add_neg]
    ring
  map_smul' := by
    rintro n ⟨a, c⟩
    simp [sub_eq_add_neg]
    ring

theorem endpointSignature_section (z : ℤ × ℤ) :
    endpointSignature (endpointSection z) = z := by
  rcases z with ⟨a, c⟩
  let p : Polynomial ℤ := C (a - c) * X + C a
  let q : Polynomial ℤ := reflect p
  have hq : q = C (c - a) * X + C a := by
    simp [q, p, reflect]
    ring
  have hqderiv : q.derivative = C (c - a) := by
    rw [hq]
    simp
  have hsumderiv :
      (Polynomial.sumIDeriv q).derivative = C (c - a) := by
    calc
      (Polynomial.sumIDeriv q).derivative =
          Polynomial.sumIDeriv q.derivative :=
        (Polynomial.sumIDeriv_derivative q).symm
      _ = C (c - a) := by rw [hqderiv, Polynomial.sumIDeriv_C]
  have hsum : Polynomial.sumIDeriv q = q + C (c - a) := by
    rw [Polynomial.sumIDeriv_eq_self_add, hsumderiv]
  have hdouble : reflect q = p := by
    simpa [q] using reflect_reflect p
  have hS : signedSumIDeriv p = C (a - c) * X + C c := by
    change reflect (Polynomial.sumIDeriv q) = _
    calc
      reflect (Polynomial.sumIDeriv q) =
          reflect (q + C (c - a)) := by rw [hsum]
      _ = reflect q + reflect (C (c - a)) := by simp
      _ = p + C (c - a) := by
        rw [hdouble]
        simp [reflect_apply]
      _ = C (a - c) * X + C c := by dsimp [p]; ring_nf
  change ((signedSumIDeriv p).eval 1, (signedSumIDeriv p).eval 0) = (a, c)
  rw [hS]
  simp [p]

theorem endpointSignature_surjective :
    Function.Surjective endpointSignature := by
  intro z
  exact ⟨endpointSection z, endpointSignature_section z⟩

theorem endpointSignature_rightInverse :
    endpointSignature.comp endpointSection = LinearMap.id := by
  apply LinearMap.ext
  intro z
  exact endpointSignature_section z

noncomputable def endpointSplitEquiv :
    Polynomial ℤ ≃ₗ[ℤ] LinearMap.ker endpointSignature × (ℤ × ℤ) :=
  splitKerEquiv endpointSignature endpointSection endpointSignature_rightInverse

noncomputable def endpointQuotientEquiv :
    (Polynomial ℤ ⧸ LinearMap.ker endpointSignature) ≃ₗ[ℤ] ℤ × ℤ :=
  endpointSignature.quotKerEquivOfSurjective endpointSignature_surjective

theorem endpointQuotientEquiv_mkQ (p : Polynomial ℤ) :
    endpointQuotientEquiv ((LinearMap.ker endpointSignature).mkQ p) =
      endpointSignature p := by
  change endpointSignature.quotKerEquivOfSurjective endpointSignature_surjective
      ((LinearMap.ker endpointSignature).mkQ p) = endpointSignature p
  exact LinearMap.quotKerEquivOfSurjective_apply_mk
    endpointSignature endpointSignature_surjective p

/-! Analytic component of the mixed integral. -/

theorem intervalIntegral_exp_mul_eval (p : Polynomial ℝ) :
    (∫ x in (0 : ℝ)..1, Real.exp x * p.eval x) =
      Real.exp 1 * endpointA p - endpointC p := by
  let s := signedSumIDeriv p
  have hderiv (x : ℝ) :
      HasDerivAt (fun t : ℝ => Real.exp t * s.eval t)
        (Real.exp x * p.eval x) x := by
    have h := (Real.hasDerivAt_exp x).mul (s.hasDerivAt x)
    have heval : s.eval x + s.derivative.eval x = p.eval x := by
      have hh := congrArg (fun r : Polynomial ℝ => r.eval x)
        (derivative_signedSum_add p)
      simpa [add_comm] using hh
    convert h using 1
    · rw [← mul_add, heval]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hderiv x)
    (ContinuousOn.intervalIntegrable (by fun_prop))]
  simp [endpointA, endpointC, s, Real.exp_zero]

theorem intervalIntegral_four_a_over_one_add_sq (a : ℝ) :
    (∫ x in (0 : ℝ)..1, (4 * a) / (1 + x ^ 2)) = a * Real.pi := by
  calc
    (∫ x in (0 : ℝ)..1, (4 * a) / (1 + x ^ 2))
        = ∫ x in (0 : ℝ)..1, (4 * a) * (1 + x ^ 2)⁻¹ := by
          simp [div_eq_mul_inv]
    _ = (4 * a) * (∫ x in (0 : ℝ)..1, (1 + x ^ 2)⁻¹) := by
          rw [← intervalIntegral.integral_const_mul]
    _ = (4 * a) * (Real.arctan 1 - Real.arctan 0) := by
          rw [integral_inv_one_add_sq]
    _ = a * Real.pi := by
          simp [Real.arctan_one]
          ring

theorem endpointA_map_real (p : Polynomial ℤ) :
    endpointA (R := ℝ) (p.map (Int.castRingHom ℝ)) =
      (endpointA (R := ℤ) p : ℝ) := by
  simp [endpointA, signedSumIDeriv_map]

theorem endpointC_map_real (p : Polynomial ℤ) :
    endpointC (R := ℝ) (p.map (Int.castRingHom ℝ)) =
      (endpointC (R := ℤ) p : ℝ) := by
  simp [endpointC, signedSumIDeriv_map]

/-- The mixed integral appearing in the project research note. -/
noncomputable def mixedIntegralValue (p : Polynomial ℤ) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    Real.exp x * (p.map (Int.castRingHom ℝ)).eval x +
      (4 * (endpointA (R := ℤ) p : ℝ)) / (1 + x ^ 2)

/-- The linear form on endpoint coefficients. -/
noncomputable def mixedPairValue : ℤ × ℤ →ₗ[ℤ] ℝ where
  toFun z := (z.1 : ℝ) * (Real.exp 1 + Real.pi) - (z.2 : ℝ)
  map_add' := by
    rintro ⟨a, c⟩ ⟨b, d⟩
    simp
    ring
  map_smul' := by
    rintro n ⟨a, c⟩
    simp only [Prod.smul_mk, zsmul_eq_mul, Int.cast_mul, RingHom.id_apply]
    push_cast
    ring

/-- The mixed integral descends to the quotient by the endpoint kernel. -/
noncomputable def mixedIntegralQuotientFactor :
    (Polynomial ℤ ⧸ LinearMap.ker endpointSignature) →ₗ[ℤ] ℝ :=
  mixedPairValue.comp endpointQuotientEquiv.toLinearMap

theorem mixedIntegralQuotientFactor_mkQ (p : Polynomial ℤ) :
    mixedIntegralQuotientFactor ((LinearMap.ker endpointSignature).mkQ p) =
      mixedPairValue (endpointSignature p) := by
  change mixedPairValue
      (endpointQuotientEquiv ((LinearMap.ker endpointSignature).mkQ p)) =
    mixedPairValue (endpointSignature p)
  rw [endpointQuotientEquiv_mkQ]

theorem mixedIntegral_identity (p : Polynomial ℤ) :
    mixedIntegralValue p = mixedPairValue (endpointSignature p) := by
  let pR := p.map (Int.castRingHom ℝ)
  have hA := endpointA_map_real p
  have hC := endpointC_map_real p
  have hExp := intervalIntegral_exp_mul_eval pR
  have hArctan := intervalIntegral_four_a_over_one_add_sq
    (endpointA (R := ℤ) p : ℝ)
  have hfCont : Continuous (fun x : ℝ => Real.exp x * pR.eval x) := by fun_prop
  have hbase : Continuous (fun x : ℝ => 1 + x ^ 2) := by fun_prop
  have hinv : Continuous (fun x : ℝ => (1 + x ^ 2)⁻¹) :=
    hbase.inv₀ (by intro x; positivity)
  have hgCont : Continuous
      (fun x : ℝ => (4 * (endpointA (R := ℤ) p : ℝ)) / (1 + x ^ 2)) := by
    rw [div_eq_mul_inv]
    change Continuous
      ((fun _ : ℝ => 4 * (endpointA (R := ℤ) p : ℝ)) *
        (fun x : ℝ => (1 + x ^ 2)⁻¹))
    exact continuous_const.mul hinv
  have hfInt : IntervalIntegrable
      (fun x : ℝ => Real.exp x * pR.eval x) volume 0 1 :=
    hfCont.intervalIntegrable 0 1
  have hgInt : IntervalIntegrable
      (fun x : ℝ => (4 * (endpointA (R := ℤ) p : ℝ)) / (1 + x ^ 2)) volume 0 1 :=
    hgCont.intervalIntegrable 0 1
  unfold mixedIntegralValue
  rw [intervalIntegral.integral_add hfInt hgInt, hExp, hArctan,
    endpointA_map_real, endpointC_map_real]
  simp [mixedPairValue, endpointSignature, endpointA, endpointC]
  ring

theorem mixedIntegral_factorization_map :
    mixedIntegralQuotientFactor.comp ((LinearMap.ker endpointSignature).mkQ) =
      mixedPairValue.comp endpointSignature := by
  apply LinearMap.ext
  intro p
  exact mixedIntegralQuotientFactor_mkQ p

theorem mixedIntegral_factors_through_quotient (p : Polynomial ℤ) :
    mixedIntegralQuotientFactor ((LinearMap.ker endpointSignature).mkQ p) =
      mixedIntegralValue p := by
  rw [mixedIntegralQuotientFactor_mkQ, ← mixedIntegral_identity]

#print axioms derivative_signedSum_add
#print axioms splitKerEquiv
#print axioms endpointSignature_section
#print axioms mixedIntegral_identity
#print axioms mixedIntegral_factorization_map

end MixedKernelQuotient
