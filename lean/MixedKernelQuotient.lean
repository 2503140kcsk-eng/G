module
public import Mathlib.Algebra.Polynomial.SumIteratedDerivative
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

open Polynomial
open scoped Topology

noncomputable section
namespace MixedKernelQuotient

variable {R : Type*} [CommRing R]

/-- Reflection of a polynomial: p(X) is sent to p(-X). -/
def reflect : Polynomial R →ₗ[R] Polynomial R where
  toFun p := p.comp (-X)
  map_add' p q := by simp
  map_smul' a p := by simp

/-- Alternating sum of iterated derivatives, implemented by reflection
of Mathlib's sum of iterated derivatives. -/
noncomputable def signedSumIDeriv : Polynomial R →ₗ[R] Polynomial R :=
  reflect.comp (Polynomial.sumIDeriv.comp reflect)

theorem derivative_signedSum_add (p : Polynomial R) :
    (signedSumIDeriv p).derivative + signedSumIDeriv p = p := by
  let q := reflect p
  let t := Polynomial.sumIDeriv q
  have hsum := Polynomial.sumIDeriv_eq_self_add q
  have hdouble : q.comp (-X) = p := by simp [q, reflect]
  have hcomp : t.comp (-X) = p + t.derivative.comp (-X) := by
    calc
      t.comp (-X) = (q + t.derivative).comp (-X) := by rw [hsum]
      _ = q.comp (-X) + t.derivative.comp (-X) := by simp
      _ = p + t.derivative.comp (-X) := by rw [hdouble]
  have hderiv : (t.comp (-X)).derivative = -t.derivative.comp (-X) := by
    rw [Polynomial.derivative_comp]
    simp
  change (t.comp (-X)).derivative + t.comp (-X) = p
  rw [hderiv, hcomp]
  abel

theorem signedSumIDeriv_map
    {S : Type*} [CommRing S] (f : R →+* S) (p : Polynomial R) :
    signedSumIDeriv (p.map f) = (signedSumIDeriv p).map f := by
  simp [signedSumIDeriv, reflect, Polynomial.sumIDeriv_map]

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
      simp only [map_smul]
      module
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
  map_add' p q := by simp [endpointA, endpointC, signedSumIDeriv]
  map_smul' a p := by simp [endpointA, endpointC, signedSumIDeriv]

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
      _ = C (c - a) := by rw [hqderiv]; simp
  have hsum : Polynomial.sumIDeriv q = q + C (c - a) := by
    rw [Polynomial.sumIDeriv_eq_self_add, hsumderiv]
  have hS :
      signedSumIDeriv p = p + C (c - a) := by
    change reflect (Polynomial.sumIDeriv q) = _
    rw [hsum]
    simp [reflect, hq, p]
  simp [endpointSignature, endpointA, endpointC, endpointSection, p, hS]
  <;> ring

theorem endpointSignature_surjective :
    Function.Surjective endpointSignature := by
  intro z
  exact ⟨endpointSection z, endpointSignature_section z⟩

noncomputable def endpointSplitEquiv :
    Polynomial ℤ ≃ₗ[ℤ] LinearMap.ker endpointSignature × (ℤ × ℤ) :=
  splitKerEquiv endpointSignature endpointSection (by
    ext z
    exact endpointSignature_section z)

noncomputable def endpointQuotientEquiv :
    (Polynomial ℤ ⧸ LinearMap.ker endpointSignature) ≃ₗ[ℤ] ℤ × ℤ :=
  splitKerQuotientEquiv endpointSignature endpointSection (by
    ext z
    exact endpointSignature_section z)

theorem endpointQuotientEquiv_mkQ (p : Polynomial ℤ) :
    endpointQuotientEquiv ((LinearMap.ker endpointSignature).mkQ p) =
      endpointSignature p := by
  simp [endpointQuotientEquiv, splitKerQuotientEquiv]

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
    · rfl
    · rw [← mul_add, heval]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hderiv x)
    (ContinuousOn.intervalIntegrable (by fun_prop))]
  simp [endpointA, endpointC, s, Real.exp_zero]

theorem intervalIntegral_four_a_over_one_add_sq (a : ℝ) :
    (∫ x in (0 : ℝ)..1, (4 * a) / (1 + x ^ 2)) = a * Real.pi := by
  calc
    (∫ x in (0 : ℝ)..1, (4 * a) / (1 + x ^ 2))
        = (4 * a) * (∫ x in (0 : ℝ)..1, (1 + x ^ 2)⁻¹) := by
          rw [intervalIntegral.integral_const_mul]
          congr 1
          funext x
          ring
    _ = (4 * a) * (Real.arctan 1 - Real.arctan 0) := by
          rw [intervalIntegral.integral_inv_one_add_sq]
    _ = a * Real.pi := by
          simp [Real.arctan_one]
          ring

theorem endpointA_map_real (p : Polynomial ℤ) :
    endpointA (p.map (Int.castRingHom ℝ)) = (endpointA p : ℝ) := by
  simp [endpointA, signedSumIDeriv_map]

theorem endpointC_map_real (p : Polynomial ℤ) :
    endpointC (p.map (Int.castRingHom ℝ)) = (endpointC p : ℝ) := by
  simp [endpointC, signedSumIDeriv_map]

/-- The mixed integral appearing in the project research note. -/
noncomputable def mixedIntegralValue (p : Polynomial ℤ) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    Real.exp x * (p.map (Int.castRingHom ℝ)).eval x +
      (4 * (endpointA p : ℝ)) / (1 + x ^ 2)

/-- The linear form on endpoint coefficients. -/
noncomputable def mixedPairValue : ℤ × ℤ →ₗ[ℤ] ℝ where
  toFun z := (z.1 : ℝ) * (Real.exp 1 + Real.pi) - (z.2 : ℝ)
  map_add' := by
    rintro ⟨a, c⟩ ⟨b, d⟩
    simp
    ring
  map_smul' := by
    intro n z
    rcases z with ⟨a, c⟩
    change ((n * a : ℤ) : ℝ) * (Real.exp 1 + Real.pi) -
        ((n * c : ℤ) : ℝ) =
      (n : ℝ) * ((a : ℝ) * (Real.exp 1 + Real.pi) - (c : ℝ))
    push_cast
    ring

/-- The mixed integral descends to the quotient by the endpoint kernel. -/
noncomputable def mixedIntegralQuotientFactor :
    (Polynomial ℤ ⧸ LinearMap.ker endpointSignature) →ₗ[ℤ] ℝ :=
  mixedPairValue.comp endpointQuotientEquiv.toLinearMap

theorem mixedIntegralQuotientFactor_mkQ (p : Polynomial ℤ) :
    mixedIntegralQuotientFactor ((LinearMap.ker endpointSignature).mkQ p) =
      mixedPairValue (endpointSignature p) := by
  simp [mixedIntegralQuotientFactor, endpointQuotientEquiv_mkQ]

theorem mixedIntegral_identity (p : Polynomial ℤ) :
    mixedIntegralValue p = mixedPairValue (endpointSignature p) := by
  let pR := p.map (Int.castRingHom ℝ)
  have hA := endpointA_map_real p
  have hC := endpointC_map_real p
  have hExp := intervalIntegral_exp_mul_eval pR
  have hArctan := intervalIntegral_four_a_over_one_add_sq (endpointA p : ℝ)
  have hfCont : Continuous (fun x : ℝ => Real.exp x * pR.eval x) := by fun_prop
  have hgCont : Continuous (fun x : ℝ => (4 * (endpointA p : ℝ)) / (1 + x ^ 2)) := by
    fun_prop
  have hfInt : IntervalIntegrable
      (fun x : ℝ => Real.exp x * pR.eval x) volume 0 1 :=
    hfCont.intervalIntegrable 0 1
  have hgInt : IntervalIntegrable
      (fun x : ℝ => (4 * (endpointA p : ℝ)) / (1 + x ^ 2)) volume 0 1 :=
    hgCont.intervalIntegrable 0 1
  unfold mixedIntegralValue
  rw [intervalIntegral.integral_add hfInt hgInt, hExp, hArctan,
    endpointA_map_real, endpointC_map_real]
  simp [mixedPairValue, endpointSignature, endpointA, endpointC]
  ring

theorem mixedIntegral_factorization_map :
    mixedIntegralQuotientFactor.comp ((LinearMap.ker endpointSignature).mkQ) =
      mixedPairValue.comp endpointSignature := by
  ext p
  simp [mixedIntegralQuotientFactor_mkQ]

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
