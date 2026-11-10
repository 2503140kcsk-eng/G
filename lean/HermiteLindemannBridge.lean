module
public import Mathlib
public import AlgebraicClosure

@[expose] public section

/-!
# The Hermite–Lindemann interface and its elementary specializations

This module isolates the exact analytic input needed from Hermite–Lindemann.
It does NOT postulate that input as an axiom and does NOT claim to prove it.
The propositions below are the algebraic consequences that follow once the
analytic theorem has been independently established.
-/

namespace HermiteLindemannBridge

/--
The Hermite–Lindemann statement over ℚ and ℂ:
the exponential of every nonzero algebraic complex number is transcendental.
This is a proposition, not an axiom.
-/
def HermiteLindemannInput : Prop :=
  ∀ z : ℂ, IsAlgebraic ℚ z → z ≠ 0 → Transcendental ℚ (Complex.exp z)

/-- The imaginary unit is algebraic over ℚ, since it is a root of X² + 1. -/
theorem isAlgebraic_complex_I : IsAlgebraic ℚ (Complex.I : ℂ) := by
  refine ⟨Polynomial.X ^ 2 + 1, ?_, ?_⟩
  · intro hp
    have hc := congrArg (fun p : Polynomial ℚ => p.coeff 2) hp
    norm_num at hc
  · simp [Complex.I_mul_I]

/--
Hermite–Lindemann at 1 gives transcendence of e.
The real-to-complex passage uses Mathlib's Complex.ofReal_exp.
-/
theorem transcendental_e_of_hermite_lindemann
    (hHL : HermiteLindemannInput) :
    Transcendental ℚ (Real.exp 1) := by
  have hcomplex : Transcendental ℚ (Complex.exp (1 : ℂ)) :=
    hHL 1 (isAlgebraic_one (R := ℚ) (A := ℂ)) (by norm_num)
  intro he
  apply hcomplex
  have heC : IsAlgebraic ℚ (algebraMap ℝ ℂ (Real.exp 1)) := he.algebraMap
  simpa only [Complex.ofReal_exp] using heC

/--
Assuming Hermite–Lindemann, π is transcendental.
If π were algebraic, then iπ would be nonzero algebraic, while
exp(iπ) = -1 is algebraic, contradicting Hermite–Lindemann.
-/
theorem transcendental_pi_of_hermite_lindemann
    (hHL : HermiteLindemannInput) :
    Transcendental ℚ Real.pi := by
  intro hpi
  have hpiC : IsAlgebraic ℚ (algebraMap ℝ ℂ Real.pi) := hpi.algebraMap
  have hαalg : IsAlgebraic ℚ (Complex.I * algebraMap ℝ ℂ Real.pi) :=
    AlgebraicNumberClosureFormalization.isAlgebraic_mul
      isAlgebraic_complex_I hpiC
  have hαne : Complex.I * algebraMap ℝ ℂ Real.pi ≠ 0 := by
    apply mul_ne_zero Complex.I_ne_zero
    simpa using (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hexp_trans : Transcendental ℚ
      (Complex.exp (Complex.I * algebraMap ℝ ℂ Real.pi)) :=
    hHL _ hαalg hαne
  have hexp_eq : Complex.exp (Complex.I * algebraMap ℝ ℂ Real.pi) = -1 := by
    change Complex.exp (Complex.I * (Real.pi : ℂ)) = -1
    rw [mul_comm, Complex.exp_pi_mul_I]
  have hminus : IsAlgebraic ℚ (-1 : ℂ) :=
    AlgebraicNumberClosureFormalization.isAlgebraic_neg
      (isAlgebraic_one (R := ℚ) (A := ℂ))
  exact hexp_trans (hexp_eq ▸ hminus)

/-! ## Kernel audit -/
#print axioms isAlgebraic_complex_I
#print axioms transcendental_e_of_hermite_lindemann
#print axioms transcendental_pi_of_hermite_lindemann

end HermiteLindemannBridge
