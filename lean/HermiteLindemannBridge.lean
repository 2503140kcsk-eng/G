module
public import Mathlib
public import AlgebraicClosure
public import Mathlib.NumberTheory.Transcendental.Lindemann.AnalyticalPart
public import LindemannBasic

@[expose] public section

/-!
# The Hermite–Lindemann interface and its elementary specializations

This module connects Mathlib's analytic approximation lemma to the
vendored Lindemann–Weierstrass proof. It derives the Hermite–Lindemann
conclusion, then specializes it to the transcendence of e and π.
-/

namespace HermiteLindemannBridge

open scoped Nat

/-- The imaginary unit is algebraic over ℚ, since it is a root of X² + 1. -/
theorem isAlgebraic_complex_I : IsAlgebraic ℚ (Complex.I : ℂ) := by
  refine ⟨Polynomial.X ^ 2 + 1, ?_, ?_⟩
  · intro hp
    have hc := congrArg (fun p : Polynomial ℚ => p.eval 0) hp
    norm_num at hc
  · simp

lemma lindemann_analytic_approximation
    (f : Polynomial ℤ) (hf : Polynomial.eval 0 f ≠ 0) :
    ∃ c,
      ∀ p > (Polynomial.eval 0 f).natAbs, p.Prime →
        ∃ nₚ : ℤ, ¬ ↑p ∣ nₚ ∧ ∃ gₚ : Polynomial ℤ,
          gₚ.natDegree ≤ p * f.natDegree - 1 ∧
          ∀ {r : ℂ}, r ∈ Polynomial.aroots f ℂ →
            ‖nₚ • Complex.exp r - p • Polynomial.aeval r gₚ‖ ≤
              c ^ p / (p - 1)! :=
  LindemannWeierstrass.exp_polynomial_approx f hf

#print axioms lindemann_analytic_approximation


/--
Hermite–Lindemann over ℚ, obtained from the vendored Lindemann–Weierstrass
linear-independence theorem. This is a theorem, not an assumed input.
-/
theorem transcendental_exp_of_algebraic
    {z : ℂ} (hz0 : z ≠ 0) (hz : IsAlgebraic ℚ z) :
    Transcendental ℚ (Complex.exp z) := by
  intro h
  let expz : integralClosure ℚ ℂ := ⟨Complex.exp z, h.isIntegral⟩
  have hli : LinearIndependent (integralClosure ℚ ℂ)
      (fun i : Fin 2 => Complex.exp (![z, 0] i)) :=
    Complex.linearIndependent_exp ![z, 0]
      (by simp [hz, isAlgebraic_zero])
      (by simpa [Subtype.ext_iff])
  have hrel := Fintype.linearIndependent_iff.mp hli ![1, -expz] (by
    simp [expz, Algebra.smul_def])
  simp at hrel

/-- The real number e is transcendental over ℚ. -/
theorem transcendental_e : Transcendental ℚ (Real.exp 1) := by
  have hcomplex : Transcendental ℚ (Complex.exp (1 : ℂ)) :=
    transcendental_exp_of_algebraic (by norm_num) (isAlgebraic_one (R := ℚ) (A := ℂ))
  change ¬ IsAlgebraic ℚ (Real.exp 1)
  intro he
  have heC : IsAlgebraic ℚ (algebraMap ℝ ℂ (Real.exp 1)) := he.algebraMap
  have hmap : algebraMap ℝ ℂ (Real.exp 1) = Complex.exp (1 : ℂ) := by
    exact Complex.ofReal_exp 1
  exact hcomplex (hmap ▸ heC)

/-- The real number π is transcendental over ℚ. -/
theorem transcendental_pi : Transcendental ℚ Real.pi := by
  intro hpi
  have hpiC : IsAlgebraic ℚ (algebraMap ℝ ℂ Real.pi) := hpi.algebraMap
  have hαalg : IsAlgebraic ℚ (Complex.I * algebraMap ℝ ℂ Real.pi) :=
    AlgebraicNumberClosureFormalization.isAlgebraic_mul
      isAlgebraic_complex_I hpiC
  have hαne : Complex.I * algebraMap ℝ ℂ Real.pi ≠ 0 := by
    apply mul_ne_zero Complex.I_ne_zero
    exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hexp_trans : Transcendental ℚ
      (Complex.exp (Complex.I * algebraMap ℝ ℂ Real.pi)) :=
    transcendental_exp_of_algebraic hαne hαalg
  have hexp_eq : Complex.exp (Complex.I * algebraMap ℝ ℂ Real.pi) = -1 := by
    change Complex.exp (Complex.I * (Real.pi : ℂ)) = -1
    rw [mul_comm, Complex.exp_pi_mul_I]
  have hminus : IsAlgebraic ℚ (-1 : ℂ) :=
    AlgebraicNumberClosureFormalization.isAlgebraic_neg
      (isAlgebraic_one (R := ℚ) (A := ℂ))
  exact hexp_trans (hexp_eq ▸ hminus)
/-! ## Kernel audit -/
#print axioms Complex.linearIndependent_exp
#print axioms Complex.algebraicIndependent_exp
#print axioms isAlgebraic_complex_I
#print axioms transcendental_exp_of_algebraic
#print axioms transcendental_e
#print axioms transcendental_pi

end HermiteLindemannBridge
