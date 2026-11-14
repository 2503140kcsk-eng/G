import Mathlib

/-!
# Mixed kernel quotient factorization

This file proves an explicit split-kernel decomposition, the universal
factorization through the quotient by a kernel, and its application to a
mixed Bochner integral.

A mixed kernel is a measurable family of continuous bilinear forms
K x : V →L[ℝ] W →L[ℝ] ℝ. Its Bochner integral is a continuous bilinear
form, and evaluation at vectors commutes with integration.

The concrete integrand from the project request was not present in the
message payload, so the theorem is stated at the operator level and can be
instantiated with the intended kernel.
-/

open MeasureTheory

noncomputable section

namespace MixedKernelQuotient

/-! ## 1. The split-kernel theorem -/

section SplitKernel

variable {R V W : Type*}
variable [Ring R]
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]

/-- If s is a linear right inverse of f, then f (s w) = w. -/
theorem splitSection_apply
    (f : V →ₗ[R] W) (s : W →ₗ[R] V)
    (hs : f.comp s = LinearMap.id) (w : W) :
    f (s w) = w := by
  have h := congrArg (fun g : W →ₗ[R] W => g w) hs
  simpa using h

/-- Split-kernel theorem: a linear map with a linear section decomposes its
domain as the product of its kernel and codomain. The inverse sends (k,w)
to k + s w. -/
def splitKerEquiv
    (f : V →ₗ[R] W) (s : W →ₗ[R] V)
    (hs : f.comp s = LinearMap.id) :
    V ≃ₗ[R] LinearMap.ker f × W where
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
  map_smul' c v := by
    apply Prod.ext
    · apply Subtype.ext
      change c • v - s (f (c • v)) = c • (v - s (f v))
      simp only [map_smul]
      module
    · simp

/-- A split epimorphism identifies the quotient by its kernel with the
codomain. -/
noncomputable def splitKerQuotientEquiv
    (f : V →ₗ[R] W) (s : W →ₗ[R] V)
    (hs : f.comp s = LinearMap.id) :
    (V ⧸ LinearMap.ker f) ≃ₗ[R] W :=
  f.quotKerEquivOfSurjective
    (fun w => ⟨s w, splitSection_apply f s hs w⟩)

end SplitKernel

/-! ## 2. Universal factorization through the kernel quotient -/

section KernelQuotient

variable {R V U : Type*}
variable [Ring R]
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup U] [Module R U]

/-- The induced map from the quotient by the kernel to the original
codomain, with codomain restricted to the range. -/
noncomputable def factorThroughKernelQuotient (T : V →ₗ[R] U) :
    (V ⧸ LinearMap.ker T) →ₗ[R] U :=
  (LinearMap.range T).subtype.comp T.quotKerEquivRange.toLinearMap

/-- Every linear map factors through the quotient by its kernel. -/
theorem factorThroughKernelQuotient_comp_mkQ (T : V →ₗ[R] U) :
    (factorThroughKernelQuotient T).comp (T.ker.mkQ) = T := by
  ext x
  simp [factorThroughKernelQuotient]

end KernelQuotient

/-! ## 3. Mixed integral operator -/

section MixedIntegral

variable {α V W : Type*}
variable [MeasurableSpace α]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The Bochner integral of a family of continuous bilinear forms. -/
noncomputable def mixedIntegralOperator
    (μ : Measure α)
    (K : α → V →L[ℝ] W →L[ℝ] ℝ) :
    V →L[ℝ] W →L[ℝ] ℝ :=
  ∫ x, K x ∂μ

/-- The linear operator associated to the mixed integral. -/
noncomputable def mixedIntegralMap
    (μ : Measure α)
    (K : α → V →L[ℝ] W →L[ℝ] ℝ) :
    V →ₗ[ℝ] W →L[ℝ] ℝ :=
  (mixedIntegralOperator μ K).toLinearMap

/-- Evaluation at both variables commutes with the mixed Bochner integral. -/
theorem mixedIntegral_evaluation
    (μ : Measure α)
    (K : α → V →L[ℝ] W →L[ℝ] ℝ)
    (hK : Integrable K μ) (v : V) (w : W) :
    mixedIntegralOperator μ K v w = ∫ x, K x v w ∂μ := by
  have hV : Integrable (fun x => K x v) μ := by
    exact (ContinuousLinearMap.apply ℝ (W →L[ℝ] ℝ) v).integrable_comp hK
  change (∫ x, K x ∂μ) v w = _
  rw [ContinuousLinearMap.integral_apply hK v,
      ContinuousLinearMap.integral_apply hV w]

/-- Main quotient-factorization theorem for the mixed integral operator. -/
theorem mixedIntegral_factors_through_kernel_quotient
    (μ : Measure α)
    (K : α → V →L[ℝ] W →L[ℝ] ℝ) :
    (factorThroughKernelQuotient (mixedIntegralMap μ K)).comp
      ((mixedIntegralMap μ K).ker.mkQ) = mixedIntegralMap μ K :=
  factorThroughKernelQuotient_comp_mkQ (mixedIntegralMap μ K)

end MixedIntegral

end MixedKernelQuotient
