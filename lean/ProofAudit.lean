import MixedKernelQuotient

/-!
# ProofAudit

The declarations below expose the mathematical claims that CI must audit.
Only the standard allowlist propext, Classical.choice, and Quot.sound is
permitted by the GitHub Actions workflow.
-/

namespace ProofAudit

/-- Audit target: split decomposition of the source space. -/
noncomputable def split_kernel_decomposition
    {R V W : Type*} [Ring R]
    [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W]
    (f : V →ₗ[R] W) (s : W →ₗ[R] V)
    (hs : f.comp s = LinearMap.id) :
    V ≃ₗ[R] LinearMap.ker f × W :=
  MixedKernelQuotient.splitKerEquiv f s hs

/-- Audit target: the quotient by the kernel of a split epimorphism. -/
noncomputable def split_kernel_quotient_equivalence
    {R V W : Type*} [Ring R]
    [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W]
    (f : V →ₗ[R] W) (s : W →ₗ[R] V)
    (hs : f.comp s = LinearMap.id) :
    (V ⧸ LinearMap.ker f) ≃ₗ[R] W :=
  MixedKernelQuotient.splitKerQuotientEquiv f s hs

/-- Audit target: the pointwise mixed-integral identity. -/
theorem mixed_integral_evaluation
    {α V W : Type*} [MeasurableSpace α]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure α)
    (K : α → V →L[ℝ] W →L[ℝ] ℝ)
    (hK : MeasureTheory.Integrable K μ) (v : V) (w : W) :
    MixedKernelQuotient.mixedIntegralOperator μ K v w =
      ∫ x, K x v w ∂μ :=
  MixedKernelQuotient.mixedIntegral_evaluation μ K hK v w

/-- Main audited theorem: the mixed integral factors through the quotient
by the kernel of its associated linear operator. -/
theorem mixed_integral_factors_through_quotient
    {α V W : Type*} [MeasurableSpace α]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure α)
    (K : α → V →L[ℝ] W →L[ℝ] ℝ) :
    (MixedKernelQuotient.factorThroughKernelQuotient
        (MixedKernelQuotient.mixedIntegralMap μ K)).comp
      ((MixedKernelQuotient.mixedIntegralMap μ K).ker.mkQ) =
        MixedKernelQuotient.mixedIntegralMap μ K :=
  MixedKernelQuotient.mixedIntegral_factors_through_kernel_quotient μ K

end ProofAudit

#print axioms ProofAudit.split_kernel_decomposition
#print axioms ProofAudit.split_kernel_quotient_equivalence
#print axioms ProofAudit.mixed_integral_evaluation
#print axioms ProofAudit.mixed_integral_factors_through_quotient
