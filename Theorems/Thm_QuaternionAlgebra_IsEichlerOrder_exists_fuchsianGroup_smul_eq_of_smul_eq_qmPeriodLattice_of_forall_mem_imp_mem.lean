import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsEichlerOrder_exists_fuchsianGroup_smul_eq_of_smul_eq_qmPeriodLattice_of_forall_mem_imp_mem
attribute [-instance] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra CerednikDrinfeld

theorem QuaternionAlgebra.IsEichlerOrder.exists_fuchsianGroup_smul_eq_of_smul_eq_qmPeriodLattice_of_forall_mem_imp_mem
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (L M : Submodule ℤ (Fin 2 → ℂ))
    (hLM : L ≤ M) (hMN : ∀ v ∈ M, ((N : ℤ) • v) ∈ L)
    (hMstab : ∀ x ∈ Λ, ∀ v ∈ M, ((ι x).map (algebraMap ℝ ℂ)).mulVec v ∈ M)
    (hidx : L.toAddSubgroup.relIndex M.toAddSubgroup = N ^ 2)
    (τ₁ τ₂ : UpperHalfPlane) (c₁ c₂ : ℂ) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0)
    (hL₁ : c₁ • L = qmPeriodLattice ι Λ τ₁) (hL₂ : c₂ • L = qmPeriodLattice ι Λ τ₂)
    (hlev₁ : (∀ (lam : ℍ[ℚ, a, b]), lam ∈ Λ → ∀ r ∈ R,
        ((N : ℂ)⁻¹) • qmPeriodMap ι τ₁ lam ∈ c₁ • M → ((N : ℂ)⁻¹) • qmPeriodMap ι τ₁ (lam * r) ∈ c₁ • M))
    (hlev₂ : (∀ (lam : ℍ[ℚ, a, b]), lam ∈ Λ → ∀ r ∈ R,
        ((N : ℂ)⁻¹) • qmPeriodMap ι τ₂ lam ∈ c₂ • M → ((N : ℂ)⁻¹) • qmPeriodMap ι τ₂ (lam * r) ∈ c₂ • M)) :
    ∃ γ ∈ fuchsianGroup R ι, γ • τ₁ = τ₂ := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_fuchsianGroup_smul_eq_of_smul_eq_qmPeriodLattice_of_forall_mem_imp_mem.solution
