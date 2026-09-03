import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsEichlerOrder_forall_mem_imp_mem_iff_exists_levelModule_qmPeriodLattice_eq
attribute [-instance] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra CerednikDrinfeld

theorem QuaternionAlgebra.IsEichlerOrder.forall_mem_imp_mem_iff_exists_levelModule_qmPeriodLattice_eq
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (τ : UpperHalfPlane) (M : Submodule ℤ (Fin 2 → ℂ))
    (hLM : qmPeriodLattice ι Λ τ ≤ M) (hMN : ∀ v ∈ M, ((N : ℤ) • v) ∈ qmPeriodLattice ι Λ τ)
    (hMstab : ∀ x ∈ Λ, ∀ v ∈ M, ((ι x).map (algebraMap ℝ ℂ)).mulVec v ∈ M)
    (hidx : (qmPeriodLattice ι Λ τ).toAddSubgroup.relIndex M.toAddSubgroup = N ^ 2) :
    (∀ (lam : ℍ[ℚ, a, b]), lam ∈ Λ → ∀ r ∈ R,
        ((N : ℂ)⁻¹) • qmPeriodMap ι τ lam ∈ M → ((N : ℂ)⁻¹) • qmPeriodMap ι τ (lam * r) ∈ M) ↔
    ∃ J' : Submodule ℤ ℍ[ℚ, a, b],
      (Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
        Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2 ∧ (∀ x ∈ Λ, x ∈ R ↔ ∀ y ∈ J', y * x ∈ J')) ∧
      M = qmPeriodLattice ι J' τ := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsEichlerOrder_forall_mem_imp_mem_iff_exists_levelModule_qmPeriodLattice_eq.solution
