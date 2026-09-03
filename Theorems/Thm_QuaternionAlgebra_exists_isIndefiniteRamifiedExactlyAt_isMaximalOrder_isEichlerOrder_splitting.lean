import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_exists_isIndefiniteRamifiedExactlyAt_isMaximalOrder_isEichlerOrder_splitting
attribute [-instance] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false
open scoped TensorProduct Quaternion NumberField
open QuaternionAlgebra

theorem QuaternionAlgebra.exists_isIndefiniteRamifiedExactlyAt_isMaximalOrder_isEichlerOrder_splitting
    (q q' N : ℕ) (hq : q.Prime) (hq' : q'.Prime) (hqq' : q' ≠ q) (hN : N ≠ 0) (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) :
    ∃ a b : ℚ, IsIndefiniteRamifiedExactlyAt a b q q' ∧
      ∃ Λ R : Submodule ℤ ℍ[ℚ, a, b], IsMaximalOrder Λ ∧ IsEichlerOrder R N ∧ R ≤ Λ ∧
        ∃ ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ, Function.Injective ι := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_exists_isIndefiniteRamifiedExactlyAt_isMaximalOrder_isEichlerOrder_splitting.solution
