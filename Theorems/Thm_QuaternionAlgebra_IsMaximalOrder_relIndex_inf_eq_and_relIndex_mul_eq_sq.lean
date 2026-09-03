import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_relIndex_inf_eq_and_relIndex_mul_eq_sq
attribute [-instance] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions
attribute [-simp] LocalGL2.swapUnit_val QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

theorem QuaternionAlgebra.IsMaximalOrder.relIndex_inf_eq_and_relIndex_mul_eq_sq
    {a b : ℚ} (Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛ' : IsMaximalOrder Λ')
    {N : ℕ} [NeZero N] (hN : (Λ ⊓ Λ').toAddSubgroup.relIndex Λ.toAddSubgroup = N) :
    (Λ ⊓ Λ').toAddSubgroup.relIndex Λ'.toAddSubgroup = N ∧
      Λ.toAddSubgroup.relIndex (Λ * Λ').toAddSubgroup = N ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_relIndex_inf_eq_and_relIndex_mul_eq_sq.solution
