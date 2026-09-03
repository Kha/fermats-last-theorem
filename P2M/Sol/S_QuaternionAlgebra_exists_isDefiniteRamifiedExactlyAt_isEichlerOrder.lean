import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Theorems.Thm_QuaternionAlgebra_exists_isDefiniteRamifiedExactlyAt
import Theorems.Thm_QuaternionAlgebra_exists_isMaximalOrder
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_le_isEichlerOrder_of_isDefiniteRamifiedExactlyAt
import P2M.Util
namespace P2MW.S_QuaternionAlgebra_exists_isDefiniteRamifiedExactlyAt_isEichlerOrder
attribute [-instance] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem solution
    (q : ℕ) (hq : q.Prime) (N : ℕ) (hN : N ≠ 0) (hqN : ¬ q ∣ N) :
    ∃ a b : ℚ, QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q ∧
      ∃ Λ : Submodule ℤ ℍ[ℚ, a, b], QuaternionAlgebra.IsEichlerOrder Λ N := by
  obtain ⟨a, b, hB⟩ := QuaternionAlgebra.exists_isDefiniteRamifiedExactlyAt q hq
  obtain ⟨Λ₁, h₁⟩ := QuaternionAlgebra.exists_isMaximalOrder a b hB.neg_left.ne hB.neg_right.ne
  obtain ⟨Λ, -, hΛ⟩ := QuaternionAlgebra.IsMaximalOrder.exists_le_isEichlerOrder_of_isDefiniteRamifiedExactlyAt hq hB h₁ N hN hqN
  exact ⟨a, b, hB, Λ, hΛ⟩
