import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsEichlerOrder_exists_units_localBox_atkinLehner_of_prime_of_not_dvd
attribute [-instance] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.IsEichlerOrder.exists_units_localBox_atkinLehner_of_prime_of_not_dvd
    {a b : ℚ} {q' : ℕ} (hq' : q'.Prime) (hB : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q')
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : QuaternionAlgebra.IsEichlerOrder R N)
    (q : ℕ) (hq : q.Prime) (hqq' : q ≠ q') (hqN : ¬ q ∣ N)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hqv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    ∃ w : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ,
      ((w : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox R v ∧
        algebraMap ℚ (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) (q : ℚ) * (↑w⁻¹ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox R v ∧
        (↑w⁻¹ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∉ Submodule.localBox R v ∧
        algebraMap ℚ (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) (q : ℚ)⁻¹ * (w : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∉ Submodule.localBox R v) ∧
      ((q : ℚ) • (↑w⁻¹ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox R v ∧
        (q : ℚ)⁻¹ • (w : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∉ Submodule.localBox R v) ∧
      ((w : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * w = algebraMap ℚ (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) (q : ℚ)) ∧
      ∀ O' : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ),
        (∀ x, x ∈ O' ↔ (↑w⁻¹ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * x * w ∈ Submodule.localBox R v) →
        (Submodule.localBox R v ⊓ O').relIndex (Submodule.localBox R v) = q := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_units_localBox_atkinLehner_of_prime_of_not_dvd.solution
