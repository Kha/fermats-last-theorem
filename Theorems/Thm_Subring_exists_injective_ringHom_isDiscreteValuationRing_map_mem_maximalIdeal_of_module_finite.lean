import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Finiteness.Defs
import P2M.Util
import P2M.Sol.S_Subring_exists_injective_ringHom_isDiscreteValuationRing_map_mem_maximalIdeal_of_module_finite
attribute [-instance] instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

theorem Subring.exists_injective_ringHom_isDiscreteValuationRing_map_mem_maximalIdeal_of_module_finite
    (A : Subring ℂ) [Module.Finite ℤ A] (l : ℕ) [Fact l.Prime]
    (𝔪A : Ideal A) [𝔪A.IsPrime] (hl : (l : A) ∈ 𝔪A) :
    ∃ (𝓞' : Type) (_ : CommRing 𝓞') (_ : IsDomain 𝓞') (_ : IsDiscreteValuationRing 𝓞')
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal 𝓞') 𝓞')
      (_ : Finite (IsLocalRing.ResidueField 𝓞')) (_ : CharZero 𝓞'),
      (l : 𝓞') ∈ IsLocalRing.maximalIdeal 𝓞' ∧
        ∃ ι : A →+* 𝓞', Function.Injective ι ∧
          ∀ x : A, x ∈ 𝔪A → ι x ∈ IsLocalRing.maximalIdeal 𝓞' := by p2m_exact_reverting @_root_.P2MW.S_Subring_exists_injective_ringHom_isDiscreteValuationRing_map_mem_maximalIdeal_of_module_finite.solution
