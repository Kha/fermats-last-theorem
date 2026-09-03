import Definitions.Def_NumberField_TateGlobalZeta
import P2M.Util
import P2M.Sol.S_NumberField_TateGlobal_integrableOn_and_differentiable_setIntegral_mul_ideleNorm_cpow_of_norm_le_min_pow
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open NumberField NumberField.TateGlobal MeasureTheory

theorem NumberField.TateGlobal.integrableOn_and_differentiable_setIntegral_mul_ideleNorm_cpow_of_norm_le_min_pow
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ)
    (D : Set (AdeleRing (𝓞 F) F)ˣ) (hD : MeasurableSet D)
    (htemp : ∀ r : ℝ, ∃ k : ℕ, IntegrableOn
      (fun a => min (ideleNorm F a) (ideleNorm F a)⁻¹ ^ k * ideleNorm F a ^ r) D ν)
    (h : (AdeleRing (𝓞 F) F)ˣ → ℂ) (hh : AEStronglyMeasurable h (ν.restrict D))
    (hdec : ∀ k : ℕ, ∃ C : ℝ, ∀ a ∈ D, ‖h a‖ ≤ C * min (ideleNorm F a) (ideleNorm F a)⁻¹ ^ k) :
    (∀ s : ℂ, IntegrableOn (fun a => h a * ((ideleNorm F a : ℝ) : ℂ) ^ s) D ν) ∧
      Differentiable ℂ (fun s : ℂ => ∫ a in D, h a * ((ideleNorm F a : ℝ) : ℂ) ^ s ∂ν) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_TateGlobal_integrableOn_and_differentiable_setIntegral_mul_ideleNorm_cpow_of_norm_le_min_pow.solution
