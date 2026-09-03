import Mathlib
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_TateLocal_integrableOn_charExt_mul_norm_inv_and_exists_forall_setIntegral_psiLocal_mul_eq_add_mul_inv_of_lt_zero
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.TateLocal

theorem LanglandsTunnell.TateLocal.integrableOn_charExt_mul_norm_inv_and_exists_forall_setIntegral_psiLocal_mul_eq_add_mul_inv_of_lt_zero
    (p : HeightOneSpectrum (𝓞 ℚ))
    (η : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hη : IsLocallyConstant η)
    (σ : ℝ) (hσ : ∀ a : (p.adicCompletion ℚ)ˣ, ‖((η a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ σ)
    (hσ0 : σ < 0) (n₀ : ℤ) :
    letI := localBorel ℚ p
    ∀ (ν : Measure (p.adicCompletion ℚ)) [ν.IsAddHaarMeasure],
      IntegrableOn (fun t : p.adicCompletion ℚ => charExt η t * ((‖t‖⁻¹ : ℝ) : ℂ))
          {t : p.adicCompletion ℚ | WithZero.exp n₀ ≤ Valued.v t} ν ∧
      ∃ (c : ℝ) (A B : ℂ), 0 < c ∧
        ∀ y : (p.adicCompletion ℚ)ˣ, ‖(y : p.adicCompletion ℚ)‖ ≤ c →
          ∫ t in {t : p.adicCompletion ℚ | WithZero.exp n₀ ≤ Valued.v t},
              NumberField.StandardAddChar.psiLocal ℚ p ((y : p.adicCompletion ℚ) * t) *
                (charExt η t * ((‖t‖⁻¹ : ℝ) : ℂ)) ∂ν =
            A + B * (((η y : ℂˣ) : ℂ))⁻¹ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_integrableOn_charExt_mul_norm_inv_and_exists_forall_setIntegral_psiLocal_mul_eq_add_mul_inv_of_lt_zero.solution
