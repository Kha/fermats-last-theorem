import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_setIntegral_valuationShell_eq_zero_of_forall_integral_mul_modulus_cpow_eq_zero
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal MeasureTheory
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.setIntegral_valuationShell_eq_zero_of_forall_integral_mul_modulus_cpow_eq_zero
    (v : HeightOneSpectrum (𝓞 ℚ)) (F : (v.adicCompletion ℚ)ˣ → ℂ) (σ : ℝ) (K : ℤ)
    (hsupp : ∀ a : (v.adicCompletion ℚ)ˣ, WithZero.exp K < Valued.v (a : v.adicCompletion ℚ) → F a = 0)
    (hint : letI := localBorel ℚ v
      ∀ s : ℂ, σ < s.re → Integrable
        (fun a : (v.adicCompletion ℚ)ˣ => F a * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1))
        (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))))
    (hzero : letI := localBorel ℚ v
      ∀ s : ℂ, σ < s.re →
        ∫ a : (v.adicCompletion ℚ)ˣ, F a * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) = 0) :
    letI := localBorel ℚ v
    ∀ k : ℤ, ∫ a in {a : (v.adicCompletion ℚ)ˣ | Valued.v (a : v.adicCompletion ℚ) = WithZero.exp (-k)}, F a
      ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) = 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_setIntegral_valuationShell_eq_zero_of_forall_integral_mul_modulus_cpow_eq_zero.solution
