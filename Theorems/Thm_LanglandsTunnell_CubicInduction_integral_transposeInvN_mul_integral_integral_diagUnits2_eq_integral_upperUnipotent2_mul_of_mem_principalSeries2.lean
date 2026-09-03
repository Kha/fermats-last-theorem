import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_SmoothingKernel
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_integral_transposeInvN_mul_integral_integral_diagUnits2_eq_integral_upperUnipotent2_mul_of_mem_principalSeries2
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.integral_transposeInvN_mul_integral_integral_diagUnits2_eq_integral_upperUnipotent2_mul_of_mem_principalSeries2
    (p : HeightOneSpectrum (𝓞 ℚ))

    (ψ : AddChar (p.adicCompletion ℚ) ℂ) (W : LocalGL3 p → ℂ) (hW : IsGL3PsiWhittakerFn ψ W)
    (ω : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hω : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : LocalGL3 p),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((ω z : ℂˣ) : ℂ) * W g)

    (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (f : LocalGL2 p → ℂ) (hf : f ∈ principalSeries2 p χ)
    (w₀p : LocalGL2 p) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (s : ℂ) :
    letI := localBorel ℚ p
    ∀ (μ : Measure (p.adicCompletion ℚ)ˣ) [μ.IsMulLeftInvariant]
      (ν : Measure (p.adicCompletion ℚ)) [ν.IsAddHaarMeasure],
      (∫ y : p.adicCompletion ℚ,
          f (w₀p * AutomorphicForm.transposeInvN (Fin 2) (w₀p * upperUnipotent2 p y)) *
            (∫ a : (p.adicCompletion ℚ)ˣ, ∫ t : (p.adicCompletion ℚ)ˣ,
              ((((χ 1) a : ℂˣ) : ℂ)⁻¹ * ((ω a : ℂˣ) : ℂ)⁻¹ * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s *
                ((((χ 0) t : ℂˣ) : ℂ) * ((modulus (t : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-s - 1))) *
              W (iotaGL (diagUnits2 (t * a) a) *
                (longWeyl3 * upperUnipotent3 0 0 (-y) * longWeyl3 * weylPrime3)) ∂μ ∂μ) ∂ν) =
        ∫ y : p.adicCompletion ℚ,
          f (w₀p * upperUnipotent2 p y) *
            (∫ a : (p.adicCompletion ℚ)ˣ, ∫ t : (p.adicCompletion ℚ)ˣ,
              ((((χ 1) a : ℂˣ) : ℂ)⁻¹ * ((ω a : ℂˣ) : ℂ)⁻¹ * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s *
                ((((χ 0) t : ℂˣ) : ℂ) * ((modulus (t : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-s - 1))) *
              W (iotaGL (diagUnits2 (t * a) a) *
                (longWeyl3 * upperUnipotent3 0 0 y * weylPrime3)) ∂μ ∂μ) ∂ν := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_integral_transposeInvN_mul_integral_integral_diagUnits2_eq_integral_upperUnipotent2_mul_of_mem_principalSeries2.solution
