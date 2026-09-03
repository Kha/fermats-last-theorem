import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_NumberField_AdelicLevel
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_TateLocal_hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker NumberField.AdelicLevel

theorem
  LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localBorel ℚ p
    (∀ n : ℤ, MeasurableSet {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(n))}) ∧
    (∀ y : (p.adicCompletion ℚ)ˣ,
      ∃! n : ℤ, y ∈ {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(n))}) ∧
    (∀ n : ℤ,
      (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
          {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(n))} =
        (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
          {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-((0 : ℤ)))} ∧
      0 < (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
          {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(n))} ∧
      (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
          {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(n))} < ⊤) ∧
    (∀ (n : ℤ) (y : (p.adicCompletion ℚ)ˣ),
      y ∈ {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(n))} →
      (modulus (y : p.adicCompletion ℚ) : ℝ) = ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ (-n)) ∧
    (∀ f : (p.adicCompletion ℚ)ˣ → ℂ, Integrable f (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) →
      HasSum
        (fun n : ℤ =>
          ∫ y in {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(n))}, f y
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))))
        (∫ y, f y ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq.solution
