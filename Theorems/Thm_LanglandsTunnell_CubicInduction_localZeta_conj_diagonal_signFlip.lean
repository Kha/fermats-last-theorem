import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalWhittakerDatum
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_localZeta_conj_diagonal_signFlip
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.localZeta_conj_diagonal_signFlip
    (v : HeightOneSpectrum (𝓞 ℚ)) (W : LocalGL3 v → ℂ)
    (ωv : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hω : ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ωv t : ℂˣ) : ℂ) * W h) :
    let δ : LocalGL3 v := iotaGL (Matrix.GeneralLinearGroup.scalar (Fin 2) (-1 : (v.adicCompletion ℚ)ˣ) * diagOne (-1 : (v.adicCompletion ℚ)ˣ))
    let W₀ : LocalGL3 v → ℂ := fun g => W (δ * g * δ⁻¹)
    letI := localBorel ℚ v
    (dualWhittakerFn3 W₀ = fun g => dualWhittakerFn3 W (δ * g * δ⁻¹)) ∧
    (∀ (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (g : LocalGL3 v),
      localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W₀ χ s g =
        localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ s (δ * g * δ⁻¹)) ∧
    (∀ (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (g : LocalGL3 v) (σ₀ : ℝ),
      IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W₀ χ g σ₀ ↔
        IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ (δ * g * δ⁻¹) σ₀) ∧
    (∀ (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (g : LocalGL3 v),
      localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) W₀ χ s g =
        ((ωv (-1) : ℂˣ) : ℂ) * ((χ (-1) : ℂˣ) : ℂ) *
          localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v) W χ s
            (δ * g * δ⁻¹)) ∧
    (∀ (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (g : LocalGL3 v) (σ₁ : ℝ),
      IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
          (dualWhittakerFn3 W₀) χ (weylPrime3 * transposeInv3 g) σ₁ ↔
        IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
          (dualWhittakerFn3 W) χ (weylPrime3 * transposeInv3 (δ * g * δ⁻¹)) σ₁) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_localZeta_conj_diagonal_signFlip.solution
