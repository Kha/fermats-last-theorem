import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_NumberField_AdelicFourier
import P2M.Util
import P2M.Sol.S_UnramifiedWhittaker_integrable_and_differentiable_integral_mul_zetaIntegrand_sPartMeasure_of_bounded
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.TateGlobal
open UnramifiedWhittaker

theorem UnramifiedWhittaker.integrable_and_differentiable_integral_mul_zetaIntegrand_sPartMeasure_of_bounded
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (Wg : AdelicGL2 (𝓞 F) F → ℂ) (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (μ : (AdeleRing (𝓞 F) F)ˣ → ℝ)
    (Ω K : Set (AdeleRing (𝓞 F) F)ˣ) (hΩm : MeasurableSet[NumberField.Idele.ideleBorel F] Ω) (hKm : MeasurableSet[NumberField.Idele.ideleBorel F] K)
    (hΩ : NumberField.Idele.sPartMeasure F S Ωᶜ = 0) (hK : NumberField.Idele.sPartMeasure F S K < ⊤)
    (M₀ M₁ X r R : ℝ) (hr : 0 < r)
    (hmeas : ∀ s : ℂ, Measurable[NumberField.Idele.ideleBorel F] fun a => (μ a : ℂ) * zetaIntegrand Wg χ s a)
    (hμ : ∀ a, |μ a| ≤ M₀)
    (hsupp : ∀ a ∈ Ω, a ∉ K → μ a = 0)
    (hKb : ∀ a ∈ K, ‖Wg (diagOne a)‖ ≤ M₁ ∧ ‖((χ a : ℂˣ) : ℂ)‖ ≤ X ∧ r ≤ ideleNorm F a ∧ ideleNorm F a ≤ R) :
    (∀ s : ℂ, Integrable (fun a => (μ a : ℂ) * zetaIntegrand Wg χ s a) (NumberField.Idele.sPartMeasure F S)) ∧
    Differentiable ℂ (fun s : ℂ => ∫ a, (μ a : ℂ) * zetaIntegrand Wg χ s a ∂(NumberField.Idele.sPartMeasure F S)) := by p2m_exact_reverting @_root_.P2MW.S_UnramifiedWhittaker_integrable_and_differentiable_integral_mul_zetaIntegrand_sPartMeasure_of_bounded.solution
