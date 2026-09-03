import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_exists_sFinite_forall_lintegral_withDensity_density_eq_lintegral_lintegral_mul_finFactor_placeEmbed
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions
set_option autoImplicit false
open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open scoped ENNReal in

theorem LanglandsTunnell.RankinSelberg.exists_sFinite_forall_lintegral_withDensity_density_eq_lintegral_lintegral_mul_finFactor_placeEmbed
    [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)]
    (v : HeightOneSpectrum (𝓞 ℚ))
    (μ : Measure (finiteAdelicGL2Subgroup ℚ)) [μ.IsHaarMeasure]
    (μN : Measure RSCarrier.finUnipotent) [μN.IsHaarMeasure] :
    letI := localGLBorel ℚ v
    haveI := borelSpace_localGLBorel ℚ v
    ∀ (μv : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μv.IsHaarMeasure]
      (μNv : Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μNv.IsHaarMeasure],
    ∃ μ' : Measure (finiteAdelicGL2Subgroup ℚ), SFinite μ' ∧
      (∀ᵐ g' : finiteAdelicGL2Subgroup ℚ ∂μ', localAt ℚ v (g' : AdelicGL2 (𝓞 ℚ) ℚ) = 1) ∧
      ∀ Φ : finiteAdelicGL2Subgroup ℚ → ℝ≥0∞, Measurable Φ →
        (∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ), Φ ((n : finiteAdelicGL2Subgroup ℚ) * g) = Φ g) →
        ∫⁻ g, Φ g ∂(μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN)) =
          ∫⁻ g', ∫⁻ x, Φ (g' * RSCarrier.finFactor (UnramifiedWhittaker.placeEmbed ℚ v x))
              ∂(μv.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μNv))
            ∂μ' := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_exists_sFinite_forall_lintegral_withDensity_density_eq_lintegral_lintegral_mul_finFactor_placeEmbed.solution
