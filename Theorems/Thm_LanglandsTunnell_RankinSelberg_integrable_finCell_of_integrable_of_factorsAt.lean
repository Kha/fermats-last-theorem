import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_AdelicDock_LocalEmbedding
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_integrable_finCell_of_integrable_of_factorsAt
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions
attribute [-simp] AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
open scoped ENNReal
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem LanglandsTunnell.RankinSelberg.integrable_finCell_of_integrable_of_factorsAt
    [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)]
    (p : HeightOneSpectrum (𝓞 ℚ))
    (μ : Measure (finiteAdelicGL2Subgroup ℚ)) [μ.IsHaarMeasure]
    (μN : Measure RSCarrier.finUnipotent) [μN.IsHaarMeasure]
    (W F W₀ F₀ W' F' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (w f w₀ f₀ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hW : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, W g = w (localAt ℚ p g) * W' g)
    (hW₀ : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, W₀ g = w₀ (localAt ℚ p g) * W' g)
    (hF : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, F g = f (localAt ℚ p g) * F' g)
    (hF₀ : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, F₀ g = f₀ (localAt ℚ p g) * F' g)
    (hW' : ∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ), W' (g * placeEmbed ℚ p x) = W' g)
    (hF' : ∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ), F' (g * placeEmbed ℚ p x) = F' g)
    (hN' : ∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
      ‖W' ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) *
          F' ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ)‖ =
        ‖W' (g : AdelicGL2 (𝓞 ℚ) ℚ) * F' (g : AdelicGL2 (𝓞 ℚ) ℚ)‖)
    (hn : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      ‖w (unipotent x * g) * f (unipotent x * g)‖ = ‖w g * f g‖)
    (hn₀ : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      ‖w₀ (unipotent x * g) * f₀ (unipotent x * g)‖ = ‖w₀ g * f₀ g‖)
    (hWFm' : Measurable fun g : finiteAdelicGL2Subgroup ℚ => W' g * F' g)
    (hWFm : Measurable fun g : finiteAdelicGL2Subgroup ℚ => W g * F g)
    (s : ℂ) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
      Measurable (fun y => w y * f y) → Measurable (fun y => w₀ y * f₀ y) →
      Integrable (fun g : finiteAdelicGL2Subgroup ℚ => (W₀ g * F₀ g) *
          ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℂ) ^ (s - 1 / 2)))
        (μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN)) →
      (∫⁻ y : GL (Fin 2) (p.adicCompletion ℚ), ‖(w₀ y * f₀ y) *
          ((modulus ((Matrix.GeneralLinearGroup.det y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ
        ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ≠ 0 →
      (∫⁻ y : GL (Fin 2) (p.adicCompletion ℚ), ‖(w y * f y) *
          ((modulus ((Matrix.GeneralLinearGroup.det y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ
        ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) < ⊤ →
      Integrable (fun g : finiteAdelicGL2Subgroup ℚ => (W g * F g) *
          ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℂ) ^ (s - 1 / 2)))
        (μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_integrable_finCell_of_integrable_of_factorsAt.solution
