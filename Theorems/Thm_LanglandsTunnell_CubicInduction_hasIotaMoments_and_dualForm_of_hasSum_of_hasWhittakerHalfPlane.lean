import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem LanglandsTunnell.CubicInduction.hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hexp : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, HasSum
      (fun i : MirabolicIndex ℚ =>
      whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ Φ (mirabolicTranslate i * g))
      (Φ g))
    (hexp' : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, HasSum
      (fun i : MirabolicIndex ℚ =>
      whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ⁻¹ (dualForm Φ) (mirabolicTranslate i * g))
      (dualForm Φ g))
    (hhp : HasWhittakerHalfPlane (whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ Φ))
    (hhp' : HasWhittakerHalfPlane (whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ⁻¹ (dualForm Φ))) :
    HasIotaMoments Φ ∧ HasIotaMoments (dualForm Φ) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane.solution
