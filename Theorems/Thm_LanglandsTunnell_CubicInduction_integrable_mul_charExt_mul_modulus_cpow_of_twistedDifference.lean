import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_integrable_mul_charExt_mul_modulus_cpow_of_twistedDifference
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal MeasureTheory

attribute [local instance] LanglandsTunnell.TateLocal.localBorel in

theorem
LanglandsTunnell.CubicInduction.integrable_mul_charExt_mul_modulus_cpow_of_twistedDifference
    (v : HeightOneSpectrum (𝓞 ℚ)) (β : Fin 3 → ℂ)
    (D : ℂ → (v.adicCompletion ℚ → ℂ) → v.adicCompletion ℚ → ℂ)
    (hD : ∀ (α : ℂ) (f : v.adicCompletion ℚ → ℂ) (a : v.adicCompletion ℚ),
      D α f a = f a - α * f (a / (NumberField.AdelicLevel.uniformizerUnit ℚ v : v.adicCompletion ℚ)))
    (φ : v.adicCompletion ℚ → ℂ) (hφ : ∀ t : v.adicCompletion ℚ, t ≠ 0 → ∀ᶠ t' in nhds t, φ t' = φ t)
    (hφB : ∃ B : ℝ, ∀ t : v.adicCompletion ℚ, B < (modulus t : ℝ) → φ t = 0)
    (hrec : ∀ᶠ x in nhds (0 : v.adicCompletion ℚ), D (β 0) (D (β 1) (D (β 2) φ)) x = 0)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) (s : ℂ)
    (hs : ∀ i, ‖β i‖ * ‖(χ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂ)‖ *
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) < 1) :
    Integrable (fun x => φ x * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s) (mulMeasure (selfDualHaarAt ℚ v)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_integrable_mul_charExt_mul_modulus_cpow_of_twistedDifference.solution
