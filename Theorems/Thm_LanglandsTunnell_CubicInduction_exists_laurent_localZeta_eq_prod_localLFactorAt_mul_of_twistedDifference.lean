import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_prod_localLFactorAt_mul_of_twistedDifference
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal MeasureTheory

attribute [local instance] LanglandsTunnell.TateLocal.localBorel in

theorem
LanglandsTunnell.CubicInduction.exists_laurent_localZeta_eq_prod_localLFactorAt_mul_of_twistedDifference
    (v : HeightOneSpectrum (𝓞 ℚ)) (η : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hu : ∀ i, ‖((η i) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂ)‖ = 1)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) (c : Fin 3 → ℂ)
    (hc₀ : ∀ i, HasConductorExponentAt ℚ v (η i) 0 →
      c i * (χ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂ) =
        ((η i) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂ))
    (hc₁ : ∀ i, ¬ HasConductorExponentAt ℚ v (η i) 0 → c i = 0)
    (D : ℂ → (v.adicCompletion ℚ → ℂ) → v.adicCompletion ℚ → ℂ)
    (hD : ∀ (α : ℂ) (f : v.adicCompletion ℚ → ℂ) (a : v.adicCompletion ℚ),
      D α f a = f a - α * f (a / (NumberField.AdelicLevel.uniformizerUnit ℚ v : v.adicCompletion ℚ)))
    (φ : v.adicCompletion ℚ → ℂ) (hφ : ∀ t : v.adicCompletion ℚ, t ≠ 0 → ∀ᶠ t' in nhds t, φ t' = φ t)
    (hφB : ∃ B : ℝ, ∀ t : v.adicCompletion ℚ, B < (modulus t : ℝ) → φ t = 0)
    (hrec : ∀ᶠ x in nhds (0 : v.adicCompletion ℚ),
      D (c 0) (D (c 1) (D (c 2) (fun a =>
        (∫ w in {x : v.adicCompletion ℚ | Valued.v x = 1}, φ (a * w) * charExt χ w
            ∂(mulMeasure (selfDualHaarAt ℚ v))) /
          (((mulMeasure (selfDualHaarAt ℚ v)).real {x : v.adicCompletion ℚ | Valued.v x = 1} : ℝ) : ℂ)))) x = 0) :
    ∃ P : ℂ → ℂ,
      (∃ (Q : Polynomial ℂ) (m : ℕ), ∀ s : ℂ,
        P s = Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
      ∀ s : ℂ, 0 < s.re →
        Integrable (fun x => φ x * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s) (mulMeasure (selfDualHaarAt ℚ v)) →
          localZeta (selfDualHaarAt ℚ v) φ χ s = (∏ i, localLFactorAt ℚ v (η i) s) * P s := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_prod_localLFactorAt_mul_of_twistedDifference.solution
