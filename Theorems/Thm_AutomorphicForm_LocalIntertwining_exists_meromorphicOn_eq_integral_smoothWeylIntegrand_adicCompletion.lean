import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Mathlib.Analysis.Meromorphic.Basic
import P2M.Util
import P2M.Sol.S_AutomorphicForm_LocalIntertwining_exists_meromorphicOn_eq_integral_smoothWeylIntegrand_adicCompletion
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem AutomorphicForm.LocalIntertwining.exists_meromorphicOn_eq_integral_smoothWeylIntegrand_adicCompletion
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∃ c : ℕ, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v c, χ u = 1)
    (m : ℕ) (hm : 1 ≤ m)
    (A : ℂ → v.adicCompletion F → ℂ)
    (hA : ∀ s : ℂ, ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → A s y = A s x)
    (hAhol : ∀ x : v.adicCompletion F, Differentiable ℂ (fun s : ℂ => A s x))
    (B : ℂ → v.adicCompletion F → ℂ)
    (hB : ∀ s : ℂ, ∀ x y : v.adicCompletion F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B s y = B s x)
    (hBhol : ∀ y : v.adicCompletion F, Differentiable ℂ (fun s : ℂ => B s y)) :
    ∃ M : ℂ → ℂ, MeromorphicOn M Set.univ ∧
      ∀ s : ℂ, ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1 →
        M s =
          ∫ x, ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (A s) x
              + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
                  (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                    * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B s y⁻¹) x) ∂μ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_LocalIntertwining_exists_meromorphicOn_eq_integral_smoothWeylIntegrand_adicCompletion.solution
