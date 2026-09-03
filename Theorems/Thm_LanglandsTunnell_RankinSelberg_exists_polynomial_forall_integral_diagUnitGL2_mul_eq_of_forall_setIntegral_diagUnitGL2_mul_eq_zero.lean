import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_exists_polynomial_forall_integral_diagUnitGL2_mul_eq_of_forall_setIntegral_diagUnitGL2_mul_eq_zero
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.RankinSelberg.exists_polynomial_forall_integral_diagUnitGL2_mul_eq_of_forall_setIntegral_diagUnitGL2_mul_eq_zero
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    {ϖ : v.adicCompletionIntegers K}
    (hπ : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) = WithZero.exp (-1 : ℤ))
    (B : GL (Fin 2) (v.adicCompletion K) → ℂ)
    (χ : (v.adicCompletion K)ˣ →* ℂˣ)
    (h : GL (Fin 2) (v.adicCompletion K)) :
    letI := localBorel K v
    ∀ (ν : Measure (v.adicCompletion K)ˣ) [ν.IsHaarMeasure],
      (∃ T : Finset ℤ, ∀ n : ℤ, n ∉ T →
        ∫ u in {u : (v.adicCompletion K)ˣ | Valued.v (u : v.adicCompletion K) = 1},
          B (diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ ^ n * u) *
            h) * ((χ u : ℂˣ) : ℂ) ∂ν = 0) →
      ∀ σ₀ : ℝ,
        (∀ s : ℂ, σ₀ < s.re →
          Integrable (fun a : (v.adicCompletion K)ˣ =>
            B (diagUnitGL2 a * h) * ((χ a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion K) : ℝ) : ℂ) ^ (s - 1)) ν) →
        ∃ (P : Polynomial ℂ) (m : ℤ), ∀ s : ℂ, σ₀ < s.re →
          ∫ a, B (diagUnitGL2 a * h) * ((χ a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion K) : ℝ) : ℂ) ^ (s - 1) ∂ν =
            (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_exists_polynomial_forall_integral_diagUnitGL2_mul_eq_of_forall_setIntegral_diagUnitGL2_mul_eq_zero.solution
