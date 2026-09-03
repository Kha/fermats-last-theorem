import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AdelicDock_LocalEmbedding
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_setIntegral_translate_transposeTwist_eq_mul_sum_of_forall_setIntegral_translate_eq
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal
  LanglandsTunnell.CubicInduction NumberField.StandardAddChar
open NumberField.AdelicLevel (diagOne)

theorem LanglandsTunnell.RankinSelberg.setIntegral_translate_transposeTwist_eq_mul_sum_of_forall_setIntegral_translate_eq
    (p : HeightOneSpectrum (𝓞 ℚ))
    (Ω : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) (hΩc : IsCompact (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))))
    (hΩt : ∀ ω ∈ Ω, transposeInvN (Fin 2) ω ∈ Ω)
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (ι : Type) [Fintype ι] (wj : ι → GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (c : ι → GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (a d : GL (Fin 2) (p.adicCompletion ℚ)) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
      (∀ g h : GL (Fin 2) (p.adicCompletion ℚ),
        ∫ ω in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (g * ω * h) ∂μ₂ =
          ((μ₂ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ) * ∑ j, c j h * wj j g) →
      ∀ g h : GL (Fin 2) (p.adicCompletion ℚ),
        ∫ ω in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))),
            (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det (d * g) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * w (a * transposeInvN (Fin 2) (d * g))) (g * ω * h) ∂μ₂ =
          ((μ₂ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ) *
            ∑ j, (((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * c j (transposeInvN (Fin 2) h)) *
              (((modulus ((Matrix.GeneralLinearGroup.det (d * g) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * wj j (a * transposeInvN (Fin 2) (d * g))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_translate_transposeTwist_eq_mul_sum_of_forall_setIntegral_translate_eq.solution
