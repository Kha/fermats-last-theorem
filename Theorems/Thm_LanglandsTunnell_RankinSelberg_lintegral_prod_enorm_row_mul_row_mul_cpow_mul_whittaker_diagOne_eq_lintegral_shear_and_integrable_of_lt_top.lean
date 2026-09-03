import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_HaarQuotient
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_lintegral_prod_enorm_row_mul_row_mul_cpow_mul_whittaker_diagOne_eq_lintegral_shear_and_integrable_of_lt_top
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal
  LanglandsTunnell.CubicInduction
open NumberField.AdelicLevel (diagOne)
open scoped ENNReal

theorem LanglandsTunnell.RankinSelberg.lintegral_prod_enorm_row_mul_row_mul_cpow_mul_whittaker_diagOne_eq_lintegral_shear_and_integrable_of_lt_top
    (p : HeightOneSpectrum (𝓞 ℚ))
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hw : IsLocallyConstant w)
    (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hχ : ∀ i, IsLocallyConstant (χ i))
    (Φ₁ : (Fin 2 → p.adicCompletion ℚ) → ℂ) (hΦ₁ : IsLocallyConstant Φ₁)
    (Φ₂ : (Fin 2 → p.adicCompletion ℚ) → ℂ) (hΦ₂ : IsLocallyConstant Φ₂)
    (s : ℂ) :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
      (∫⁻ q : GL (Fin 2) (p.adicCompletion ℚ) × (p.adicCompletion ℚ)ˣ,
          ‖Φ₁ ((q.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0) * Φ₂ ((q.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1) *
                ((χ 0 (Matrix.GeneralLinearGroup.det q.1) : ℂˣ) : ℂ) *
                ((modulus ((Matrix.GeneralLinearGroup.det q.1 : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2) *
              (w (diagOne q.2 * q.1) * ((χ 1 q.2 : ℂˣ) : ℂ) * ((modulus (q.2 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))‖ₑ
          ∂(μ₂.prod (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))))
        = ∫⁻ h : GL (Fin 2) (p.adicCompletion ℚ),
            ‖w h‖ₑ * ‖Φ₂ ((h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1)‖ₑ *
              ‖((χ 0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ)‖ₑ *
              ENNReal.ofReal (((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ)) ^ (s.re + 1 / 2)) *
            ∫⁻ t : (p.adicCompletion ℚ)ˣ,
              ‖Φ₁ (fun j : Fin 2 => (t : p.adicCompletion ℚ) * (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 j)‖ₑ *
                ‖((χ 0 t : ℂˣ) : ℂ)‖ₑ * ‖(((χ 1 t : ℂˣ) : ℂ))⁻¹‖ₑ *
                ENNReal.ofReal ((modulus (t : p.adicCompletion ℚ) : ℝ))
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∂μ₂) ∧
      ((∫⁻ h : GL (Fin 2) (p.adicCompletion ℚ),
            ‖w h‖ₑ * ‖Φ₂ ((h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1)‖ₑ *
              ‖((χ 0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ)‖ₑ *
              ENNReal.ofReal (((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ)) ^ (s.re + 1 / 2)) *
            ∫⁻ t : (p.adicCompletion ℚ)ˣ,
              ‖Φ₁ (fun j : Fin 2 => (t : p.adicCompletion ℚ) * (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 j)‖ₑ *
                ‖((χ 0 t : ℂˣ) : ℂ)‖ₑ * ‖(((χ 1 t : ℂˣ) : ℂ))⁻¹‖ₑ *
                ENNReal.ofReal ((modulus (t : p.adicCompletion ℚ) : ℝ))
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∂μ₂) < ⊤ →
        Integrable (fun q : GL (Fin 2) (p.adicCompletion ℚ) × (p.adicCompletion ℚ)ˣ =>
            Φ₁ ((q.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0) * Φ₂ ((q.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1) *
                ((χ 0 (Matrix.GeneralLinearGroup.det q.1) : ℂˣ) : ℂ) *
                ((modulus ((Matrix.GeneralLinearGroup.det q.1 : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2) *
              (w (diagOne q.2 * q.1) * ((χ 1 q.2 : ℂˣ) : ℂ) * ((modulus (q.2 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)))
          (μ₂.prod (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_lintegral_prod_enorm_row_mul_row_mul_cpow_mul_whittaker_diagOne_eq_lintegral_shear_and_integrable_of_lt_top.solution
