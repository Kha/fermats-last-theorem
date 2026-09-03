import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_HaarQuotient
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_integral_weightedGodementWhittaker2_mul_row_eq_mul_integral_row_mul_row_mul_weightedTorusZeta
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal
  LanglandsTunnell.CubicInduction
open NumberField.AdelicLevel (diagOne)

theorem LanglandsTunnell.RankinSelberg.exists_pos_forall_integral_weightedGodementWhittaker2_mul_row_eq_mul_integral_row_mul_row_mul_weightedTorusZeta
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure]
      (ν : Measure (p.adicCompletion ℚ)) [ν.IsAddHaarMeasure],
    ∃ c : ℝ, 0 < c ∧
      ∀ (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (_hwlc : IsLocallyConstant w)
        (_hwlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
          w (unipotentGL2 x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g)
        (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
        (_hχ : ∀ i, IsLocallyConstant (χ i))
        (Φ₁ : (Fin 2 → p.adicCompletion ℚ) → ℂ) (_hΦ₁ : IsLocallyConstant Φ₁ ∧ HasCompactSupport Φ₁)
        (Φ₂ : (Fin 2 → p.adicCompletion ℚ) → ℂ) (_hΦ₂ : IsLocallyConstant Φ₂)
        (ω : WithZero (Multiplicative ℤ) → WithZero (Multiplicative ℤ) → ℂ)
        (s : ℂ),

        Integrable (fun q : GL (Fin 2) (p.adicCompletion ℚ) × (p.adicCompletion ℚ)ˣ =>
            Φ₁ ((q.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0) * Φ₂ ((q.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1) *
                ((χ 0 (Matrix.GeneralLinearGroup.det q.1) : ℂˣ) : ℂ) *
                ((modulus ((Matrix.GeneralLinearGroup.det q.1 : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2) *
              (ω (Valued.v (q.2 : p.adicCompletion ℚ)) (Valued.v ((Matrix.GeneralLinearGroup.det q.1 : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)) *
                w (diagOne q.2 * q.1) * ((χ 1 q.2 : ℂˣ) : ℂ) * ((modulus (q.2 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)))
          (μ₂.prod (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) →
        Integrable (fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
            (((χ 0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
              ∫ t : (p.adicCompletion ℚ)ˣ,
                ω (Valued.v (t : p.adicCompletion ℚ))⁻¹ (Valued.v (t : p.adicCompletion ℚ) * Valued.v ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)) *
                  (∫ y : p.adicCompletion ℚ, Φ₁ (fun j : Fin 2 => (t : p.adicCompletion ℚ) * (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 j + y * (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j) *
                      NumberField.StandardAddChar.psiLocal ℚ p ((t : p.adicCompletion ℚ)⁻¹ * y) ∂ν) *
                  ((χ 0 t : ℂˣ) : ℂ) * (((χ 1 t : ℂˣ) : ℂ))⁻¹ ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) *
              (w h * Φ₂ ((h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1)) *
              ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s)
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) ∧
        ∫ h, (fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
            (((χ 0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
              ∫ t : (p.adicCompletion ℚ)ˣ,
                ω (Valued.v (t : p.adicCompletion ℚ))⁻¹ (Valued.v (t : p.adicCompletion ℚ) * Valued.v ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)) *
                  (∫ y : p.adicCompletion ℚ, Φ₁ (fun j : Fin 2 => (t : p.adicCompletion ℚ) * (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 j + y * (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j) *
                      NumberField.StandardAddChar.psiLocal ℚ p ((t : p.adicCompletion ℚ)⁻¹ * y) ∂ν) *
                  ((χ 0 t : ℂˣ) : ℂ) * (((χ 1 t : ℂˣ) : ℂ))⁻¹ ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) *
              (w h * Φ₂ ((h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1)) *
              ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s) h
          ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) =
        c *
          ∫ g, Φ₁ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0) * Φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1) * ((χ 0 (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2) *
              (∫ y : (p.adicCompletion ℚ)ˣ,
                ω (Valued.v (y : p.adicCompletion ℚ)) (Valued.v ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)) *
                  w (diagOne y * g) * ((χ 1 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
                ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∂μ₂ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_integral_weightedGodementWhittaker2_mul_row_eq_mul_integral_row_mul_row_mul_weightedTorusZeta.solution
