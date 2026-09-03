import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField NumberField.StandardAddChar LanglandsTunnell.TateLocal

theorem LanglandsTunnell.CubicInduction.integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1)
    (K : ℤ → v.adicCompletion ℚ → v.adicCompletion ℚ → ℂ)
    (hK : ∀ (c : ℤ) (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ),
      letI := localBorel ℚ v
      K c a x =
        ∫ p in {p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ |
            Valued.v p.2.1 ≤ WithZero.exp c ∧ Valued.v p.2.2 ≤ WithZero.exp c * Valued.v p.2.1 ∧
              Valued.v (p.1 - p.2.2 / p.2.1) ≤ WithZero.exp c},
          (psiLocal ℚ v (-(p.1 + p.2.1)) : ℂ) *
            cellSectionOf v ν Φ
              (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2 *
                (longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x *
                  (weylPrime3 * transposeInv3 1)) * antidiagonal3 v))
          ∂(jacquetHaar3 v))
    (c : ℤ) (ω : v.adicCompletion ℚ → v.adicCompletion ℚ → ℂ)
    (hω :
      letI := localBorel ℚ v
      Measurable (Function.uncurry ω))
    (B : ℝ) (hB : ∀ a x, ‖ω a x‖ ≤ B) :
    letI := localBorel ℚ v
    Integrable
        (fun y : (v.adicCompletion ℚ × v.adicCompletion ℚ) × v.adicCompletion ℚ × v.adicCompletion ℚ ×
            v.adicCompletion ℚ =>
          (if Valued.v (-y.1.1) ≤ WithZero.exp c then (psiLocal ℚ v (-y.1.1) : ℂ) else 0) *
                  charExt (ν 0 * χ)⁻¹ y.1.1 * ((modulus y.1.1 : ℝ) : ℂ) ^ (1 - s) *
                ((if Valued.v (-y.1.2) ≤ WithZero.exp c then (psiLocal ℚ v (-y.1.2) : ℂ) else 0) *
                  charExt (ν 1 * χ)⁻¹ y.1.2 * ((modulus y.1.2 : ℝ) : ℂ) ^ (1 - s)) *
              (Φ ![y.2.1, y.2.2.1, y.2.2.2] *
                  (charExt (ν 2 * χ)⁻¹ y.2.1 * ((modulus y.2.1 : ℝ) : ℂ) ^ (1 - s)) *
                  (charExt (ν 1 * χ) y.2.2.1 * ((modulus y.2.2.1 : ℝ) : ℂ) ^ s) *
                  (charExt (ν 0 * (ν 1)⁻¹) (y.2.2.1 - y.2.1 * y.2.2.2) *
                    ((modulus (y.2.2.1 - y.2.1 * y.2.2.2) : ℝ) : ℂ)⁻¹) *
                  (if Valued.v (y.2.2.2 / (y.2.2.1 - y.2.1 * y.2.2.2)) ≤ WithZero.exp c then
                    (psiLocal ℚ v (y.2.2.2 / (y.2.2.1 - y.2.1 * y.2.2.2)) : ℂ)
                  else 0)) *
            ω (y.1.1 * (y.1.2 * y.2.1 / y.2.2.1)) (y.1.2 * y.2.1 / y.2.2.1 - (y.2.2.1 - y.2.1 * y.2.2.2)⁻¹))
        ((((mulMeasure (selfDualHaarAt ℚ v)).prod (mulMeasure (selfDualHaarAt ℚ v))).prod
          ((mulMeasure (selfDualHaarAt ℚ v)).prod ((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v))))) ∧
      Integrable
          (fun q : v.adicCompletion ℚ × v.adicCompletion ℚ =>
            ω q.1 q.2 *
              (((modulus q.1 : ℝ) : ℂ)⁻¹ * charExt χ⁻¹ q.1 * ((modulus q.1 : ℝ) : ℂ) ^ (1 - s) * K c q.1 q.2))
          ((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v)) ∧
        ∫ q : v.adicCompletion ℚ × v.adicCompletion ℚ,
            ω q.1 q.2 *
              (((modulus q.1 : ℝ) : ℂ)⁻¹ * charExt χ⁻¹ q.1 * ((modulus q.1 : ℝ) : ℂ) ^ (1 - s) * K c q.1 q.2)
            ∂((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v)) =
          ∫ y : (v.adicCompletion ℚ × v.adicCompletion ℚ) × v.adicCompletion ℚ × v.adicCompletion ℚ ×
              v.adicCompletion ℚ,
            (if Valued.v (-y.1.1) ≤ WithZero.exp c then (psiLocal ℚ v (-y.1.1) : ℂ) else 0) *
                    charExt (ν 0 * χ)⁻¹ y.1.1 * ((modulus y.1.1 : ℝ) : ℂ) ^ (1 - s) *
                  ((if Valued.v (-y.1.2) ≤ WithZero.exp c then (psiLocal ℚ v (-y.1.2) : ℂ) else 0) *
                    charExt (ν 1 * χ)⁻¹ y.1.2 * ((modulus y.1.2 : ℝ) : ℂ) ^ (1 - s)) *
                (Φ ![y.2.1, y.2.2.1, y.2.2.2] *
                    (charExt (ν 2 * χ)⁻¹ y.2.1 * ((modulus y.2.1 : ℝ) : ℂ) ^ (1 - s)) *
                    (charExt (ν 1 * χ) y.2.2.1 * ((modulus y.2.2.1 : ℝ) : ℂ) ^ s) *
                    (charExt (ν 0 * (ν 1)⁻¹) (y.2.2.1 - y.2.1 * y.2.2.2) *
                      ((modulus (y.2.2.1 - y.2.1 * y.2.2.2) : ℝ) : ℂ)⁻¹) *
                    (if Valued.v (y.2.2.2 / (y.2.2.1 - y.2.1 * y.2.2.2)) ≤ WithZero.exp c then
                      (psiLocal ℚ v (y.2.2.2 / (y.2.2.1 - y.2.1 * y.2.2.2)) : ℂ)
                    else 0)) *
              ω (y.1.1 * (y.1.2 * y.2.1 / y.2.2.1)) (y.1.2 * y.2.1 / y.2.2.1 - (y.2.2.1 - y.2.1 * y.2.2.2)⁻¹)
            ∂((((mulMeasure (selfDualHaarAt ℚ v)).prod (mulMeasure (selfDualHaarAt ℚ v))).prod
              ((mulMeasure (selfDualHaarAt ℚ v)).prod
                ((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v))))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.solution
