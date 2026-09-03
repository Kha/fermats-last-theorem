import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_setIntegral_tallBoxJacquet_div_norm_mul_charExt_mul_cpow_eq
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions
attribute [-simp] LanglandsTunnell.CubicInduction.longWeyl3_coe LanglandsTunnell.CubicInduction.lowerUnipotent21_coe LanglandsTunnell.CubicInduction.weylPrime3_coe UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent

set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
open LanglandsTunnell.TateLocal
open LanglandsTunnell.CubicInduction

attribute [local instance] LanglandsTunnell.TateLocal.localBorel in

theorem LanglandsTunnell.CubicInduction.setIntegral_tallBoxJacquet_div_norm_mul_charExt_mul_cpow_eq
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (c c' : ℤ)
    (J : v.adicCompletion ℚ → ℂ)
    (hJ : ∀ a : (v.adicCompletion ℚ)ˣ, J a =
      ∫ p in {p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ |
          Valued.v p.1 ≤ WithZero.exp c ∧ Valued.v p.2.1 ≤ WithZero.exp c ∧ Valued.v p.2.2 ≤ WithZero.exp (2 * c')},
        NumberField.StandardAddChar.psiLocal ℚ v (-(p.1 + p.2.1)) *
          cellSectionOf v ν Φ
            (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2 * (iotaGL (diagUnitGL2 a) * antidiagonal3 v))
        ∂(jacquetHaar3 v))
    (S : Set (v.adicCompletion ℚ)) (hS : MeasurableSet S)
    (hint : ∀ a : (v.adicCompletion ℚ)ˣ, IntegrableOn
      (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
        NumberField.StandardAddChar.psiLocal ℚ v (-(p.1 + p.2.1)) *
          cellSectionOf v ν Φ
            (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2 * (iotaGL (diagUnitGL2 a) * antidiagonal3 v)))
      {p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ |
          Valued.v p.1 ≤ WithZero.exp c ∧ Valued.v p.2.1 ≤ WithZero.exp c ∧ Valued.v p.2.2 ≤ WithZero.exp (2 * c')}
      (jacquetHaar3 v))
    (hIg : Integrable
      (fun t : v.adicCompletion ℚ =>
        (if Valued.v (-t) ≤ WithZero.exp c then (NumberField.StandardAddChar.psiLocal ℚ v (-t) : ℂ) else 0) *
          charExt (ν 2 * χ) t * ((modulus t : ℝ) : ℂ) ^ s)
      (mulMeasure (selfDualHaarAt ℚ v)))
    (hWI : Integrable
      (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ =>
        (charExt (ν 2 * χ)⁻¹ p.2 * ((modulus p.2 : ℝ) : ℂ) ^ (1 - s) * charExt (ν 1 * χ) p.1 *
            ((modulus p.1 : ℝ) : ℂ) ^ s) *
          ∫ w, Φ ![p.2, p.1, w] *
              (charExt (ν 0 * (ν 1)⁻¹) (p.1 - p.2 * w) * ((modulus (p.1 - p.2 * w) : ℝ) : ℂ)⁻¹) *
              (if Valued.v (w / (p.1 - p.2 * w)) ≤ WithZero.exp c then
                (NumberField.StandardAddChar.psiLocal ℚ v (w / (p.1 - p.2 * w)) : ℂ) else 0)
            ∂(selfDualHaarAt ℚ v))
      ((mulMeasure (selfDualHaarAt ℚ v)).prod (mulMeasure (selfDualHaarAt ℚ v)))) :
    ∫ b in S, J b / (‖b‖ : ℂ) * charExt χ b * ((modulus b : ℝ) : ℂ) ^ s ∂(mulMeasure (selfDualHaarAt ℚ v)) =
      charExt (ν 0) (-1) * charExt (ν 1) (-1) *
        ∫ r, ∫ u, (∫ t, S.indicator (fun _ => (1 : ℂ)) (r * u⁻¹ * t) *
              (if Valued.v (u⁻¹ * t) ≤ WithZero.exp (2 * c') then (1 : ℂ) else 0) *
              ((if Valued.v (-t) ≤ WithZero.exp c then (NumberField.StandardAddChar.psiLocal ℚ v (-t) : ℂ) else 0) *
                charExt (ν 2 * χ) t * ((modulus t : ℝ) : ℂ) ^ s) ∂(mulMeasure (selfDualHaarAt ℚ v))) *
            ((charExt (ν 2 * χ)⁻¹ u * ((modulus u : ℝ) : ℂ) ^ (1 - s) * charExt (ν 1 * χ) r *
                ((modulus r : ℝ) : ℂ) ^ s) *
              ∫ w, Φ ![u, r, w] *
                  (charExt (ν 0 * (ν 1)⁻¹) (r - u * w) * ((modulus (r - u * w) : ℝ) : ℂ)⁻¹) *
                  (if Valued.v (w / (r - u * w)) ≤ WithZero.exp c then
                    (NumberField.StandardAddChar.psiLocal ℚ v (w / (r - u * w)) : ℂ) else 0)
                ∂(selfDualHaarAt ℚ v))
          ∂(mulMeasure (selfDualHaarAt ℚ v)) ∂(mulMeasure (selfDualHaarAt ℚ v)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_setIntegral_tallBoxJacquet_div_norm_mul_charExt_mul_cpow_eq.solution
