import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_localZeta_primedDual_eq_pieces_add_setIntegral_annulus_of_forall_eq_zero
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions
attribute [-simp] LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField NumberField.StandardAddChar LanglandsTunnell.TateLocal

theorem LanglandsTunnell.CubicInduction.localZeta_primedDual_eq_pieces_add_setIntegral_annulus_of_forall_eq_zero
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1)
    (F : v.adicCompletion ℚ → ℂ)
    (hF : ∀ a : (v.adicCompletion ℚ)ˣ,
      letI := localBorel ℚ v
      F a =
        (∫ x : v.adicCompletion ℚ,
            jacquetValue v (gl3AmbientRightTranslate (R := ℂ)
              (longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x *
                (weylPrime3 * transposeInv3 1)) * antidiagonal3 v) (cellSectionOf v ν Φ))
          ∂(selfDualHaarAt ℚ v)) *
          ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹)
    (hint :
      letI := localBorel ℚ v
      Integrable (fun x => F x * charExt χ⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (1 - s))
        (mulMeasure (selfDualHaarAt ℚ v)))
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
    (J : v.adicCompletion ℚ → v.adicCompletion ℚ → ℂ)
    (hJ : ∀ (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ),
      J a x =
        jacquetValue v (gl3AmbientRightTranslate (R := ℂ)
          (longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x *
            (weylPrime3 * transposeInv3 1)) * antidiagonal3 v) (cellSectionOf v ν Φ)))
    (G : ℤ → v.adicCompletion ℚ → ℂ)
    (hG : ∀ (c : ℤ) (a : (v.adicCompletion ℚ)ˣ),
      letI := localBorel ℚ v
      G c a =
        (∫ x : v.adicCompletion ℚ, K c a x ∂(selfDualHaarAt ℚ v)) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹)
    (N R : ℕ)
    (hR : ∀ (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ), WithZero.exp (R : ℤ) < Valued.v x →
      J (a : v.adicCompletion ℚ) x = 0)
    (c : ℤ) :
    letI := localBorel ℚ v
    localZeta (selfDualHaarAt ℚ v) (G c) χ⁻¹ (1 - s) =
      (∫ a in {t : v.adicCompletion ℚ | WithZero.exp (-(N : ℤ)) ≤ Valued.v t ∧ Valued.v t ≤ WithZero.exp (N : ℤ)},
          ((modulus a : ℝ) : ℂ)⁻¹ * charExt χ⁻¹ a * ((modulus a : ℝ) : ℂ) ^ (1 - s) *
            ∫ x in {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (R : ℤ)}, (K c a x - J a x)
              ∂(selfDualHaarAt ℚ v)
          ∂(mulMeasure (selfDualHaarAt ℚ v))) +
        (∫ a in {t : v.adicCompletion ℚ | WithZero.exp (-(N : ℤ)) ≤ Valued.v t ∧ Valued.v t ≤ WithZero.exp (N : ℤ)},
            ((modulus a : ℝ) : ℂ)⁻¹ * charExt χ⁻¹ a * ((modulus a : ℝ) : ℂ) ^ (1 - s) *
              ∫ x in {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (R : ℤ)}ᶜ, K c a x ∂(selfDualHaarAt ℚ v)
            ∂(mulMeasure (selfDualHaarAt ℚ v))) +
        (∫ a in {t : v.adicCompletion ℚ |
              WithZero.exp (-(N : ℤ)) ≤ Valued.v t ∧ Valued.v t ≤ WithZero.exp (N : ℤ)}ᶜ,
            ((modulus a : ℝ) : ℂ)⁻¹ * charExt χ⁻¹ a * ((modulus a : ℝ) : ℂ) ^ (1 - s) *
              ∫ x, K c a x ∂(selfDualHaarAt ℚ v) ∂(mulMeasure (selfDualHaarAt ℚ v))) +
        (∫ a in {t : v.adicCompletion ℚ | WithZero.exp (-(N : ℤ)) ≤ Valued.v t ∧ Valued.v t ≤ WithZero.exp (N : ℤ)},
          F a * charExt χ⁻¹ a * ((modulus a : ℝ) : ℂ) ^ (1 - s) ∂(mulMeasure (selfDualHaarAt ℚ v))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_localZeta_primedDual_eq_pieces_add_setIntegral_annulus_of_forall_eq_zero.solution
