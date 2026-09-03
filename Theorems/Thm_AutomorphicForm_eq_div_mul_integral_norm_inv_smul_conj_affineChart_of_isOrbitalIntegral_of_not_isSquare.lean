import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import P2M.Util
import P2M.Sol.S_AutomorphicForm_eq_div_mul_integral_norm_inv_smul_conj_affineChart_of_isOrbitalIntegral_of_not_isSquare
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions
attribute [-simp] LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical

theorem AutomorphicForm.eq_div_mul_integral_norm_inv_smul_conj_affineChart_of_isOrbitalIntegral_of_not_isSquare
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (cG : ENNReal) (hcG : cG ≠ 0) (hcG' : cG ≠ ⊤)
    (hG : ∀ H : GL (Fin 2) (v.adicCompletion K) → ENNReal,
        Measurable[AutomorphicForm.localGLBorel K v] H →
        (letI := AutomorphicForm.localGLBorel K v
         ∫⁻ g, H g ∂(AutomorphicForm.localHaar K v)) =
          cG * ∫⁻ x : Fin 4 → v.adicCompletion K,
            (if h : (!![x 0, x 1; x 2, x 3] : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det ≠ 0 then
                H (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) else 0) *
              ENNReal.ofReal
                ((‖(!![x 0, x 1; x 2, x 3] : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ ^ 2)⁻¹)
            ∂(Measure.pi fun _ : Fin 4 => μ))
    (d : v.adicCompletion K) (hd : ¬ IsSquare d) (p₀ r₀ : v.adicCompletion K) (hr₀ : r₀ ≠ 0)
    (u : GL (Fin 2) (v.adicCompletion K))
    (hu : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![p₀, r₀; d * r₀, p₀])
    (τ : @Measure (AutomorphicForm.localCentralizer K v u) (AutomorphicForm.localCentralizerBorel K v u))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v u) τ)
    (cT : ENNReal) (hcT : cT ≠ 0) (hcT' : cT ≠ ⊤)
    (hT : ∀ H : GL (Fin 2) (v.adicCompletion K) → ENNReal,
        Measurable[AutomorphicForm.localGLBorel K v] H →
        (letI := AutomorphicForm.localCentralizerBorel K v u
         ∫⁻ t, H (t : GL (Fin 2) (v.adicCompletion K)) ∂τ) =
          cT * ∫⁻ q : v.adicCompletion K × v.adicCompletion K,
            (if h : (!![q.1, q.2; d * q.2, q.1] : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det ≠ 0 then
                H (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) else 0) *
              ENNReal.ofReal ‖q.1 ^ 2 - d * q.2 ^ 2‖⁻¹ ∂(μ.prod μ))
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (hfm : Measurable[AutomorphicForm.localGLBorel K v] f)
    (hfs : HasCompactSupport f) (hfb : ∃ C : ℝ, ∀ g, ‖f g‖ ≤ C)
    (I : ℂ) (hI : AutomorphicForm.IsOrbitalIntegral K v u τ f I) :
    Integrable (fun q : v.adicCompletion K × v.adicCompletion K =>
        ‖q.2‖⁻¹ • (if h : (!![1, 0; q.1, q.2] : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det ≠ 0 then
          f ((Matrix.GeneralLinearGroup.mkOfDetNeZero _ h)⁻¹ * u *
            Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) else 0)) (μ.prod μ) ∧
      I = ((cG / cT).toReal : ℂ) *
        ∫ q : v.adicCompletion K × v.adicCompletion K,
          ‖q.2‖⁻¹ • (if h : (!![1, 0; q.1, q.2] : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det ≠ 0 then
            f ((Matrix.GeneralLinearGroup.mkOfDetNeZero _ h)⁻¹ * u *
              Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) else 0) ∂(μ.prod μ) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_eq_div_mul_integral_norm_inv_smul_conj_affineChart_of_isOrbitalIntegral_of_not_isSquare.solution
