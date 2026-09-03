import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_TateLocal_integrable_and_hasSum_setIntegral_shell_of_isLocallyConstant_of_norm_le
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions
attribute [-simp] NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicLevel LanglandsTunnell.TateLocal

theorem LanglandsTunnell.TateLocal.integrable_and_hasSum_setIntegral_shell_of_isLocallyConstant_of_norm_le
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (φ : (v.adicCompletion K)ˣ → ℂ) (hφ : IsLocallyConstant φ)
    (C : ℝ) (M : ℕ)
    (hC : ∀ y : (v.adicCompletion K)ˣ, ‖φ y‖ ≤ C * max 1 ((modulus (y : v.adicCompletion K)) ^ M)⁻¹)
    (c₀ : ℝ) (hc₀ : ∀ y : (v.adicCompletion K)ˣ, c₀ < modulus (y : v.adicCompletion K) → φ y = 0)
    (ν : (v.adicCompletion K)ˣ →* ℂˣ) (hν : IsLocallyConstant fun y : (v.adicCompletion K)ˣ => ((ν y : ℂˣ) : ℂ))
    (B : ℝ) (hB : ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 → ‖((ν u : ℂˣ) : ℂ)‖ ≤ B)
    (hνϖ : ‖((ν (uniformizerUnit K v) : ℂˣ) : ℂ)‖ = 1)
    (z : ℂ) (hz : (M : ℝ) < z.re) :
    Integrable (fun y : (v.adicCompletion K)ˣ =>
        φ y * ((ν y : ℂˣ) : ℂ) * ((modulus (y : v.adicCompletion K) : ℝ) : ℂ) ^ z)
      (Measure.comap Units.val (mulMeasure μ)) ∧
    (∀ n : ℤ, IntegrableOn
      (fun u : (v.adicCompletion K)ˣ => φ (uniformizerUnit K v ^ n * u) * ((ν u : ℂˣ) : ℂ))
      {u : (v.adicCompletion K)ˣ | Valued.v (u : v.adicCompletion K) = 1}
      (Measure.comap Units.val (mulMeasure μ))) ∧
    HasSum (fun n : ℤ =>
        (Ideal.absNorm v.asIdeal : ℂ) ^ (-((n : ℂ) * z)) * ((ν (uniformizerUnit K v) : ℂˣ) : ℂ) ^ n *
          ∫ u in {u : (v.adicCompletion K)ˣ | Valued.v (u : v.adicCompletion K) = 1},
            φ (uniformizerUnit K v ^ n * u) * ((ν u : ℂˣ) : ℂ) ∂(Measure.comap Units.val (mulMeasure μ)))
      (∫ y, φ y * ((ν y : ℂˣ) : ℂ) * ((modulus (y : v.adicCompletion K) : ℝ) : ℂ) ^ z
        ∂(Measure.comap Units.val (mulMeasure μ))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_integrable_and_hasSum_setIntegral_shell_of_isLocallyConstant_of_norm_le.solution
