import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_HaarQuotient
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_rsLocalIntegral_finset_sum_translate_eq_sum_mul_rsLocalIntegral_of_le_localLevelOne
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions
attribute [-simp] NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal

theorem LanglandsTunnell.RankinSelberg.rsLocalIntegral_finset_sum_translate_eq_sum_mul_rsLocalIntegral_of_le_localLevelOne
    (p : HeightOneSpectrum (𝓞 ℚ))
    (θ : AddChar (p.adicCompletion ℚ) ℂ)
    (A B : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hA : Continuous A) (hB : Continuous B)
    (hAlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)), A (unipotentGL2 x * g) = θ⁻¹ x * A g)
    (hBlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)), B (unipotentGL2 x * g) = θ x * B g)
    (Kc : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) (hKc : Kc ≤ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤)
    (hBK : ∀ k ∈ Kc, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), B (g * k) = B g)
    {ι : Type} (T : Finset ι) (c : ι → ℝ) (kf : ι → GL (Fin 2) (p.adicCompletion ℚ)) (hkf : ∀ i ∈ T, kf i ∈ Kc) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure] (s : ℂ),
      Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (A g * B g) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
            (s - 1 / 2))
        (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) →
      Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((∑ i ∈ T, (c i : ℂ) * A (g * kf i)) * B g) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
            (s - 1 / 2))
        (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) ∧
      RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ)) s
          (fun g => ∑ i ∈ T, (c i : ℂ) * A (g * kf i)) B =
        ((∑ i ∈ T, c i : ℝ) : ℂ) *
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
            (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ)) s A B := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_rsLocalIntegral_finset_sum_translate_eq_sum_mul_rsLocalIntegral_of_le_localLevelOne.solution
