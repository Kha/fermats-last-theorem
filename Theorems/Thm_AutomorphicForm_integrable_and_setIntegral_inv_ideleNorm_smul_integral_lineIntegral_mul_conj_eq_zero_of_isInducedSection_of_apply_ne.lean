import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import P2M.Util
import P2M.Sol.S_AutomorphicForm_integrable_and_setIntegral_inv_ideleNorm_smul_integral_lineIntegral_mul_conj_eq_zero_of_isInducedSection_of_apply_ne
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions
attribute [-simp] ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar AutomorphicForm
open IsDedekindDomain
open scoped ComplexConjugate NNReal ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

theorem AutomorphicForm.integrable_and_setIntegral_inv_ideleNorm_smul_integral_lineIntegral_mul_conj_eq_zero_of_isInducedSection_of_apply_ne
    (K : Type) [Field K] [NumberField K] :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (D : Set (AdeleRing (𝓞 K) K)ˣ) (_hDm : MeasurableSet D)
      (_hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K))
      (V : ℝ≥0∞) (_hV0 : V ≠ 0) (_hVT : V ≠ ∞)
      (_hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
        ∫⁻ z in D, f (NumberField.TateGlobal.ideleNorm K z) ∂(NumberField.Idele.idelicHaar K) =
          V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)

      (μP νP : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμPu : IsUnitaryChar (𝓞 K) K μP) (_hνPu : IsUnitaryChar (𝓞 K) K νP)
      (_hμPic : IsIdeleClassChar (𝓞 K) K μP) (_hνPic : IsIdeleClassChar (𝓞 K) K νP)
      (_hμPc : Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((μP x : ℂˣ) : ℂ))
      (f : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hf : ∀ s, IsInducedSection (𝓞 K) K (etaFst μP αm hαm s) (etaSnd νP αm hαm s) (f s))
      (_hfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => f p.1 p.2))
      (_hfhol : ∀ g, Differentiable ℂ (fun s => f s g))
      (_hfdec : ∀ (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖f ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)

      (μ' ν' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ'u : IsUnitaryChar (𝓞 K) K μ') (_hμ'ic : IsIdeleClassChar (𝓞 K) K μ')
      (T : ℝ) (Φ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hΦ : IsInducedSection (𝓞 K) K (etaFst μ' αm hαm ((T : ℂ) * Complex.I)) (etaSnd ν' αm hαm ((T : ℂ) * Complex.I)) Φ)
      (_hΦc : Continuous Φ)
      (z₀ : (AdeleRing (𝓞 K) K)ˣ) (_hz₀ : z₀ ∈ NumberField.TateGlobal.normOneIdeles K) (_hne : μP z₀ ≠ μ' z₀),
    Integrable (fun p : (AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K =>
          (∫ t' : ℝ, f ((t' : ℂ) * Complex.I) (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K))) *
            conj (Φ (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K))))
        ((((NumberField.Idele.idelicHaar K).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 K) K)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹))).prod
          (maximalCompactHaar K)) ∧
    ∫ y in D, (NumberField.TateGlobal.ideleNorm K y)⁻¹ •
          ∫ k, (∫ t' : ℝ, f ((t' : ℂ) * Complex.I) (diagOne y * (k : AdelicGL2 (𝓞 K) K))) *
              conj (Φ (diagOne y * (k : AdelicGL2 (𝓞 K) K))) ∂(maximalCompactHaar K)
        ∂(NumberField.Idele.idelicHaar K) = 0 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_integrable_and_setIntegral_inv_ideleNorm_smul_integral_lineIntegral_mul_conj_eq_zero_of_isInducedSection_of_apply_ne.solution
