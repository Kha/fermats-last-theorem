import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import P2M.Util
import P2M.Sol.S_AutomorphicForm_integrableOn_and_setIntegral_rationalTorusUnipotentQuotient_slab_mul_conj_eq_mul_setIntegral_inv_ideleNorm_smul_integral_maximalCompact
attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions
attribute [-simp] AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.gl2Weyl_val AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.cpowChar_apply_val ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply
attribute [-simp] LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open IsDedekindDomain NumberField.TateGlobal
open scoped NNReal ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

theorem AutomorphicForm.integrableOn_and_setIntegral_rationalTorusUnipotentQuotient_slab_mul_conj_eq_mul_setIntegral_inv_ideleNorm_smul_integral_maximalCompact
    (F : Type) [Field F] [NumberField F] :
    ∀
      (c : ℝ≥0∞) (hc_top : c ≠ ∞)
      (hc : ∀ (D D' : Set (AdeleRing (𝓞 F) F)ˣ), MeasurableSet D → MeasurableSet D' →
          IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F) →
          IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D' (NumberField.Idele.idelicHaar F) →
        ∀ f : AdelicGL2 (𝓞 F) F → ℝ≥0∞, Measurable f →
          (∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, f (x * g) = f g) →
          ∫⁻ q, f q.out ∂(rationalTorusUnipotentQuotientMeasure F) =
            c * ∫⁻ z in D, ∫⁻ t in D', ∫⁻ k,
                  f (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
                    ENNReal.ofReal ((ideleNorm F t)⁻¹)
                ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F))
      (D : Set (AdeleRing (𝓞 F) F)ˣ) (_hDm : MeasurableSet D)
      (_hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
      (V : ℝ≥0∞) (_hV0 : V ≠ 0) (_hVT : V ≠ ∞)
      (_hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
        ∫⁻ z in D, f (NumberField.TateGlobal.ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
          V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
      (d₁ d₂ : ℝ) (_hd₁ : 0 < d₁) (_hd : d₁ ≤ d₂)
      (Φ₁ Φ₂ : AdelicGL2 (𝓞 F) F → ℂ) (_hΦ₁m : Measurable Φ₁) (_hΦ₂m : Measurable Φ₂)
      (_hΦ₁inv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, Φ₁ (x * g) = Φ₁ g)
      (_hΦ₂inv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, Φ₂ (x * g) = Φ₂ g)
      (_hcen : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F),
        Φ₁ (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
            starRingEnd ℂ (Φ₂ (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F))) =
          Φ₁ (diagOne t * (k : AdelicGL2 (𝓞 F) F)) * starRingEnd ℂ (Φ₂ (diagOne t * (k : AdelicGL2 (𝓞 F) F))))
      (_hint : Integrable
        (fun p : (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F =>
          Φ₁ (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F)) * starRingEnd ℂ (Φ₂ (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F))))
        ((((NumberField.Idele.idelicHaar F).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 F) F)ˣ => ENNReal.ofReal ((ideleNorm F t)⁻¹))).prod
          (maximalCompactHaar F))),
    IntegrableOn (fun q : RationalTorusUnipotentQuotient F => Φ₁ q.out * starRingEnd ℂ (Φ₂ q.out))
        {q : RationalTorusUnipotentQuotient F |
          ideleNorm F (Matrix.GeneralLinearGroup.det q.out) ∈ Set.Icc d₁ d₂}
        (rationalTorusUnipotentQuotientMeasure F) ∧
    ∫ q in {q : RationalTorusUnipotentQuotient F |
        ideleNorm F (Matrix.GeneralLinearGroup.det q.out) ∈ Set.Icc d₁ d₂},
        Φ₁ q.out * starRingEnd ℂ (Φ₂ q.out) ∂(rationalTorusUnipotentQuotientMeasure F) =
      ((c.toReal * (V.toReal * (Real.log (d₂ / d₁) / 2)) : ℝ) : ℂ) *
        ∫ t in D, (ideleNorm F t)⁻¹ •
          ∫ k, Φ₁ (diagOne t * (k : AdelicGL2 (𝓞 F) F)) * starRingEnd ℂ (Φ₂ (diagOne t * (k : AdelicGL2 (𝓞 F) F)))
            ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_integrableOn_and_setIntegral_rationalTorusUnipotentQuotient_slab_mul_conj_eq_mul_setIntegral_inv_ideleNorm_smul_integral_maximalCompact.solution
