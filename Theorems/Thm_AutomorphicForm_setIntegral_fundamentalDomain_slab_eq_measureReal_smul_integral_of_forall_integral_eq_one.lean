import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_AutomorphicForm_setIntegral_fundamentalDomain_slab_eq_measureReal_smul_integral_of_forall_integral_eq_one
attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions
attribute [-simp] ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply

set_option autoImplicit false

open MeasureTheory NumberField

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.setIntegral_fundamentalDomain_slab_eq_measureReal_smul_integral_of_forall_integral_eq_one
    (F : Type) [Field F] [NumberField F]
    (μ : Measure (AutomorphicForm.AdelicGL2 (𝓞 F) F)) [SFinite μ] [μ.IsMulLeftInvariant]
    (T : Subgroup (AutomorphicForm.AdelicGL2 (𝓞 F) F)) [MeasurableSpace T] [BorelSpace T]
    (τ : Measure T) [SFinite τ] [τ.IsMulRightInvariant]
    (hT : ∀ c : ℝ, 0 < c → ∃ t : T, t ∈ Subgroup.center T ∧
      NumberField.TateGlobal.ideleNorm F
        (Matrix.GeneralLinearGroup.det (t : AutomorphicForm.AdelicGL2 (𝓞 F) F)) = c)
    (Γ : Subgroup (GL (Fin 2) F)) (hΓ : Γ.map (AutomorphicForm.globalPoints (𝓞 F) F) ≤ T)
    (α β : ℝ) (hα : 0 < α)
    (Ψ : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F))
    (hΨ : IsFundamentalDomain (Γ.map (AutomorphicForm.globalPoints (𝓞 F) F)) Ψ
      (μ.restrict {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈
        Set.Icc α β}))
    (D : Set T)
    (hD : IsFundamentalDomain
      ((Γ.map (AutomorphicForm.globalPoints (𝓞 F) F)).subgroupOf T).op D τ)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : AutomorphicForm.AdelicGL2 (𝓞 F) F → E) (hhm : StronglyMeasurable h)
    (hhT : ∀ t ∈ T, ∀ x, h (t * x) = h x)
    (W : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℝ) (hW0 : ∀ x, 0 ≤ W x) (hWm : Measurable W)
    (hW : ∀ x, h x ≠ 0 → ∫ t : T, W ((t : AutomorphicForm.AdelicGL2 (𝓞 F) F) * x) ∂τ = 1) :
    ∫ x in Ψ, h x ∂(μ.restrict {g | NumberField.TateGlobal.ideleNorm F
        (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}) =
      (τ.real (D ∩ {t | NumberField.TateGlobal.ideleNorm F
        (Matrix.GeneralLinearGroup.det (t : AutomorphicForm.AdelicGL2 (𝓞 F) F)) ∈ Set.Icc α β})) •
        ∫ x, W x • h x ∂μ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_setIntegral_fundamentalDomain_slab_eq_measureReal_smul_integral_of_forall_integral_eq_one.solution
