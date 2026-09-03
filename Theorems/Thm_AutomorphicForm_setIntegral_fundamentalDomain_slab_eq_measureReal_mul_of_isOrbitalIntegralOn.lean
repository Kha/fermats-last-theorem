import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta
import P2M.Util
import P2M.Sol.S_AutomorphicForm_setIntegral_fundamentalDomain_slab_eq_measureReal_mul_of_isOrbitalIntegralOn
attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions
attribute [-simp] ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply

set_option autoImplicit false

open MeasureTheory NumberField

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

theorem AutomorphicForm.setIntegral_fundamentalDomain_slab_eq_measureReal_mul_of_isOrbitalIntegralOn
    (F : Type) [Field F] [NumberField F]
    (μ : Measure (AutomorphicForm.AdelicGL2 (𝓞 F) F)) [SFinite μ] [μ.IsMulLeftInvariant]
    (γ : GL (Fin 2) F)
    (τ : Measure (Subgroup.centralizer
      ({AutomorphicForm.globalPoints (𝓞 F) F γ} : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F))))
    [SFinite τ] [τ.IsMulRightInvariant]
    (α β : ℝ) (hα : 0 < α)
    (Ψ : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F))
    (hΨ : IsFundamentalDomain
      ((Subgroup.centralizer ({γ} : Set (GL (Fin 2) F))).map (AutomorphicForm.globalPoints (𝓞 F) F))
      Ψ (μ.restrict {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈
        Set.Icc α β}))
    (D : Set (Subgroup.centralizer
      ({AutomorphicForm.globalPoints (𝓞 F) F γ} : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F))))
    (hD : IsFundamentalDomain
      (((Subgroup.centralizer ({γ} : Set (GL (Fin 2) F))).map
        (AutomorphicForm.globalPoints (𝓞 F) F)).subgroupOf
        (Subgroup.centralizer {AutomorphicForm.globalPoints (𝓞 F) F γ})).op D τ)
    (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ) (hfm : Measurable f)
    (I : ℂ) (hI : AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 F) F) μ
      (AutomorphicForm.globalPoints (𝓞 F) F γ) τ f I) :
    ∫ x in Ψ, f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * x)
        ∂(μ.restrict {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈
          Set.Icc α β}) =
      (τ.real (D ∩ {t | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det
        (t : AutomorphicForm.AdelicGL2 (𝓞 F) F)) ∈ Set.Icc α β}) : ℂ) * I := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_setIntegral_fundamentalDomain_slab_eq_measureReal_mul_of_isOrbitalIntegralOn.solution
