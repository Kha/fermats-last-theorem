import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_SigmaCentralizer
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta
import P2M.Util
import P2M.Sol.S_AutomorphicForm_setIntegral_fundamentalDomain_slab_sigmaCentralizer_eq_measureReal_mul_integral_of_forall_exists_mem_center
attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions
attribute [-simp] ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply

set_option autoImplicit false

open MeasureTheory NumberField

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.setIntegral_fundamentalDomain_slab_sigmaCentralizer_eq_measureReal_mul_integral_of_forall_exists_mem_center
    (L : Type) [Field L] [NumberField L]
    (μ : Measure (AutomorphicForm.AdelicGL2 (𝓞 L) L)) [SFinite μ] [μ.IsMulLeftInvariant]
    (σ : L →+* L) (σA : AutomorphicForm.AdelicGL2 (𝓞 L) L →* AutomorphicForm.AdelicGL2 (𝓞 L) L)
    (hσA : ∀ γ : GL (Fin 2) L, σA (AutomorphicForm.globalPoints (𝓞 L) L γ) =
      AutomorphicForm.globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.map σ γ))
    (hσAc : Continuous σA)
    (δ₀ : GL (Fin 2) L)
    [MeasurableSpace (AutomorphicForm.sigmaCentralizer σA (AutomorphicForm.globalPoints (𝓞 L) L δ₀))]
    [BorelSpace (AutomorphicForm.sigmaCentralizer σA (AutomorphicForm.globalPoints (𝓞 L) L δ₀))]
    (τ' : Measure (AutomorphicForm.sigmaCentralizer σA (AutomorphicForm.globalPoints (𝓞 L) L δ₀)))
    [SFinite τ'] [τ'.IsMulRightInvariant]
    (hT' : ∀ c : ℝ, 0 < c →
      ∃ t : AutomorphicForm.sigmaCentralizer σA (AutomorphicForm.globalPoints (𝓞 L) L δ₀),
        t ∈ Subgroup.center
            (AutomorphicForm.sigmaCentralizer σA (AutomorphicForm.globalPoints (𝓞 L) L δ₀)) ∧
          NumberField.TateGlobal.ideleNorm L
            (Matrix.GeneralLinearGroup.det (t : AutomorphicForm.AdelicGL2 (𝓞 L) L)) = c)
    (α β : ℝ) (hα : 0 < α)
    (Ψ : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L))
    (hΨ : IsFundamentalDomain
      ((AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map σ) δ₀).map
        (AutomorphicForm.globalPoints (𝓞 L) L)) Ψ
      (μ.restrict {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (D' : Set (AutomorphicForm.sigmaCentralizer σA (AutomorphicForm.globalPoints (𝓞 L) L δ₀)))
    (hD' : IsFundamentalDomain
      (((AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map σ) δ₀).map
        (AutomorphicForm.globalPoints (𝓞 L) L)).subgroupOf
        (AutomorphicForm.sigmaCentralizer σA (AutomorphicForm.globalPoints (𝓞 L) L δ₀))).op D' τ')
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφm : Measurable φ)
    (w : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℝ) (hw0 : ∀ x, 0 ≤ w x) (hwm : Measurable w)
    (hwc : HasCompactSupport w)
    (hw1 : ∀ x, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * σA x) ≠ 0 →
      ∫ t : AutomorphicForm.sigmaCentralizer σA (AutomorphicForm.globalPoints (𝓞 L) L δ₀),
        w ((t : AutomorphicForm.AdelicGL2 (𝓞 L) L) * x) ∂τ' = 1) :
    ∫ x in Ψ, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * σA x)
        ∂(μ.restrict {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈
          Set.Icc α β}) =
      (τ'.real (D' ∩ {t | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det
        (t : AutomorphicForm.AdelicGL2 (𝓞 L) L)) ∈ Set.Icc α β}) : ℂ) *
        ∫ x, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * σA x) * (w x : ℂ) ∂μ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_setIntegral_fundamentalDomain_slab_sigmaCentralizer_eq_measureReal_mul_integral_of_forall_exists_mem_center.solution
