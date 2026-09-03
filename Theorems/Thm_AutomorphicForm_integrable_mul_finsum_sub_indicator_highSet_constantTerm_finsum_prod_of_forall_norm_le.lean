import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_AutomorphicForm_integrable_mul_finsum_sub_indicator_highSet_constantTerm_finsum_prod_of_forall_norm_le
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions
attribute [-simp] M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff
attribute [-simp] RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.integrable_mul_finsum_sub_indicator_highSet_constantTerm_finsum_prod_of_forall_norm_le
    (L : Type) [Field L] [NumberField L]
    (θ : AutomorphicForm.AdelicGL2 (𝓞 L) L →* AutomorphicForm.AdelicGL2 (𝓞 L) L) (hθc : Continuous θ)
    (hθ : ∀ g : AutomorphicForm.AdelicGL2 (𝓞 L) L,
      NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det (θ g)) =
        NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g))
    (Φ : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) (hΦμ : adelicGLHaar (Fin 2) (𝓞 L) L Φ < ⊤)
    (hΦm : NullMeasurableSet Φ (adelicGLHaar (Fin 2) (𝓞 L) L))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZ : Measure (AdeleRing (𝓞 L) L)ˣ) [νZ.IsHaarMeasure] (Ω : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩ : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range Ω νZ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (I J : Set (Matrix.GeneralLinearGroup (Fin 2) L)) (T C : ℝ)
    (hbound : ∀ x ∈ Φ, ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      ‖(∑ᶠ γ ∈ I,
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ * θ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
          Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) T)
            (@AutomorphicForm.constantTerm _ (adeleBorel (𝓞 L) L) _ _
              (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
              (fun t => AutomorphicForm.unipotentGL2 t)
              (fun y => ∑ᶠ γ ∈ J, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ * θ y)))
            (AutomorphicForm.centralScalar (𝓞 L) L z * x)‖ ≤ C) :
    Integrable
        (fun p : AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
          ((ξ ⟨p.2, Subgroup.mem_top p.2⟩ : ℂˣ) : ℂ) *
            ((∑ᶠ γ ∈ I,
                φ (p.1⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ *
                  θ (AutomorphicForm.centralScalar (𝓞 L) L p.2 * p.1))) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) T)
                (@AutomorphicForm.constantTerm _ (adeleBorel (𝓞 L) L) _ _
                  (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ γ ∈ J, φ (p.1⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ * θ y)))
                (AutomorphicForm.centralScalar (𝓞 L) L p.2 * p.1)))
        (((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ).prod (νZ.restrict Ω)) ∧
      IntegrableOn
        (fun x : AutomorphicForm.AdelicGL2 (𝓞 L) L =>
          ∫ z in Ω, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            ((∑ᶠ γ ∈ I,
                φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ *
                  θ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) T)
                (@AutomorphicForm.constantTerm _ (adeleBorel (𝓞 L) L) _ _
                  (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ γ ∈ J, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ * θ y)))
                (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZ)
        Φ (adelicGLHaar (Fin 2) (𝓞 L) L) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_integrable_mul_finsum_sub_indicator_highSet_constantTerm_finsum_prod_of_forall_norm_le.solution
