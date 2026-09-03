import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_forall_setLIntegral_tsum_borelSubgroup_cosets_eq_mul_lintegral_iwasawa
attribute [-instance] M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra
attribute [-simp] ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi
attribute [-simp] LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul LocalGL2.swapUnit_val

set_option autoImplicit false

open MeasureTheory NumberField open NumberField.AdelicHaar hiding exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa open NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

theorem AutomorphicForm.exists_forall_setLIntegral_tsum_borelSubgroup_cosets_eq_mul_lintegral_iwasawa
    (K : Type) [Field K] [NumberField K] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
    (∀ (S₀ : Set (AdelicGL2 (𝓞 K) K)), MeasurableSet S₀ →
        (∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), globalPoints (𝓞 K) K γ * g ∈ S₀ ↔ g ∈ S₀) →
      ∀ (Φ₀ : Set (AdelicGL2 (𝓞 K) K)), Φ₀ ⊆ S₀ →
        IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀ ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict S₀) →
      ∀ (reps : Set (GL (Fin 2) K)),
        (∀ g : GL (Fin 2) K, ∃! ρ : GL (Fin 2) K, ρ ∈ reps ∧ g * ρ⁻¹ ∈ borelSubgroup K) →
      ∀ (X : Set (AdeleRing (𝓞 K) K)) (Ω₁ Ω₂ : Set (AdeleRing (𝓞 K) K)ˣ),
        IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 K) K) X (adelicAddHaar (𝓞 K) K) →
        IsFundamentalDomain (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range Ω₁
          (NumberField.Idele.idelicHaar K) →
        IsFundamentalDomain (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range Ω₂
          (NumberField.Idele.idelicHaar K) →
      ∀ F : AdelicGL2 (𝓞 K) K → ℝ≥0∞, Measurable F →
        (∀ β ∈ borelSubgroup K, ∀ g : AdelicGL2 (𝓞 K) K, F (globalPoints (𝓞 K) K β * g) = F g) →
        ∫⁻ x in Φ₀, ∑' ρ : reps, F (globalPoints (𝓞 K) K (ρ : GL (Fin 2) K) * x) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
          c * ∫⁻ x in X, ∫⁻ u in Ω₁, ∫⁻ t in Ω₂, ∫⁻ k,
                S₀.indicator F (unipotentGL2 x * centralScalar (𝓞 K) K u * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
              ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K)
            ∂(adelicAddHaar (𝓞 K) K)) ∧
    (∀ (S₀ : Set (AdelicGL2 (𝓞 K) K)), MeasurableSet S₀ →
        (∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), globalPoints (𝓞 K) K γ * g ∈ S₀ ↔ g ∈ S₀) →
      ∀ (Φ₀ : Set (AdelicGL2 (𝓞 K) K)), Φ₀ ⊆ S₀ →
        IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀ ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict S₀) →
      ∀ (reps : Set (GL (Fin 2) K)),
        (∀ g : GL (Fin 2) K, ∃! ρ : GL (Fin 2) K, ρ ∈ reps ∧ g * ρ⁻¹ ∈ borelSubgroup K) →
      ∀ (X : Set (AdeleRing (𝓞 K) K)) (Ω₁ Ω₂ : Set (AdeleRing (𝓞 K) K)ˣ),
        IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 K) K) X (adelicAddHaar (𝓞 K) K) →
        IsFundamentalDomain (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range Ω₁
          (NumberField.Idele.idelicHaar K) →
        IsFundamentalDomain (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range Ω₂
          (NumberField.Idele.idelicHaar K) →
      ∀ F : AdelicGL2 (𝓞 K) K → ℂ, Measurable F →
        (∀ β ∈ borelSubgroup K, ∀ g : AdelicGL2 (𝓞 K) K, F (globalPoints (𝓞 K) K β * g) = F g) →
        (∫⁻ x in Φ₀, ∑' ρ : reps, ‖F (globalPoints (𝓞 K) K (ρ : GL (Fin 2) K) * x)‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
          ≠ ∞) →
        ∫ x in Φ₀, ∑' ρ : reps, F (globalPoints (𝓞 K) K (ρ : GL (Fin 2) K) * x) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
          (c.toReal : ℂ) * ∫ x in X, ∫ u in Ω₁, ∫ t in Ω₂, ∫ k,
                S₀.indicator F (unipotentGL2 x * centralScalar (𝓞 K) K u * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
                  (((NumberField.TateGlobal.ideleNorm K t)⁻¹ : ℝ) : ℂ)
              ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K)
            ∂(adelicAddHaar (𝓞 K) K)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_forall_setLIntegral_tsum_borelSubgroup_cosets_eq_mul_lintegral_iwasawa.solution
