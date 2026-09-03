import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_rsGlobalIntegral_eq_mul_integral_unipotentQuotient_whittakerCoefficient_mul_of_hasSum_mirabolicTranslate_and_dual
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions
attribute [-simp] ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm
open LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.RankinSelberg.exists_ne_zero_forall_rsGlobalIntegral_eq_mul_integral_unipotentQuotient_whittakerCoefficient_mul_of_hasSum_mirabolicTranslate_and_dual
    (Dp : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ) :
    ∃ c : ℂ, c ≠ 0 ∧
      (∀ (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
        (Θ W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
        (_hΘc : Continuous Θ) (_hWc : Continuous W) (_hWg : IsGaugeMajorised3 ℚ W)
        (_hWlaw : IsGL3PsiWhittakerFn ψ W)
        (_hWexp : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, HasSum (fun i : MirabolicIndex ℚ => W (mirabolicTranslate i * g)) (Θ g))
        (_hWhp : HasWhittakerHalfPlane W)
        (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (_hφc : Continuous φ)
        (_hφ : ∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (globalPoints (𝓞 ℚ) ℚ γ * g) = φ g)
        (_hφb : ∃ C : ℝ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ‖φ g‖ * detNorm g ^ (-(1 / 2 : ℝ)) ≤ C)
        (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
        (_hD : IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D
          (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ))
        (σq : UnipotentQuotient ℚ → AdelicGL2 (𝓞 ℚ) ℚ)
        (_hσq : ∀ q, (Quotient.mk'' (σq q) : UnipotentQuotient ℚ) = q),
        ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
          rsGlobalIntegral D s φ Θ =
            c * ∫ q, (fun g : AdelicGL2 (𝓞 ℚ) ℚ =>
                  whittakerCoefficient ℚ (productionPinsOf ℚ Dp U gen (AdelicBox.adelicBox ℚ)) ψ⁻¹ φ 1 g *
                    W (iota (𝓞 ℚ) ℚ g) * ((detNorm g : ℝ) : ℂ) ^ (s - 1 / 2)) (σq q)
              ∂(unipotentQuotientMeasure ℚ)) ∧
      (∀ (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
        (Θ W' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
        (_hΘc : Continuous Θ) (_hW'c : Continuous W') (_hW'g : IsGaugeMajorised3 ℚ W')
        (_hW'law : IsGL3PsiWhittakerFn ψ⁻¹ W')
        (_hW'exp : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, HasSum (fun i : MirabolicIndex ℚ => W' (mirabolicTranslate i * g)) (dualForm Θ g))
        (_hW'hp : HasWhittakerHalfPlane W')
        (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (_hφc : Continuous φ)
        (_hφ : ∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (globalPoints (𝓞 ℚ) ℚ γ * g) = φ g)
        (_hφb : ∃ C : ℝ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ‖φ g‖ * detNorm g ^ (-(1 / 2 : ℝ)) ≤ C)
        (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
        (_hD : IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D
          (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ))
        (σq : UnipotentQuotient ℚ → AdelicGL2 (𝓞 ℚ) ℚ)
        (_hσq : ∀ q, (Quotient.mk'' (σq q) : UnipotentQuotient ℚ) = q),
        ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
          rsGlobalIntegral D s φ (dualForm Θ) =
            c * ∫ q, (fun g : AdelicGL2 (𝓞 ℚ) ℚ =>
                  whittakerCoefficient ℚ (productionPinsOf ℚ Dp U gen (AdelicBox.adelicBox ℚ)) ψ φ 1 g *
                    W' (iota (𝓞 ℚ) ℚ g) * ((detNorm g : ℝ) : ℂ) ^ (s - 1 / 2)) (σq q)
              ∂(unipotentQuotientMeasure ℚ)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_rsGlobalIntegral_eq_mul_integral_unipotentQuotient_whittakerCoefficient_mul_of_hasSum_mirabolicTranslate_and_dual.solution
