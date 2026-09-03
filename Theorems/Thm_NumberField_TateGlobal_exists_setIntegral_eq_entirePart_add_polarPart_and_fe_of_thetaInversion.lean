import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_AutomorphicForm_AdelicLsXi
import P2M.Util
import P2M.Sol.S_NumberField_TateGlobal_exists_setIntegral_eq_entirePart_add_polarPart_and_fe_of_thetaInversion
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions
attribute [-simp] M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq AutomorphicForm.rightTranslationEmbed_smul_apply AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply
attribute [-simp] Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply

set_option autoImplicit false

open MeasureTheory NumberField

theorem NumberField.TateGlobal.exists_setIntegral_eq_entirePart_add_polarPart_and_fe_of_thetaInversion
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Set (AdeleRing (𝓞 F) F)ˣ),
        IsFundamentalDomain
          (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω ν →
      ∀ (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ), AutomorphicForm.IsIdeleClassChar (𝓞 F) F χ →
        AutomorphicForm.IsUnitaryChar (𝓞 F) F χ →
        Continuous (fun x : (AdeleRing (𝓞 F) F)ˣ => ((χ x : ℂˣ) : ℂ)) →
      ∀ (θ θ' : (AdeleRing (𝓞 F) F)ˣ → ℂ),
        (∀ (u : Fˣ) (t : (AdeleRing (𝓞 F) F)ˣ),
          θ' (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u * t) = θ' t) →
      ∀ (a b : ℂ) (d : ℝ), 0 < d →
        (∀ t : (AdeleRing (𝓞 F) F)ˣ,
          θ t + a = ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ (-(d : ℂ)) * (θ' t⁻¹ + b)) →
        (∀ σ : ℝ, IntegrableOn
          (fun t => θ t * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ (σ : ℂ))
          (Ω ∩ {t | 1 ≤ NumberField.TateGlobal.ideleNorm F t}) ν) →
        (∀ σ : ℝ, IntegrableOn
          (fun t => θ' t * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ (σ : ℂ))
          (Ω ∩ {t | 1 ≤ NumberField.TateGlobal.ideleNorm F t}) ν) →
        ∃ R R' : ℂ → ℂ,
          (∀ s : ℂ, R s =
            ∫ t in Ω ∩ {t | 1 ≤ NumberField.TateGlobal.ideleNorm F t},
                θ t * ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν
              + ∫ t in Ω ∩ {t | 1 ≤ NumberField.TateGlobal.ideleNorm F t},
                θ' t * ((χ t : ℂˣ) : ℂ)⁻¹ * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ ((d : ℂ) - s) ∂ν) ∧
          (∀ s : ℂ, R' s =
            ∫ t in Ω ∩ {t | 1 ≤ NumberField.TateGlobal.ideleNorm F t},
                θ' t * ((χ t : ℂˣ) : ℂ)⁻¹ * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν
              + ∫ t in Ω ∩ {t | 1 ≤ NumberField.TateGlobal.ideleNorm F t},
                θ t * ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ ((d : ℂ) - s) ∂ν) ∧
          (∀ s : ℂ, R s = R' ((d : ℂ) - s)) ∧
          ((∀ τ : ℝ, χ ≠ NumberField.TateGlobal.normPowChar F τ) →
            (∀ s : ℂ, d < s.re →
              ∫ t in Ω, θ t * ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν = R s) ∧
            (∀ s : ℂ, d < s.re →
              ∫ t in Ω, θ' t * ((χ t : ℂˣ) : ℂ)⁻¹ * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν = R' s)) ∧
          (∀ τ : ℝ, χ = NumberField.TateGlobal.normPowChar F τ →
            (∀ s : ℂ, d < s.re →
              ∫ t in Ω, θ t * ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν =
                R s + C * b / (s - d + (τ : ℂ) * Complex.I) - C * a / (s + (τ : ℂ) * Complex.I)) ∧
            (∀ s : ℂ, d < s.re →
              ∫ t in Ω, θ' t * ((χ t : ℂˣ) : ℂ)⁻¹ * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν =
                R' s + C * a / (s - d - (τ : ℂ) * Complex.I) - C * b / (s - (τ : ℂ) * Complex.I))) ∧
          (∃ c₁ c₀ p₁ p₀ : ℂ,
            ((∀ τ : ℝ, χ ≠ NumberField.TateGlobal.normPowChar F τ) → c₁ = 0 ∧ c₀ = 0) ∧
            (∀ s : ℂ, d < s.re →
              ∫ t in Ω, θ t * ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν =
                R s + (c₁ / (s - p₁) + c₀ / (s - p₀))) ∧
            (∀ s : ℂ, d < s.re →
              ∫ t in Ω, θ' t * ((χ t : ℂˣ) : ℂ)⁻¹ * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν =
                R' s - (c₁ / (s - ((d : ℂ) - p₁)) + c₀ / (s - ((d : ℂ) - p₀))))) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_TateGlobal_exists_setIntegral_eq_entirePart_add_polarPart_and_fe_of_thetaInversion.solution
