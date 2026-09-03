import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_AutomorphicForm_integral_integral_unipotentGL2_conj_twistedOrbital_eq_integral_mul_integral_and_lintegral_lt_top_of_norm_div_ne_one
attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions
attribute [-simp] ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply
attribute [-simp] FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar

attribute [local instance] NumberField.AdelicHaar.adeleBorel

theorem AutomorphicForm.integral_integral_unipotentGL2_conj_twistedOrbital_eq_integral_mul_integral_and_lintegral_lt_top_of_norm_div_ne_one
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξ : (AdeleRing (𝓞 L) L)ˣ → ℂ) (hξ : Continuous ξ)
    (t' : GL (Fin 2) L) (ht'u : (t' : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (ht'l : (t' : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 0 0 / (t' : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (y : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    (∫⁻ s : AdeleRing (𝓞 L) L, ∫⁻ z, ‖ξ z‖ₑ *
        ‖φ ((AutomorphicForm.unipotentGL2 s * y)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t' *
          AutomorphicForm.sigmaAdelicAct K L D σ
            (AutomorphicForm.centralScalar (𝓞 L) L z * (AutomorphicForm.unipotentGL2 s * y)))‖ₑ
        ∂νZL ∂(adelicAddHaar (𝓞 L) L)) =
      ∫⁻ w, ‖ξ w‖ₑ * ∫⁻ t : AdeleRing (𝓞 L) L,
        ‖φ (y⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t' *
          AutomorphicForm.sigmaAdelicAct K L D σ
            (AutomorphicForm.unipotentGL2 t * (AutomorphicForm.centralScalar (𝓞 L) L w * y)))‖ₑ
        ∂(adelicAddHaar (𝓞 L) L) ∂νZL ∧
    (∫⁻ w, ‖ξ w‖ₑ * ∫⁻ t : AdeleRing (𝓞 L) L,
        ‖φ (y⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t' *
          AutomorphicForm.sigmaAdelicAct K L D σ
            (AutomorphicForm.unipotentGL2 t * (AutomorphicForm.centralScalar (𝓞 L) L w * y)))‖ₑ
        ∂(adelicAddHaar (𝓞 L) L) ∂νZL) < ⊤ ∧
    ∫ s : AdeleRing (𝓞 L) L, ∫ z, ξ z *
        φ ((AutomorphicForm.unipotentGL2 s * y)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t' *
          AutomorphicForm.sigmaAdelicAct K L D σ
            (AutomorphicForm.centralScalar (𝓞 L) L z * (AutomorphicForm.unipotentGL2 s * y)))
        ∂νZL ∂(adelicAddHaar (𝓞 L) L) =
      ∫ w, ξ w * ∫ t : AdeleRing (𝓞 L) L,
        φ (y⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t' *
          AutomorphicForm.sigmaAdelicAct K L D σ
            (AutomorphicForm.unipotentGL2 t * (AutomorphicForm.centralScalar (𝓞 L) L w * y)))
        ∂(adelicAddHaar (𝓞 L) L) ∂νZL := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_integral_integral_unipotentGL2_conj_twistedOrbital_eq_integral_mul_integral_and_lintegral_lt_top_of_norm_div_ne_one.solution
