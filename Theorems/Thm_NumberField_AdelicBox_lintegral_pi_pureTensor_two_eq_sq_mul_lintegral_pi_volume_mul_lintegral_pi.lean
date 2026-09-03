import Definitions.Def_NumberField_AdelicBox
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import P2M.Util
import P2M.Sol.S_NumberField_AdelicBox_lintegral_pi_pureTensor_two_eq_sq_mul_lintegral_pi_volume_mul_lintegral_pi
attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions
attribute [-simp] ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply

set_option autoImplicit false

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.AdelicBox IsDedekindDomain

open scoped Classical in

theorem NumberField.AdelicBox.lintegral_pi_pureTensor_two_eq_sq_mul_lintegral_pi_volume_mul_lintegral_pi
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (G : (Fin 2 → mixedEmbedding.mixedSpace F) → ENNReal) (hG : Measurable G)
    (H : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ENNReal) (hH : Measurable H) :
    ∫⁻ x, G (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) * H (fun i => (x i).2)
        ∂(Measure.pi fun _ : Fin 2 => μ) =
      ENNReal.ofReal ((μ (adelicBox F)).toReal * 2 ^ nrComplexPlaces F /
            (Real.sqrt |(discr F : ℝ)| * (ν (integralFiniteAdeles (𝓞 F) F)).toReal)) ^ 2 *
        (∫⁻ y, G y ∂(Measure.pi fun _ : Fin 2 => (volume : Measure (mixedEmbedding.mixedSpace F)))) *
        ∫⁻ z, H z ∂(Measure.pi fun _ : Fin 2 => ν) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicBox_lintegral_pi_pureTensor_two_eq_sq_mul_lintegral_pi_volume_mul_lintegral_pi.solution
