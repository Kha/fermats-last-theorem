import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_M4aHerbrand_IdeleGaloisDescent_exists_continuousAddEquiv_measurePreserving_act_sub_algebraMap_mul_of_norm_ne_one
attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions
attribute [-simp] ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply

set_option autoImplicit false

open NumberField MeasureTheory

theorem M4aHerbrand.IdeleGaloisDescent.exists_continuousAddEquiv_measurePreserving_act_sub_algebraMap_mul_of_norm_ne_one
    {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (c : L) (hc : Algebra.norm K c ≠ 1)
    [MeasurableSpace (AdeleRing (𝓞 L) L)] [BorelSpace (AdeleRing (𝓞 L) L)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 L) L)) [μ.IsAddHaarMeasure] :
    ∃ e : AdeleRing (𝓞 L) L ≃ₜ+ AdeleRing (𝓞 L) L,
      (∀ s : AdeleRing (𝓞 L) L,
        e s = (D.act σ : RingAut (AdeleRing (𝓞 L) L)) s - algebraMap L (AdeleRing (𝓞 L) L) c * s) ∧
      MeasureTheory.addEquivAddHaarChar e = 1 ∧ MeasureTheory.MeasurePreserving e μ μ := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_IdeleGaloisDescent_exists_continuousAddEquiv_measurePreserving_act_sub_algebraMap_mul_of_norm_ne_one.solution
