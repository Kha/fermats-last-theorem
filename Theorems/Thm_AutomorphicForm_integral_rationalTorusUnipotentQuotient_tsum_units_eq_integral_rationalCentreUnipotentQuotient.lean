import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Mathlib.MeasureTheory.Group.FundamentalDomain
import P2M.Util
import P2M.Sol.S_AutomorphicForm_integral_rationalTorusUnipotentQuotient_tsum_units_eq_integral_rationalCentreUnipotentQuotient
attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions
attribute [-simp] ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel open AutomorphicForm hiding existsUnique_diagOne_inv_mul_mem_scalar_sup_unipotent_of_mem_borelSubgroup isFundamentalDomain_boxSheet_rationalCentreUnipotent isFundamentalDomain_boxSheet_rationalTorusUnipotent
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem AutomorphicForm.integral_rationalTorusUnipotentQuotient_tsum_units_eq_integral_rationalCentreUnipotentQuotient
    (F : Type) [Field F] [NumberField F]
    (𝓕B : Set (AdelicGL2 (𝓞 F) F))
    (h𝓕B : IsFundamentalDomain ((borelSubgroup F).map (globalPoints (𝓞 F) F)) 𝓕B (adelicGLHaar (Fin 2) (𝓞 F) F))
    (k : AdelicGL2 (𝓞 F) F → ℂ) (hk : Measurable k)
    (hkH : ∀ h ∈ rationalCentreUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, k (h * g) = k g)
    (hfin : ∫⁻ g in 𝓕B, ∑' a : Fˣ, ‖k (globalPoints (𝓞 F) F (diagOne a) * g)‖ₑ
      ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ∞) :
    Integrable (fun q : RationalCentreUnipotentQuotient F => k q.out) (rationalCentreUnipotentQuotientMeasure F) ∧
    Integrable (fun q : RationalTorusUnipotentQuotient F => ∑' a : Fˣ, k (globalPoints (𝓞 F) F (diagOne a) * q.out))
      (rationalTorusUnipotentQuotientMeasure F) ∧
    ∫ q : RationalTorusUnipotentQuotient F, ∑' a : Fˣ, k (globalPoints (𝓞 F) F (diagOne a) * q.out)
        ∂(rationalTorusUnipotentQuotientMeasure F) =
      ∫ g in 𝓕B, ∑' a : Fˣ, k (globalPoints (𝓞 F) F (diagOne a) * g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) ∧
    ∫ g in 𝓕B, ∑' a : Fˣ, k (globalPoints (𝓞 F) F (diagOne a) * g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
      ∫ q : RationalCentreUnipotentQuotient F, k q.out ∂(rationalCentreUnipotentQuotientMeasure F) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_integral_rationalTorusUnipotentQuotient_tsum_units_eq_integral_rationalCentreUnipotentQuotient.solution
