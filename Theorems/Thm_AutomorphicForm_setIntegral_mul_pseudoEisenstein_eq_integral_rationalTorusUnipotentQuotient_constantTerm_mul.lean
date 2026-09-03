import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_AutomorphicForm_BorelSubgroup
import P2M.Util
import P2M.Sol.S_AutomorphicForm_setIntegral_mul_pseudoEisenstein_eq_integral_rationalTorusUnipotentQuotient_constantTerm_mul
attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions
attribute [-simp] ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox AutomorphicForm
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem AutomorphicForm.setIntegral_mul_pseudoEisenstein_eq_integral_rationalTorusUnipotentQuotient_constantTerm_mul
    (F : Type) [Field F] [NumberField F]
    (S : Set (AdelicGL2 (𝓞 F) F)) (hSm : MeasurableSet S)
    (hS : ∀ (γ : GL (Fin 2) F) (x : AdelicGL2 (𝓞 F) F), globalPoints (𝓞 F) F γ * x ∈ S ↔ x ∈ S)
    (hSN : ∀ (u : AdeleRing (𝓞 F) F) (x : AdelicGL2 (𝓞 F) F), unipotentGL2 u * x ∈ S ↔ x ∈ S)
    (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) (hΦ₀S : Φ₀ ⊆ S)
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ₀ ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S))
    (f ψ : AdelicGL2 (𝓞 F) F → ℂ) (hf : Measurable f) (hψ : Measurable ψ)
    (hfG : ∀ (γ : GL (Fin 2) F) (x : AdelicGL2 (𝓞 F) F), f (globalPoints (𝓞 F) F γ * x) = f x)
    (hψB : ∀ γ ∈ borelSubgroup F, ∀ x : AdelicGL2 (𝓞 F) F, ψ (globalPoints (𝓞 F) F γ * x) = ψ x)
    (hψN : ∀ (u : AdeleRing (𝓞 F) F) (x : AdelicGL2 (𝓞 F) F), ψ (unipotentGL2 u * x) = ψ x)
    (hfin : ∫⁻ x in Φ₀, ‖f x‖ₑ * (‖ψ x‖ₑ + ∑' ξ : F,
        ‖ψ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x)‖ₑ)
      ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ∞) :
    IntegrableOn (fun x => f x * pseudoEisenstein F ψ x) Φ₀ (adelicGLHaar (Fin 2) (𝓞 F) F) ∧
    (∀ h ∈ rationalTorusUnipotent F, ∀ y : AdelicGL2 (𝓞 F) F,
      S.indicator (fun y => constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
          (fun t => unipotentGL2 t) f y * ψ y) (h * y) =
        S.indicator (fun y => constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
          (fun t => unipotentGL2 t) f y * ψ y) y) ∧
    Integrable (fun q : RationalTorusUnipotentQuotient F =>
        S.indicator (fun y => constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
          (fun t => unipotentGL2 t) f y * ψ y) q.out)
      (rationalTorusUnipotentQuotientMeasure F) ∧
    ∫ x in Φ₀, f x * pseudoEisenstein F ψ x ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
      ∫ q, S.indicator (fun y => constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
          (fun t => unipotentGL2 t) f y * ψ y) q.out ∂(rationalTorusUnipotentQuotientMeasure F) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_setIntegral_mul_pseudoEisenstein_eq_integral_rationalTorusUnipotentQuotient_constantTerm_mul.solution
