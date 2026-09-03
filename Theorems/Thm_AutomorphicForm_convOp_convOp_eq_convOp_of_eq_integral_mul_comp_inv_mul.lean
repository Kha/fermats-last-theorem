import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import P2M.Util
import P2M.Sol.S_AutomorphicForm_convOp_convOp_eq_convOp_of_eq_integral_mul_comp_inv_mul
attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions
attribute [-simp] ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.convOp_convOp_eq_convOp_of_eq_integral_mul_comp_inv_mul
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (U : Subgroup (AdelicGL2 (𝓞 L) L)) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ ψ : AdelicGL2 (𝓞 L) L → ℂ)
    (hφ : IsFactorizableTestFn L φ ∧ Continuous φ ∧ HasCompactSupport φ)
    (hψ : IsFactorizableTestFn L ψ ∧ Continuous ψ ∧ HasCompactSupport ψ) :
    ∀ χ : AdelicGL2 (𝓞 L) L → ℂ,
      χ = (fun g => ∫ y, ψ y * φ (y⁻¹ * g) ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) →
      (IsFactorizableTestFn L χ ∧ Continuous χ ∧ HasCompactSupport χ) ∧
      (∀ w : AdelicGL2 (𝓞 L) L → ℂ, Continuous w → convOp L ψ (convOp L φ w) = convOp L χ w) ∧
      ((∀ u ∈ U, ∀ x, ψ (u * x) = ψ x) → ∀ u ∈ U, ∀ x, χ (u * x) = χ x) ∧
      ((∀ u ∈ U, ∀ x, φ (x * u) = φ x) → ∀ u ∈ U, ∀ x, χ (x * u) = χ x) ∧
      (∀ tys : ArchTypeFamily L,
        (fun x => ψ x⁻¹) ∈ archCutSubmodule L tys → (fun x => χ x⁻¹) ∈ archCutSubmodule L tys) ∧
      (∀ tys : ArchTypeFamily L, φ ∈ archDualCutSubmodule L tys → χ ∈ archDualCutSubmodule L tys) ∧
      (IsUnitFactorizableAbove K L U S ψ → IsUnitFactorizableAbove K L U S φ →
        IsUnitFactorizableAbove K L U S χ) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_convOp_convOp_eq_convOp_of_eq_integral_mul_comp_inv_mul.solution
