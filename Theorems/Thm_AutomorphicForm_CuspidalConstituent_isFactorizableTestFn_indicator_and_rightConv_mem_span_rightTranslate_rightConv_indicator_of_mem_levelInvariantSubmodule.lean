import Definitions.Def_AutomorphicForm_CuspidalConstituent
import P2M.Util
import P2M.Sol.S_AutomorphicForm_CuspidalConstituent_isFactorizableTestFn_indicator_and_rightConv_mem_span_rightTranslate_rightConv_indicator_of_mem_levelInvariantSubmodule
attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions
attribute [-simp] ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.isFactorizableTestFn_indicator_and_rightConv_mem_span_rightTranslate_rightConv_indicator_of_mem_levelInvariantSubmodule
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F) (B : Set (AdeleRing (𝓞 F) F))
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (Ψ : AdelicGL2 (𝓞 F) F → ℂ) (hΨ : Continuous Ψ)
    (hΨN : Ψ ∈ levelInvariantSubmodule F (productionPinsOf F D
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) gen B) N)
    (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ)
    (hfa : IsArchTestFactor F fa) (hff : IsFinTestFactor F ff) :
    IsFactorizableTestFn F (fun y => fa (AdelicLevel.glArch (𝓞 F) F y) *
        Set.indicator ((AdelicLevel.glFin (𝓞 F) F) '' ((productionPinsOf F D
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) gen B).U N : Set (AdelicGL2 (𝓞 F) F)))
          (fun _ => (1 : ℂ)) (AdelicLevel.glFin (𝓞 F) F y)) ∧
    rightConv F Ψ (fun y => fa (AdelicLevel.glArch (𝓞 F) F y) * ff (AdelicLevel.glFin (𝓞 F) F y)) ∈
      Submodule.span ℂ ((fun g => rightTranslate F g (rightConv F Ψ
        (fun y => fa (AdelicLevel.glArch (𝓞 F) F y) *
          Set.indicator ((AdelicLevel.glFin (𝓞 F) F) '' ((productionPinsOf F D
          (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) gen B).U N : Set (AdelicGL2 (𝓞 F) F)))
            (fun _ => (1 : ℂ)) (AdelicLevel.glFin (𝓞 F) F y)))) ''
        (finiteAdelicGL2Subgroup F : Set (AdelicGL2 (𝓞 F) F))) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_CuspidalConstituent_isFactorizableTestFn_indicator_and_rightConv_mem_span_rightTranslate_rightConv_indicator_of_mem_levelInvariantSubmodule.solution
