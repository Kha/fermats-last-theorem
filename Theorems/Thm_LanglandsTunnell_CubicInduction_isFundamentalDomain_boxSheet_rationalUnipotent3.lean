import Definitions.Def_LanglandsTunnell_CubicInduction_WhittakerBlock
import Definitions.Def_NumberField_AdelicBox
import Mathlib.MeasureTheory.Group.FundamentalDomain
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_isFundamentalDomain_boxSheet_rationalUnipotent3
attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions
attribute [-simp] ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox LanglandsTunnell.CubicInduction
  WhittakerBlock
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem LanglandsTunnell.CubicInduction.isFundamentalDomain_boxSheet_rationalUnipotent3 :
    let Γ : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ) := unipotentSubgroup3 ⊓ (globalPointsGL 3 (𝓞 ℚ) ℚ).range
    let T : Set ↥unipotentSubgroup3 :=
      {n | ∃ x ∈ adelicBox ℚ, ∃ y ∈ adelicBox ℚ, ∃ z ∈ adelicBox ℚ,
        (n : AdelicGL 3 (𝓞 ℚ) ℚ) = upperUnipotent3 x y z}
    Countable Γ ∧ MeasurableSet T ∧
    IsFundamentalDomain (Γ.subgroupOf unipotentSubgroup3) T unipotentHaar3 ∧
    (∀ F : ↥unipotentSubgroup3 → ℝ≥0∞, Measurable F →
      ∫⁻ n in T, F n ∂unipotentHaar3 =
        ∫⁻ x in adelicBox ℚ, ∫⁻ y in adelicBox ℚ, ∫⁻ z in adelicBox ℚ,
          F ⟨upperUnipotent3 x y z, Subgroup.subset_closure ⟨(x, y, z), rfl⟩⟩
          ∂(adelicAddHaar (𝓞 ℚ) ℚ) ∂(adelicAddHaar (𝓞 ℚ) ℚ) ∂(adelicAddHaar (𝓞 ℚ) ℚ) ∧
      ∫⁻ n in T, F n ∂unipotentHaar3 =
        (adelicAddHaar (𝓞 ℚ) ℚ (adelicBox ℚ)) ^ 3 *
          ∫⁻ x, ∫⁻ y, ∫⁻ z, F ⟨upperUnipotent3 x y z, Subgroup.subset_closure ⟨(x, y, z), rfl⟩⟩
            ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) (adelicBox ℚ))
            ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) (adelicBox ℚ))
            ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) (adelicBox ℚ))) ∧
    unipotentHaar3 T = (adelicAddHaar (𝓞 ℚ) ℚ (adelicBox ℚ)) ^ 3 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_isFundamentalDomain_boxSheet_rationalUnipotent3.solution
