import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicBox
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_lintegral_box_norm_sq_radicalP21_eq_tsum_norm_sq_radicalCoefficient
attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions
attribute [-simp] ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply

set_option autoImplicit false

open MeasureTheory NumberField AutomorphicForm LanglandsTunnell.CubicInduction

open scoped ENNReal

theorem
    LanglandsTunnell.CubicInduction.lintegral_box_norm_sq_radicalP21_eq_tsum_norm_sq_radicalCoefficient
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (_hcont : Continuous Φ)
    (_hP21 : IsCuspidalAlongP21 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) Φ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (∫⁻ z : AdeleRing (𝓞 ℚ) ℚ, ∫⁻ y : AdeleRing (𝓞 ℚ) ℚ, (‖Φ (radicalP21 ![z, y] * g)‖₊ : ℝ≥0∞) ^ 2
        ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))
        ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))) =
      ∑' v : {v : Fin 2 → ℚ // v ≠ 0},
        (‖∫ z : AdeleRing (𝓞 ℚ) ℚ, ∫ y : AdeleRing (𝓞 ℚ) ℚ,
            Φ (radicalP21 ![z, y] * g) *
              ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (v.1 0) * z + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (v.1 1) * y))
          ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))
          ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))‖₊ :
            ℝ≥0∞) ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_lintegral_box_norm_sq_radicalP21_eq_tsum_norm_sq_radicalCoefficient.solution
