import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import P2M.Util
import P2M.Sol.S_NumberField_AdelicFourier_exists_nonneg_mem_schwartzBruhat2_norm_reflectPair_le_and_setLIntegral_enorm_reflectPair_comp_le_lintegral_mul_ofReal_rpow
attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions
attribute [-simp] ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicFourier AutomorphicForm
open scoped ENNReal

theorem NumberField.AdelicFourier.exists_nonneg_mem_schwartzBruhat2_norm_reflectPair_le_and_setLIntegral_enorm_reflectPair_comp_le_lintegral_mul_ofReal_rpow
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ₁ : Measure (AdeleRing (𝓞 F) F)) [μ₁.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (hΦ : Φ ∈ schwartzBruhat2 F) :
    ∃ Ψ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ, Ψ ∈ schwartzBruhat2 F ∧
      (∀ x : Fin 2 → AdeleRing (𝓞 F) F, 0 ≤ (Ψ x).re ∧ (Ψ x).im = 0) ∧
      (∀ x : Fin 2 → AdeleRing (𝓞 F) F, ‖reflectPair ψ μ₁ Φ x‖ ≤ (Ψ x).re) ∧
      ∀ (T : Type) [MeasurableSpace T] (τ : Measure T) (col : T → (Fin 2 → AdeleRing (𝓞 F) F))
        (N : T → ℝ), MeasurableSet {t | 1 ≤ N t} → ∀ s : ℝ, 0 ≤ s →
          ∫⁻ t in {t | 1 ≤ N t}, ‖reflectPair ψ μ₁ Φ (col t)‖ₑ ∂τ ≤
            ∫⁻ t, ENNReal.ofReal (Ψ (col t)).re * ENNReal.ofReal (N t ^ s) ∂τ := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_exists_nonneg_mem_schwartzBruhat2_norm_reflectPair_le_and_setLIntegral_enorm_reflectPair_comp_le_lintegral_mul_ofReal_rpow.solution
