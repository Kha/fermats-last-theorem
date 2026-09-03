import Definitions.Def_AutomorphicForm_GodementSection
import P2M.Util
import P2M.Sol.S_NumberField_AdelicFourier_continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2
attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions
attribute [-simp] ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicFourier IsDedekindDomain

open scoped Classical in

theorem NumberField.AdelicFourier.continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (hΦ : Φ ∈ schwartzBruhat2 F) :
    Continuous Φ ∧
    (∀ N : ℕ, ∃ (C : ℝ) (K : Set (Fin 2 → FiniteAdeleRing (𝓞 F) F)), 0 ≤ C ∧ IsCompact K ∧
      (∀ x : Fin 2 → AdeleRing (𝓞 F) F,
        ‖Φ x‖ * (1 + ‖fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1‖) ^ N ≤ C) ∧
      (∀ x : Fin 2 → AdeleRing (𝓞 F) F, (fun i => (x i).2) ∉ K → Φ x = 0)) ∧
    (∀ (μ : Measure (Fin 2 → AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure], Integrable Φ μ) ∧
    (∀ (μ₁ : Measure (AdeleRing (𝓞 F) F)) [μ₁.IsAddHaarMeasure], Integrable Φ (pairHaar μ₁)) ∧
    (∀ g : AutomorphicForm.AdelicGL2 (𝓞 F) F,
      (fun x => Φ (Matrix.vecMul x (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))))
        ∈ schwartzBruhat2 F) ∧
    (∀ t : (AdeleRing (𝓞 F) F)ˣ, (fun x => Φ ((t : AdeleRing (𝓞 F) F) • x)) ∈ schwartzBruhat2 F) ∧
    (∀ a : Fin 2 → AdeleRing (𝓞 F) F, (fun x => Φ (x + a)) ∈ schwartzBruhat2 F) ∧
    (∀ g : AutomorphicForm.AdelicGL2 (𝓞 F) F,
      (fun t : AdeleRing (𝓞 F) F => Φ (AutomorphicForm.bottomRowVec F g t)) ∈ schwartzBruhat F) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2.solution
