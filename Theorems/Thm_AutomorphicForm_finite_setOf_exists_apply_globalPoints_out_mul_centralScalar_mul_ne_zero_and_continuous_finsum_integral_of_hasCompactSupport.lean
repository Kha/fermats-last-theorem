import Definitions.Def_AutomorphicForm_AdelicLsXi
import P2M.Util
import P2M.Sol.S_AutomorphicForm_finite_setOf_exists_apply_globalPoints_out_mul_centralScalar_mul_ne_zero_and_continuous_finsum_integral_of_hasCompactSupport
attribute [-instance] NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions
attribute [-simp] ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply

set_option autoImplicit false

open MeasureTheory NumberField AutomorphicForm

theorem AutomorphicForm.finite_setOf_exists_apply_globalPoints_out_mul_centralScalar_mul_ne_zero_and_continuous_finsum_integral_of_hasCompactSupport
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (νZ : Measure (AdeleRing (𝓞 F) F)ˣ) [νZ.IsHaarMeasure]
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    (∀ C : Set (AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F), IsCompact C →
      {q : GL (Fin 2) F ⧸ Subgroup.center (GL (Fin 2) F) |
        ∃ p ∈ C, ∃ z : (AdeleRing (𝓞 F) F)ˣ,
          f (p.1⁻¹ * globalPoints (𝓞 F) F q.out * (centralScalar (𝓞 F) F z * p.2)) ≠ 0}.Finite) ∧
    Continuous (fun p : AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F =>
      ∑ᶠ q : GL (Fin 2) F ⧸ Subgroup.center (GL (Fin 2) F),
        ∫ z, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          f (p.1⁻¹ * globalPoints (𝓞 F) F q.out * (centralScalar (𝓞 F) F z * p.2)) ∂νZ) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_finite_setOf_exists_apply_globalPoints_out_mul_centralScalar_mul_ne_zero_and_continuous_finsum_integral_of_hasCompactSupport.solution
