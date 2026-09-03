import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_forall_lintegral_and_integral_maximalCompactHaar_eq_mul_prod_semiLocalHaar
attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions
attribute [-simp] AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv
attribute [-simp] RestrictedProduct.mapAlongLinearMap_apply

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain
open AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_lintegral_and_integral_maximalCompactHaar_eq_mul_prod_semiLocalHaar
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    ∃ κ : @Measure (GL (Fin 2) (InfiniteAdeleRing L)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing L)),
      @IsProbabilityMeasure (GL (Fin 2) (InfiniteAdeleRing L)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing L)) κ ∧
      κ = @Measure.map (adelicMaximalCompact L) (GL (Fin 2) (InfiniteAdeleRing L)) _
            (AutomorphicForm.glBorelOf (InfiniteAdeleRing L))
            (fun k : adelicMaximalCompact L => glArch (𝓞 L) L (k : AdelicGL2 (𝓞 L) L)) (maximalCompactHaar L) ∧
      (∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (g : GL (Fin 2) (InfiniteAdeleRing L) → ℝ≥0∞)
        (f : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ≥0∞),
        @Measurable _ _ (AutomorphicForm.glBorelOf (InfiniteAdeleRing L)) _ g →
        (∀ v ∈ S, @Measurable _ _ (AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)) _ (f v)) →
        ∫⁻ k, g (glArch (𝓞 L) L (k : AdelicGL2 (𝓞 L) L)) *
            ∏ v ∈ S, f v (AutomorphicForm.semiLocalComponent K L v (glFin (𝓞 L) L (k : AdelicGL2 (𝓞 L) L)))
          ∂(maximalCompactHaar L) =
        (∫⁻ x, g x ∂κ) *
          ∏ v ∈ S, ∫⁻ y in AutomorphicForm.semiLocalIntegralSet K L v, f v y ∂(AutomorphicForm.semiLocalHaar K L v)) ∧
      ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (g : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
        (f : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        Integrable g κ →
        (∀ v ∈ S, IntegrableOn (f v) (AutomorphicForm.semiLocalIntegralSet K L v) (AutomorphicForm.semiLocalHaar K L v)) →
        Integrable (fun k : adelicMaximalCompact L => g (glArch (𝓞 L) L (k : AdelicGL2 (𝓞 L) L)) *
            ∏ v ∈ S, f v (AutomorphicForm.semiLocalComponent K L v (glFin (𝓞 L) L (k : AdelicGL2 (𝓞 L) L))))
          (maximalCompactHaar L) ∧
        ∫ k, g (glArch (𝓞 L) L (k : AdelicGL2 (𝓞 L) L)) *
            ∏ v ∈ S, f v (AutomorphicForm.semiLocalComponent K L v (glFin (𝓞 L) L (k : AdelicGL2 (𝓞 L) L)))
          ∂(maximalCompactHaar L) =
        (∫ x, g x ∂κ) *
          ∏ v ∈ S, ∫ y in AutomorphicForm.semiLocalIntegralSet K L v, f v y ∂(AutomorphicForm.semiLocalHaar K L v) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_forall_lintegral_and_integral_maximalCompactHaar_eq_mul_prod_semiLocalHaar.solution
