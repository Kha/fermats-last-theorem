import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isWeightedOrbitalIntegralOn_sum_mul_centralScalar_mul_and_measurable_of_diagonal
attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions
attribute [-simp] ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply

set_option autoImplicit false
open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

theorem AutomorphicForm.isWeightedOrbitalIntegralOn_sum_mul_centralScalar_mul_and_measurable_of_diagonal
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (γ₀ : GL (Fin 2) K)
    (hγ₀ : (γ₀ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (γ₀ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧
      (γ₀ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ₀ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1)
    (τ : Measure (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))))
    [τ.IsHaarMeasure]
    (f : ι → AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ)
    (hf : ∀ i ∈ s, Continuous (f i) ∧ HasCompactSupport (f i))
    (J : ι → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hJ : ∀ i ∈ s, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      AutomorphicForm.IsWeightedOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K)
        (fun x : AutomorphicForm.AdelicGL2 (𝓞 K) K =>
          -Real.log (NumberField.AdelicHeight.adelicHeight K x)
            - Real.log (NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.adelicWeyl (𝓞 K) K * x)))
        (AutomorphicForm.globalPoints (𝓞 K) K γ₀) τ
        (fun g : AutomorphicForm.AdelicGL2 (𝓞 K) K => f i (AutomorphicForm.centralScalar (𝓞 K) K z * g)) (J i z)) :
    (∀ z : (AdeleRing (𝓞 K) K)ˣ,
      AutomorphicForm.IsWeightedOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K)
        (fun x : AutomorphicForm.AdelicGL2 (𝓞 K) K =>
          -Real.log (NumberField.AdelicHeight.adelicHeight K x)
            - Real.log (NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.adelicWeyl (𝓞 K) K * x)))
        (AutomorphicForm.globalPoints (𝓞 K) K γ₀) τ
        (fun g : AutomorphicForm.AdelicGL2 (𝓞 K) K =>
          ∑ i ∈ s, c i * f i (AutomorphicForm.centralScalar (𝓞 K) K z * g)) (∑ i ∈ s, c i * J i z)) ∧
    (∀ i ∈ s, Measurable (J i)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isWeightedOrbitalIntegralOn_sum_mul_centralScalar_mul_and_measurable_of_diagonal.solution
