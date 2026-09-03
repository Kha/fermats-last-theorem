import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_AdeleRing_dedekindZeta_two_mul_pi_measure_setOf_forall_not_norm_lt_one_eq_pi_measure_setOf_forall_mem_adicCompletionIntegers
attribute [-instance] NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion NumberField.AdelicCentre.locallyCompactSpace_adelicPGL2 NumberField.AdelicCentre.isTopologicalGroup_adelicPGL2 NumberField.AdelicCentre.t2Space_adelicPGL2 NumberField.AdelicCentre.isClosed_center instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions
attribute [-simp] AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply
attribute [-simp] AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal

theorem NumberField.AdeleRing.dedekindZeta_two_mul_pi_measure_setOf_forall_not_norm_lt_one_eq_pi_measure_setOf_forall_mem_adicCompletionIntegers
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
    (μ : Measure (AdeleRing (𝓞 K) K)) (hμ : μ.IsAddHaarMeasure)
    (C : Set (mixedEmbedding.mixedSpace K × mixedEmbedding.mixedSpace K)) (hC : MeasurableSet C) :
    ENNReal.ofReal (NumberField.dedekindZeta K 2).re *
      (Measure.pi fun _ : Fin 2 => μ)
        {c : Fin 2 → AdeleRing (𝓞 K) K |
          (InfiniteAdeleRing.ringEquiv_mixedSpace K (c 0).1, InfiniteAdeleRing.ringEquiv_mixedSpace K (c 1).1) ∈ C ∧
          (∀ v : HeightOneSpectrum (𝓞 K),
            (c 0).2 v ∈ v.adicCompletionIntegers K ∧ (c 1).2 v ∈ v.adicCompletionIntegers K) ∧
          ∀ v : HeightOneSpectrum (𝓞 K), ¬ (‖(c 0).2 v‖ < 1 ∧ ‖(c 1).2 v‖ < 1)} =
    (Measure.pi fun _ : Fin 2 => μ)
        {c : Fin 2 → AdeleRing (𝓞 K) K |
          (InfiniteAdeleRing.ringEquiv_mixedSpace K (c 0).1, InfiniteAdeleRing.ringEquiv_mixedSpace K (c 1).1) ∈ C ∧
          ∀ v : HeightOneSpectrum (𝓞 K),
            (c 0).2 v ∈ v.adicCompletionIntegers K ∧ (c 1).2 v ∈ v.adicCompletionIntegers K} := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdeleRing_dedekindZeta_two_mul_pi_measure_setOf_forall_not_norm_lt_one_eq_pi_measure_setOf_forall_mem_adicCompletionIntegers.solution
