import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_mixedEmbedding_setLIntegral_setOf_forall_normAtPlace_mem_Icc_one_exp_inv_norm_eq_two_pow_mul_two_pi_pow

set_option autoImplicit false

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped ENNReal

open scoped Classical in

theorem NumberField.mixedEmbedding.setLIntegral_setOf_forall_normAtPlace_mem_Icc_one_exp_inv_norm_eq_two_pow_mul_two_pi_pow
    (K : Type) [Field K] [NumberField K] :
    ∫⁻ x in {x : mixedSpace K | ∀ w : InfinitePlace K, normAtPlace w x ∈ Set.Icc 1 (Real.exp 1)},
        (ENNReal.ofReal (mixedEmbedding.norm x))⁻¹ ∂volume =
      2 ^ nrRealPlaces K * ENNReal.ofReal ((2 * Real.pi) ^ nrComplexPlaces K) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_mixedEmbedding_setLIntegral_setOf_forall_normAtPlace_mem_Icc_one_exp_inv_norm_eq_two_pow_mul_two_pi_pow.solution
