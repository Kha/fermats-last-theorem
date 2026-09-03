import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_mixedEmbedding_fundamentalCone_setLIntegral_inv_norm_eq_volume_normLeOne_mul_log

set_option autoImplicit false

open MeasureTheory NumberField NumberField.mixedEmbedding
open scoped Classical

theorem NumberField.mixedEmbedding.fundamentalCone.setLIntegral_inv_norm_eq_volume_normLeOne_mul_log
    (K : Type) [Field K] [NumberField K] (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∫⁻ x in NumberField.mixedEmbedding.fundamentalCone K ∩
        {x | NumberField.mixedEmbedding.norm x ∈ Set.Icc a b},
        ENNReal.ofReal (NumberField.mixedEmbedding.norm x)⁻¹ =
      volume (NumberField.mixedEmbedding.fundamentalCone.normLeOne K) * ENNReal.ofReal (Real.log (b / a)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_mixedEmbedding_fundamentalCone_setLIntegral_inv_norm_eq_volume_normLeOne_mul_log.solution
