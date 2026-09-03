import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_finsum_posLog_inv_norm_one_sub_add_sum_mult_mul_posLog_inv_le

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.finsum_posLog_inv_norm_one_sub_add_sum_mult_mul_posLog_inv_le
    (F : Type) [Field F] [NumberField F] (c : F) :
    (∑ᶠ v : HeightOneSpectrum (𝓞 F), Real.posLog ‖algebraMap F (v.adicCompletion F) (1 - c)‖⁻¹) +
        ∑ w : InfinitePlace F, (w.mult : ℝ) * Real.posLog (w (1 - c))⁻¹ ≤
      (∑ᶠ v : HeightOneSpectrum (𝓞 F), Real.posLog ‖algebraMap F (v.adicCompletion F) c‖) +
        ∑ w : InfinitePlace F, (w.mult : ℝ) * (Real.log 2 + Real.posLog (w c)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_finsum_posLog_inv_norm_one_sub_add_sum_mult_mul_posLog_inv_le.solution
