import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_exists_norm_sub_one_mul_dedekindZeta_continuation_le_mul_exp_mul_im_sq

set_option autoImplicit false

theorem NumberField.exists_norm_sub_one_mul_dedekindZeta_continuation_le_mul_exp_mul_im_sq
    (K : Type) [Field K] [NumberField K] (R : ℂ → ℂ) (hR : Differentiable ℂ R)
    (hRζ : ∀ s : ℂ, 1 < s.re → R s = (s - 1) * NumberField.dedekindZeta K s) (a b : ℝ) :
    ∃ B C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖R s‖ ≤ B * Real.exp (C * s.im ^ 2) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_norm_sub_one_mul_dedekindZeta_continuation_le_mul_exp_mul_im_sq.solution
