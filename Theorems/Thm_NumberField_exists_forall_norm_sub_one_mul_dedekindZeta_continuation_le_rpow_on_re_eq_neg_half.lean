import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_exists_forall_norm_sub_one_mul_dedekindZeta_continuation_le_rpow_on_re_eq_neg_half

set_option autoImplicit false

theorem NumberField.exists_forall_norm_sub_one_mul_dedekindZeta_continuation_le_rpow_on_re_eq_neg_half
    (K : Type) [Field K] [NumberField K] :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ (R : ℂ → ℂ), Differentiable ℂ R →
        (∀ s : ℂ, 1 < s.re → R s = (s - 1) * NumberField.dedekindZeta K s) →
      ∀ s : ℂ, s.re = -1 / 2 → ‖R s‖ ≤ C * (2 + |s.im|) ^ A := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_forall_norm_sub_one_mul_dedekindZeta_continuation_le_rpow_on_re_eq_neg_half.solution
