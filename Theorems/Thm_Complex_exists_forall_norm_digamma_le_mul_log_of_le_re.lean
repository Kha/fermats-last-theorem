import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_exists_forall_norm_digamma_le_mul_log_of_le_re

set_option autoImplicit false

theorem Complex.exists_forall_norm_digamma_le_mul_log_of_le_re
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, δ ≤ s.re → s.re ≤ 2 →
      ‖Complex.digamma s‖ ≤ C * Real.log (2 + |s.im|) := by p2m_exact_reverting @_root_.P2MW.S_Complex_exists_forall_norm_digamma_le_mul_log_of_le_re.solution
