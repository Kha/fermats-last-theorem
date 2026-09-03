import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_exists_forall_norm_digamma_le_mul_log_norm_and_norm_logDeriv_GammaReal_le_and_norm_logDeriv_GammaComplex_le_of_le_re

set_option autoImplicit false

theorem Complex.exists_forall_norm_digamma_le_mul_log_norm_and_norm_logDeriv_GammaReal_le_and_norm_logDeriv_GammaComplex_le_of_le_re
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, δ ≤ s.re →
      ‖Complex.digamma s‖ ≤ C * Real.log (2 + ‖s‖) ∧
      ‖logDeriv Complex.Gammaℝ s‖ ≤ C * Real.log (2 + ‖s‖) ∧
      ‖logDeriv Complex.Gammaℂ s‖ ≤ C * Real.log (2 + ‖s‖) := by p2m_exact_reverting @_root_.P2MW.S_Complex_exists_forall_norm_digamma_le_mul_log_norm_and_norm_logDeriv_GammaReal_le_and_norm_logDeriv_GammaComplex_le_of_le_re.solution
