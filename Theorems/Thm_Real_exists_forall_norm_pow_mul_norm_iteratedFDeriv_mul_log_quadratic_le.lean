import Mathlib
import P2M.Util
import P2M.Sol.S_Real_exists_forall_norm_pow_mul_norm_iteratedFDeriv_mul_log_quadratic_le

set_option autoImplicit false

theorem Real.exists_forall_norm_pow_mul_norm_iteratedFDeriv_mul_log_quadratic_le
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ∃ C : ℝ, 0 ≤ C ∧
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p : ℝ × ℝ => (α * p.1 ^ 2 + β * p.2 ^ 2) * Real.log (α * p.1 ^ 2 + β * p.2 ^ 2))
        {p : ℝ × ℝ | p ≠ 0} ∧
      ∀ n : ℕ, n ≤ 4 → ∀ p : ℝ × ℝ, p ≠ 0 →
        ‖p‖ ^ n *
            ‖iteratedFDeriv ℝ n
                (fun p : ℝ × ℝ => (α * p.1 ^ 2 + β * p.2 ^ 2) * Real.log (α * p.1 ^ 2 + β * p.2 ^ 2))
                p‖ ≤
          C * ‖p‖ ^ 2 * (1 + |Real.log ‖p‖|) := by p2m_exact_reverting @_root_.P2MW.S_Real_exists_forall_norm_pow_mul_norm_iteratedFDeriv_mul_log_quadratic_le.solution
