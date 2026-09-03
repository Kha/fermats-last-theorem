import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_exists_contDiffOn_norm_one_sub_exp_sq_mul_log_eq_mul_add

set_option autoImplicit false

theorem Complex.exists_contDiffOn_norm_one_sub_exp_sq_mul_log_eq_mul_add :
    ∃ a b : ℝ × ℝ → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) a {p : ℝ × ℝ | |p.2| < 1 / 2} ∧
      ContDiffOn ℝ (⊤ : ℕ∞) b {p : ℝ × ℝ | |p.2| < 1 / 2} ∧
      (∀ p : ℝ × ℝ, |p.2| < 1 / 2 → 0 < a p) ∧
      (∀ p : ℝ × ℝ, |p.2| < 1 / 2 →
        ‖(1 : ℂ) - Complex.exp ((p.1 / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 : ℝ))‖ ^ 2 *
            Real.log ‖(1 : ℂ) - Complex.exp ((p.1 / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 : ℝ))‖ =
          a p * ((p.1 ^ 2 / 4 + 4 * Real.pi ^ 2 * p.2 ^ 2) *
              Real.log (p.1 ^ 2 / 4 + 4 * Real.pi ^ 2 * p.2 ^ 2)) +
            (p.1 ^ 2 / 4 + 4 * Real.pi ^ 2 * p.2 ^ 2) * b p) ∧
      (∀ p : ℝ × ℝ,
        Complex.exp ((p.1 / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 : ℝ)) = 1 ↔
          p.1 = 0 ∧ ∃ k : ℤ, p.2 = k) ∧
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p : ℝ × ℝ =>
          ‖(1 : ℂ) - Complex.exp ((p.1 / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 : ℝ))‖ ^ 2 *
            Real.log ‖(1 : ℂ) - Complex.exp ((p.1 / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 : ℝ))‖)
        {p : ℝ × ℝ | Complex.exp ((p.1 / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 : ℝ)) ≠ 1} := by p2m_exact_reverting @_root_.P2MW.S_Complex_exists_contDiffOn_norm_one_sub_exp_sq_mul_log_eq_mul_add.solution
