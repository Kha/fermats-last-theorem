import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_exists_forall_norm_integral_integral_cexp_mul_normSq_log_germ_mul_le

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_forall_norm_integral_integral_cexp_mul_normSq_log_germ_mul_le
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (h : ℝ × ℝ → ℂ), ContDiff ℝ (⊤ : ℕ∞) h → (∀ p : ℝ × ℝ, R < |p.1| → h p = 0) →
        (∀ p : ℝ × ℝ, h (p.1, p.2 + 1) = h p) →
      ∀ M : ℝ, (∀ n : ℕ, n ≤ 6 → ∀ p : ℝ × ℝ, ‖iteratedFDeriv ℝ n h p‖ ≤ M) →
      ∀ (ξ : ℝ) (m : ℤ),
        ‖∫ x : ℝ, ∫ θ in Set.Ico (0 : ℝ) 1,
            Complex.exp (-(2 * Real.pi * Complex.I * ((ξ * x + m * θ : ℝ) : ℂ))) *
              ((‖(1 : ℂ) - Complex.exp ((x / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ : ℝ))‖ ^ 2 *
                  Real.log ‖(1 : ℂ) - Complex.exp ((x / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ : ℝ))‖ : ℝ) : ℂ) *
              h (x, θ)‖ ≤
          K * M * (1 + |ξ|)⁻¹ ^ 2 * ((1 + |(m : ℝ)|) ^ (3 / 2 : ℝ))⁻¹ := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_exists_forall_norm_integral_integral_cexp_mul_normSq_log_germ_mul_le.solution
