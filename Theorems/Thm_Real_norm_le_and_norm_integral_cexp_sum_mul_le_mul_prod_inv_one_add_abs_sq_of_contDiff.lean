import Mathlib
import P2M.Util
import P2M.Sol.S_Real_norm_le_and_norm_integral_cexp_sum_mul_le_mul_prod_inv_one_add_abs_sq_of_contDiff

set_option autoImplicit false

open MeasureTheory

theorem Real.norm_le_and_norm_integral_cexp_sum_mul_le_mul_prod_inv_one_add_abs_sq_of_contDiff
    {r : ℕ} (g : (Fin r → ℝ) → ℂ) (R M : ℝ) (hR : 0 ≤ R)
    (hg : ContDiff ℝ ((2 * r : ℕ) : ℕ∞) g)
    (hsupp : ∀ x : Fin r → ℝ, (∃ k, R < |x k|) → g x = 0)
    (hM : ∀ n : ℕ, n ≤ 2 * r → ∀ x : Fin r → ℝ, ‖iteratedFDeriv ℝ n g x‖ ≤ M) :
    (∀ x : Fin r → ℝ, ‖g x‖ ≤ (M * ((1 + R) ^ (2 * r) + (8 * R) ^ r)) * ∏ k, (1 + |x k|)⁻¹ ^ 2) ∧
    (∀ ξ : Fin r → ℝ,
      ‖∫ x : Fin r → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ))) * g x‖ ≤
        (M * ((1 + R) ^ (2 * r) + (8 * R) ^ r)) * ∏ k, (1 + |ξ k|)⁻¹ ^ 2) := by p2m_exact_reverting @_root_.P2MW.S_Real_norm_le_and_norm_integral_cexp_sum_mul_le_mul_prod_inv_one_add_abs_sq_of_contDiff.solution
