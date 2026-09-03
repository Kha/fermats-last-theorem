import Mathlib
import P2M.Util
import P2M.Sol.S_Real_norm_le_and_norm_integral_cexp_mul_le_mul_inv_one_add_abs_sq_of_piecewise_contDiff_two

set_option autoImplicit false

open MeasureTheory

theorem Real.norm_le_and_norm_integral_cexp_mul_le_mul_inv_one_add_abs_sq_of_piecewise_contDiff_two
    (g gm gp : ℝ → ℂ) (R M₀ M₂ J : ℝ) (hR : 0 ≤ R)
    (hgm : ContDiff ℝ 2 gm) (hgp : ContDiff ℝ 2 gp)
    (hm : ∀ x, x ≤ 0 → g x = gm x) (hp : ∀ x, 0 ≤ x → g x = gp x)
    (hsupp : ∀ x, R < |x| → g x = 0)
    (hM₀ : ∀ x, ‖g x‖ ≤ M₀)
    (hM₂m : ∀ x, x ≤ 0 → ‖iteratedDeriv 2 gm x‖ ≤ M₂)
    (hM₂p : ∀ x, 0 ≤ x → ‖iteratedDeriv 2 gp x‖ ≤ M₂)
    (hJ : ‖deriv gp 0 - deriv gm 0‖ ≤ J) :
    (∀ x : ℝ, ‖g x‖ ≤
        (M₀ * (1 + R) ^ 2 + 8 * R * M₀ + (2 * R * M₂ + J) / Real.pi ^ 2) * (1 + |x|)⁻¹ ^ 2) ∧
    (∀ ξ : ℝ, ‖∫ x : ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((ξ * x : ℝ) : ℂ))) * g x‖ ≤
        (M₀ * (1 + R) ^ 2 + 8 * R * M₀ + (2 * R * M₂ + J) / Real.pi ^ 2) * (1 + |ξ|)⁻¹ ^ 2) := by p2m_exact_reverting @_root_.P2MW.S_Real_norm_le_and_norm_integral_cexp_mul_le_mul_inv_one_add_abs_sq_of_piecewise_contDiff_two.solution
