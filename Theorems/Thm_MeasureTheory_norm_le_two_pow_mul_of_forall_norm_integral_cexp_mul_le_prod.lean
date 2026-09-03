import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_norm_le_two_pow_mul_of_forall_norm_integral_cexp_mul_le_prod

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.norm_le_two_pow_mul_of_forall_norm_integral_cexp_mul_le_prod
    {r : ℕ} (f : (Fin r → ℝ) → ℂ) (hf : Continuous f) (hfi : Integrable f) (C : ℝ)
    (hC : ∀ ξ : Fin r → ℝ,
      ‖∫ x : Fin r → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ))) * f x‖ ≤ C * ∏ k, (1 + |ξ k|)⁻¹ ^ 2)
    (x : Fin r → ℝ) :
    ‖f x‖ ≤ 2 ^ r * C := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_norm_le_two_pow_mul_of_forall_norm_integral_cexp_mul_le_prod.solution
