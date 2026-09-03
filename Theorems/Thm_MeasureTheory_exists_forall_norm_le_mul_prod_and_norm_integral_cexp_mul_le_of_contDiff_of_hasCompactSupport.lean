import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_exists_forall_norm_le_mul_prod_and_norm_integral_cexp_mul_le_of_contDiff_of_hasCompactSupport

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_forall_norm_le_mul_prod_and_norm_integral_cexp_mul_le_of_contDiff_of_hasCompactSupport
    {r : ℕ} (Ψ : (Fin r → ℝ) → ℂ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨc : HasCompactSupport Ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ Continuous Ψ ∧ Integrable Ψ ∧
      (∀ x : Fin r → ℝ, ‖Ψ x‖ ≤ C * ∏ k, (1 + |x k|)⁻¹ ^ 2) ∧
      (∀ ξ : Fin r → ℝ,
        ‖∫ x : Fin r → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ))) * Ψ x‖ ≤
          C * ∏ k, (1 + |ξ k|)⁻¹ ^ 2) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_exists_forall_norm_le_mul_prod_and_norm_integral_cexp_mul_le_of_contDiff_of_hasCompactSupport.solution
