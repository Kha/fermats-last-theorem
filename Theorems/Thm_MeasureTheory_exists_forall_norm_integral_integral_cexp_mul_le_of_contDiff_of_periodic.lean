import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_exists_forall_norm_integral_integral_cexp_mul_le_of_contDiff_of_periodic

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_forall_norm_integral_integral_cexp_mul_le_of_contDiff_of_periodic
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (F : ℝ × ℝ → ℂ), ContDiff ℝ 4 F → (∀ p : ℝ × ℝ, R < |p.1| → F p = 0) →
        (∀ p : ℝ × ℝ, F (p.1, p.2 + 1) = F p) →
      ∀ B : ℝ, (∀ n : ℕ, n ≤ 4 → ∀ p : ℝ × ℝ, ‖iteratedFDeriv ℝ n F p‖ ≤ B) →
      ∀ (ξ : ℝ) (m : ℤ),
        ‖∫ x : ℝ, ∫ θ in Set.Ico (0 : ℝ) 1,
            Complex.exp (-(2 * Real.pi * Complex.I * ((ξ * x + m * θ : ℝ) : ℂ))) * F (x, θ)‖ ≤
          C * B * (1 + |ξ|)⁻¹ ^ 2 * (1 + |(m : ℝ)|)⁻¹ ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_exists_forall_norm_integral_integral_cexp_mul_le_of_contDiff_of_periodic.solution
