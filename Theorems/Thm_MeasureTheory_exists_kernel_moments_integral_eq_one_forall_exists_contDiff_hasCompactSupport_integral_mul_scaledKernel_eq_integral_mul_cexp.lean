import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_exists_kernel_moments_integral_eq_one_forall_exists_contDiff_hasCompactSupport_integral_mul_scaledKernel_eq_integral_mul_cexp

set_option autoImplicit false

open MeasureTheory
open scoped ComplexConjugate ContDiff

theorem MeasureTheory.exists_kernel_moments_integral_eq_one_forall_exists_contDiff_hasCompactSupport_integral_mul_scaledKernel_eq_integral_mul_cexp :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧ (∀ n : ℕ, Integrable (fun t : ℝ => |t| ^ n * ρ t)) ∧ (∫ t : ℝ, ρ t = 1) ∧
      ∀ (u : ℝ → ℂ), Measurable u → (∃ R : ℝ, ∀ x, R < |x| → u x = 0) → (∃ B : ℝ, ∀ x, ‖u x‖ ≤ B) →
      ∀ δ : ℝ, 0 < δ →
      ∃ h : ℝ → ℂ, ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧
        ∀ t : ℝ, (∫ x : ℝ, u x * ((δ⁻¹ * ρ ((t - x) / δ) : ℝ) : ℂ)) =
          ∫ x : ℝ, h x * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ)) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_exists_kernel_moments_integral_eq_one_forall_exists_contDiff_hasCompactSupport_integral_mul_scaledKernel_eq_integral_mul_cexp.solution
