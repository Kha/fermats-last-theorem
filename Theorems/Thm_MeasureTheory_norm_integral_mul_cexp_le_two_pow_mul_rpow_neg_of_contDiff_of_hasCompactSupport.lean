import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_norm_integral_mul_cexp_le_two_pow_mul_rpow_neg_of_contDiff_of_hasCompactSupport

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.norm_integral_mul_cexp_le_two_pow_mul_rpow_neg_of_contDiff_of_hasCompactSupport
    (N : ℕ) (H : ℝ → ℂ) (hH : ContDiff ℝ N H) (hHc : HasCompactSupport H) (l : ℝ) :
    ‖∫ u : ℝ, H u * Complex.exp (Complex.I * (l : ℂ) * (u : ℂ))‖
      ≤ 2 ^ N * ((∫ u : ℝ, ‖H u‖) + ∫ u : ℝ, ‖iteratedDeriv N H u‖) * (1 + |l|) ^ (-(N : ℝ)) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_norm_integral_mul_cexp_le_two_pow_mul_rpow_neg_of_contDiff_of_hasCompactSupport.solution
