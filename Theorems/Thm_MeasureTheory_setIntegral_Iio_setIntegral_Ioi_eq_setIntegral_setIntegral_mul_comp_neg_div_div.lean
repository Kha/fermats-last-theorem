import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_setIntegral_Iio_setIntegral_Ioi_eq_setIntegral_setIntegral_mul_comp_neg_div_div

set_option autoImplicit false

open MeasureTheory Set

theorem MeasureTheory.setIntegral_Iio_setIntegral_Ioi_eq_setIntegral_setIntegral_mul_comp_neg_div_div
    (h : ℝ → ℝ → ℂ) (t : ℝ) (ht : 0 < t) :
    ∫ y₁ in Iio (0 : ℝ), ∫ y₂ in Ioi (0 : ℝ), h y₁ y₂ =
      ∫ u in Ioi (0 : ℝ), ∫ v in Ioi (0 : ℝ), ((u / (t * v ^ 2) : ℝ) : ℂ) * h (-(u / t)) (u / v) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_setIntegral_Iio_setIntegral_Ioi_eq_setIntegral_setIntegral_mul_comp_neg_div_div.solution
